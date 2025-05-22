#!/usr/bin/env python3
import sys
import os
import re
import logging
import tempfile
import zipfile
from re import search

import requests
import argparse
from requests.exceptions import HTTPError, ConnectionError, Timeout, RequestException
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import xml.etree.ElementTree as ETree
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import wraps
from time import sleep
from collections import defaultdict

parser = argparse.ArgumentParser()
parser.add_argument('-j', '--job', required=True,
                    help='Beaker job id, format as J:233333 or 233333')
parser.add_argument('-u', '--url', required=True,
                    help='Report Portal instance URL (default: %(default)s)')
parser.add_argument('-p', '--project', required=True,
                    help='Report Portal project name, e.g. mshi_personal')
parser.add_argument('-t', '--token', required=True,
                    help='Report Portal token')
parser.add_argument('-w', '--whiteboard', action='store_true',
                    help='Use beaker whiteboard as launch name, it may fail if whiteboard is too long')
parser.add_argument('-d', '--debug', action='store_true',
                    help='enable debug mode')
args = parser.parse_args()
if args.debug:
    logging.basicConfig(level=logging.DEBUG,
                        format='%(asctime)s %(levelname)s %(filename)s:%(lineno)d %(funcName)s: %(message)s')
else:
    logging.basicConfig(level=logging.INFO,
                        format='%(asctime)s %(levelname)s %(filename)s:%(lineno)d %(funcName)s: %(message)s')

logger = logging.getLogger(__name__)
JOB_ID = args.job.strip("J:")
RP_BASE = args.url.removesuffix('/')
RP_PROJECT = args.project
RP_TOKEN = args.token
MAX_WORKERS = min(16, (os.cpu_count() or 4) * 4)

# template
BEAKER_BASE = 'https://beaker.engineering.redhat.com'
JUNIT_URL = f"{BEAKER_BASE}/jobs/{JOB_ID}.junit.xml"
BEAKER_XML_URL = f"{BEAKER_BASE}/jobs/{JOB_ID}.xml"
JOB_WEB_URL = f"{BEAKER_BASE}/jobs/{JOB_ID}"

# Use regular expressions to remove characters in the range of U+0000–U+001F (except tab U+0009, LF U+000A, CR U+000D)
INVALID_XML_CHARS_RE = re.compile(
    r'[\x00-\x08\x0B-\x0C\x0E-\x1F]'
)
# parse log type like:
# https://beaker.engineering.redhat.com/recipes/18712741/tasks/195099663/results/907694414/logs/dmesg.log
RESULT_ID_PATTERN = re.compile(
    r'\bhttps?://[^/]+/recipes/\d+/tasks/(\d+)/results/(\d+)/logs\b',
    re.IGNORECASE
)
# parse the task_id
TASK_ID_PATTERN = re.compile(
    r'\bhttps?://[^/]+/recipes/\d+/tasks/(\d+)(?:/|/results/\d+)?/logs/\S+\.log\b',
    re.IGNORECASE
)
TEST_BLOCK_TITLE_PATTERN = re.compile(r'(:{70,}\s*)\n::\s{2,}(.+?)\s*\n\1')

def retry_download(max_retries=5, delay=10):
    def decorator(func):
        @wraps(func)
        def wrapper(*warp_args, **kwargs):
            for attempt in range(1, max_retries + 1):
                try:
                    return func(*warp_args, **kwargs)
                except Exception as error:
                    if attempt == max_retries:
                        logger.error(f"try {max_retries} time, but got {error} failed")
                        raise
                    sleep(delay * attempt)
            return None

        return wrapper

    return decorator


class JUnitLogProcessor:
    def __init__(self, junit_xml_source, beaker_xml_source, from_string=False, debug=False):
        """
        :param junit_xml_source: XML string if from_string=True; otherwise a file path.
        :param from_string: Indicates whether junit_xml_source is file (False) or a string (True)
        """
        self.debug = debug
        self.host_role_map = {}  # key:role, value: hostname
        self.taskid_task_log_url = defaultdict(list)  # key:task_id, value:[taskout_url,..]
        self.taskid_resultid = defaultdict(list)  # key:task_id, value:[resultid,..]
        self.resultid_resultlog = defaultdict(list)  # key:resultid, value:[resultlog,..]
        self.url_context = {}  # key:logurl value: log
        self.taskid_tests_block = dict() # key:task_id, value:dict{test_name:test_block}
        # parse jnuit
        if from_string:
            # from http request
            self.root = ETree.fromstring(junit_xml_source)
        else:
            if not os.path.isfile(junit_xml_source):
                raise FileNotFoundError(f"JUnit file not found: {junit_xml_source}")
            tree = ETree.parse(junit_xml_source)
            self.root = tree.getroot()

        # find the testsuit
        if self.root.tag != 'testsuites':
            logger.error(f"receive the jnuit xml can't recognized")
            sys.exit(1)

        # parse beaker xml
        if beaker_xml_source and from_string:
            beaker_root = ETree.fromstring(beaker_xml_source)
            self._parse_beaker_xml(beaker_root)
        elif beaker_xml_source and from_string is not True:
            if not os.path.isfile(beaker_xml_source):
                raise FileNotFoundError(f"JUnit file not found: {junit_xml_source}")
            beaker_tree = ETree.parse(beaker_xml_source)
            beaker_root = beaker_tree.getroot()
            self._parse_beaker_xml(beaker_root)

    def _parse_beaker_xml(self, xml_root):
        """parse Beaker XML build thr host-role mapping host_role_map[hostname] = CLIENTS/SERVERS"""
        try:
            for task in xml_root.findall('.//task'):
                roles = task.find('roles')
                if roles is None:
                    continue
                for role_elem in roles.findall('role'):
                    role = role_elem.get('value', '').strip()
                    for system in role_elem.findall('system'):
                        host = system.get('value', '').strip()
                        if host:
                            self.host_role_map[host] = role
            if self.debug:
                logger.debug(f"host_role_map {self.host_role_map}")
        except Exception as error:
            logger.error(f"parse Beaker XML failed: {str(error)}")

    def _rename_testsuite(self):
        """
        Change the testsuite name to task_id + hostname + role.
        """
        for ts in self.root.findall('testsuite'):
            ts_id = ts.get('id', '').strip()
            ts_host = ts.get('hostname', '').strip()
            role = self.host_role_map.get(ts_host, 'UNKNOWN_ROLE')
            new_name = f"{ts_id} {ts_host} {role}".strip()
            ts.set('name', new_name)

    def process_all_subcases(self, session: requests.Session):
        """handle all test cases"""
        # build mapping between taskid, resultid and log
        self.flushing_all_task()
        self.download_log_urls(session)
        # attach taskout.log phase to subcases
        self._attach_logs_to_subcases()

    def flushing_all_task(self):
        for testcase in self.root.findall('.//testcase'):
            name = testcase.get('name', '').lower()
            system_out = testcase.find('system-out')
            if '(main)' in name:
                if system_out is None or not system_out.text:
                    logger.error("main case missing system-out")
                    sys.exit(1)
                # got url of taskout.log
                taskout_urls = [
                    url.strip() for url in system_out.text.splitlines()
                    if 'taskout.log' in url.lower()
                ]
                # got task_id
                for url in system_out.text.splitlines():
                    task_match = TASK_ID_PATTERN.search(url)
                    if task_match:
                        task_id = task_match.group(1)
                        if taskout_urls is not None:
                            self.taskid_task_log_url[task_id].extend(taskout_urls)
                            break
                        else:
                            self.taskid_task_log_url[task_id] = []
                    else:
                        logger.warning("pattern task_id failed")
            else:
                if system_out is None or not system_out.text:
                    continue
                result_urls = [
                    url.strip() for url in system_out.text.splitlines()
                    if 'resultoutputfile.log' in url.lower()
                ]

                for url in system_out.text.splitlines():
                    result_match = RESULT_ID_PATTERN.search(url)
                    if result_match:
                        result_id = result_match.group(2)
                        task_id = result_match.group(1)
                        # build result_id -> resultoutput.log
                        if result_id not in self.resultid_resultlog.keys():
                            self.resultid_resultlog[result_id] = []
                        self.resultid_resultlog[result_id].extend(result_urls)

                        # build task_id -> result_id
                        if task_id not in self.taskid_resultid.keys():
                            self.taskid_resultid[task_id] = []
                        if result_id not in self.taskid_resultid.get(task_id):
                            self.taskid_resultid[task_id].append(result_id)

    def _get_task_out_by_task_id(self, task_id: str) -> str:
        urls = self.taskid_task_log_url.get(task_id)
        task_out_url = None
        for url in urls:
            if url.endswith('/taskout.log'):
                task_out_url = url
                break
        if not task_out_url:
            logger.error(f"the taskout.log url of task_id {task_id} not found")
            return ""
        return self.url_context.get(task_out_url)

    @staticmethod
    def normalize_test_name(test_name):
        return re.sub(r"(?<=\w)[\W_]+(?=\w)", "-", test_name)

    def _parse_task_out_log(self, whole_task_out: str):
        done_str = "Uploading resultoutputfile.log .done"
        tasks_out = whole_task_out.split(done_str)
        tests_block = dict()
        for task_out in tasks_out:
            match = TEST_BLOCK_TITLE_PATTERN.search(task_out)
            if not match:
                continue
            test_name = self.normalize_test_name(match.group(2))
            tests_block.update({test_name: task_out[match.start():] + done_str})
        return tests_block

    def parse_task_out_logs(self):
        for task_id in self.taskid_task_log_url.keys():
            task_out = self._get_task_out_by_task_id(task_id)
            if not task_out:
                continue
            tests_block = self._parse_task_out_log(task_out)
            self.taskid_tests_block.update({task_id: tests_block})

    @staticmethod
    def search_task_id_from_system_out(system_out):
        for url in system_out.text.strip().splitlines():
            contain_task_id = TASK_ID_PATTERN.search(url)
            if contain_task_id:
                return contain_task_id.group(1)
        return None

    def _attach_logs_to_subcases(self):
        for testcase in self.root.findall('.//testcase'):
            classname = testcase.get('classname', '')
            name = testcase.get('name', '').strip()
            # Only handles non-main kernel test cases
            if not classname.startswith('/kernel') or name == '(main)':
                continue
            system_out = testcase.find('system-out')
            if len(system_out.text.strip().splitlines()) == 0:
                continue
            task_id = self.search_task_id_from_system_out(system_out)
            if not task_id and self.debug:
                logger.debug(f"didn't found task_id on sub kernel test cases: {classname} {name}")
                continue
            if task_id in self.taskid_tests_block.keys():
                test_block = self.taskid_tests_block.get(task_id).get(name)
            else:
                continue

            # Build log content
            log_content = []
            if system_out.text:
                log_content.append(system_out.text.strip())
            if test_block:
                log_content.append(f"\n=== Matched Log from (task_id={task_id}) ===")
                log_content.append(test_block)
            else:
                if self.debug:
                    logger.debug("_attach_logs_to_subcases:" + test_block)
                log_content.append("\n=== No related log found in taskout.log ===")
            system_out.text = '\n'.join(log_content)

    def _clean_non_kernel(self):
        """
        - Merge and reorder testcases that do not start with /kernel, keeping the original order
        - Group the same classname, add the time, and summarize the system-out;
        - Insert the merge node at the original location;
        - The kernel nodes retain their original order.
        """
        for testsuite in self.root.findall('testsuite'):
            # collect original node
            original = list(testsuite.findall('testcase'))
            # group classname set the default key:value
            grouped = defaultdict(lambda: {'time': 0.0, 'system_out': []})
            # record the value
            class_order = []
            # Scan the group and accumulate all non-kernel nodes
            for testcase in original:
                cls = testcase.get('classname', '')
                if cls.startswith('/kernel'):
                    continue
                grouped[cls]['time'] += float(testcase.get('time', '0') or 0)
                system_out = testcase.find('system-out')
                # assume non kernel task must has one system-out
                if system_out is not None and system_out.text:
                    grouped[cls]['system_out'].extend(system_out.text.strip().split())
                if cls not in class_order:
                    class_order.append(cls)

            # remove all testcase
            for testcase in original:
                testsuite.remove(testcase)

            # re-order tc：
            seen = set()
            for testcase in original:
                cls = testcase.get('classname', '')
                if cls.startswith('/kernel'):
                    # kernel
                    testsuite.append(testcase)
                else:
                    # Non-kernel, only add merge nodes when first encountered
                    if cls in seen:
                        continue
                    seen.add(cls)
                    data = grouped[cls]
                    new_tc = ETree.Element('testcase', {
                        'classname': cls,
                        'name': cls.rsplit('/', 1)[-1],
                        'time': str(data['time'])
                    })
                    so_elem = ETree.SubElement(new_tc, 'system-out')
                    so_elem.text = '\n'.join(data['system_out'])
                    testsuite.append(new_tc)

    def download_log_urls(self, session: requests.Session):
        tasks = []
        # all of taskout.log
        tasks.extend([item for sublist in self.taskid_task_log_url.values() for item in sublist])
        # all of resoultoutput.log
        tasks.extend([item for sublist in self.resultid_resultlog.values() for item in sublist])
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
            future_map = {}
            for url in tasks:
                future = executor.submit(self._download_log_content, url, session)
                future_map[future] = url

            for future in as_completed(future_map):
                url = future_map[future]
                try:
                    content = future.result()
                    self.url_context[url] = str(content)
                except Exception as error:
                    logger.error(f"handle url failed {url}: {str(error)}")

    @retry_download(max_retries=30)
    def _download_log_content(self, url: str, session: requests.Session) -> str:
        """download log"""
        try:
            response = session.get(
                url,
                timeout=(15, 60),
                headers={'Referer': BEAKER_BASE},
            )
            response.raise_for_status()
            if response.encoding is None:
                response.encoding = 'utf-8'
            return clean_xml_text(response.text)
        except (ConnectionResetError, requests.exceptions.ChunkedEncodingError) as error:
            logger.warning(f"connection reset {url}: {str(error)}")
            raise
        except requests.exceptions.RequestException as error:
            logger.error(f"HTTP error {url}: {str(error)}")
            raise
        except Exception as error:
            logger.error(f"download failed {url}: {str(error)}")
        return ""

    def re_org(self):
        self._rename_testsuite()
        self._clean_non_kernel()
        if self.debug:
            ETree.indent(self.root, space='  ')
            print('--- after merge XML ---')
            print(ETree.tostring(self.root, encoding='unicode'))
            print('--- End ---')


def clean_xml_text(text: str) -> str:
    return INVALID_XML_CHARS_RE.sub('', text)


def sanitize_filename(name: str) -> str:
    return re.sub(r'(?u)[^-\w.]', '_', name)


class KeepAliveAdapter(HTTPAdapter):
    def send(self, request, **kwargs):
        # keep-connection
        request.headers['Connection'] = 'keep-alive'
        return super().send(request, **kwargs)


def create_session() -> requests.Session:
    session = requests.Session()
    retries = Retry(
        total=10,
        backoff_factor=1.5,
        status_forcelist=[429, 500, 502, 503, 504, 520],
        allowed_methods=frozenset(['GET', 'POST']),
        respect_retry_after_header=True,
        connect=3,
        read=3,
        redirect=2,
        other=3
    )
    adapter = HTTPAdapter(
        max_retries=retries,
        pool_connections=50,
        pool_maxsize=100
    )
    session.mount('http://', adapter)
    session.mount('https://', adapter)
    session.headers.update({
        'User-Agent': 'Mozilla/5.0 (X11; Linux x86_64) bkr2rp/1.0',
        'Accept-Encoding': 'gzip, deflate',
        'Connection': 'keep-alive'
    })
    return session


def download_text(download_url: str, session: requests.Session) -> str:
    logger.debug("download url：%s", download_url)
    try:
        r = session.get(download_url, timeout=(100, 300))
        r.raise_for_status()
        # clear control character
        text = clean_xml_text(r.text)
        return text
    except HTTPError as http_err:
        logger.error(f"HTTP error occurred: {http_err}")
        return ''
    except ConnectionError as conn_err:
        logger.error(f"Connection error occurred: {conn_err}")
        return ''
    except Timeout as timeout_err:
        logger.error(f"Timeout error occurred: {timeout_err}")
        return ''
    except RequestException as req_err:
        logger.error(f"An error occurred: {req_err}")
        return ''
    except Exception as error:
        logger.error(f"An unexpected error occurred: {error}")
        return ''


def upload_to_rp(zip_source_path: str, session: requests.Session):
    rp_url = f"{RP_BASE}/api/v1/{RP_PROJECT}/launch/import"
    headers = {
        'Authorization': f'bearer {RP_TOKEN}',
        'accept': '*/*'
    }
    with open(zip_source_path, 'rb') as f:
        files = {'file': f, }
        logger.info("upload ReportPortal：%s", zip_source_path)
        resp = session.post(rp_url, headers=headers, files=files, timeout=60)
    resp.raise_for_status()
    # r.json method to parse it into Python dict objects.
    data = resp.json()
    launch_uuid = data.get('data').get('id')
    launch_message = data.get('message')
    logger.info("upload successed，Launch UUID：%s", launch_message)
    get_url = f"{RP_BASE}/api/v1/{RP_PROJECT}/launch/{launch_uuid}"
    info = requests.get(get_url, headers=headers).json()
    launch_id = info['id']
    desc = JOB_WEB_URL
    if args.whiteboard:
        # get whiteboard
        wb = session_beaker.get(BEAKER_XML_URL).content
        wb_text = ETree.fromstring(wb).findtext('whiteboard', '').strip()
        desc += '\n' + wb_text
    upd_url = f"{RP_BASE}/api/v1/{RP_PROJECT}/launch/{launch_id}/update"
    requests.put(upd_url, headers=headers, json={'description': desc})
    logger.info("completely update description of Launch")


if __name__ == "__main__":
    session_beaker = create_session()
    session_rp = create_session()

    if args.whiteboard:
        try:
            wb_xml = download_text(BEAKER_XML_URL, session_beaker)
            wb = ETree.fromstring(wb_xml).findtext('whiteboard', '')
        except Exception as e:
            logger.error(f"add whiteboard failed: {e}")
            wb = f'{JOB_ID}'
    else:
        wb = f'{JOB_ID}'

    try:
        junit_xml = download_text(JUNIT_URL, session_beaker)
        beaker_xml = download_text(BEAKER_XML_URL, session_beaker)
    except Exception as e:
        logger.error(f"download JUnit XML failed: {e}")
        sys.exit(1)
    processor = JUnitLogProcessor(
        junit_xml,
        beaker_xml_source=beaker_xml,
        from_string=True,
        debug=args.debug
    )

    # Download all log files concurrently and insert into XML
    download_session = create_session()
    processor.re_org()
    processor.process_all_subcases(download_session)
    # generated ZIP
    with tempfile.NamedTemporaryFile(delete=False, suffix=".zip") as tmpzip:
        zip_path = tmpzip.name
    with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED) as z:
        arcname = sanitize_filename(f"bkr-junit-{JOB_ID}.xml")
        z.writestr(arcname, ETree.tostring(processor.root, encoding='utf-8'))
    logger.info("create ZIP：%s", zip_path)

    # upload
    try:
        upload_to_rp(zip_path, session_rp)
    except Exception as e:
        logger.exception(f"Failed to upload or update description: {e}")
        sys.exit(1)

    # cleanup
    try:
        os.remove(zip_path)
    except OSError:
        pass

    logger.info("All completed, please check Report Portal")
