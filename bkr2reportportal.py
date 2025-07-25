#!/usr/bin/env python3
# -- coding: utf-8 --
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#
#   Copyright (c) 2013 Red Hat, Inc.
#
#   This copyrighted material is made available to anyone wishing
#   to use, modify, copy, or redistribute it subject to the terms
#   and conditions of the GNU General Public License version 2.
#
#   This program is distributed in the hope that it will be
#   useful, but WITHOUT ANY WARRANTY; without even the implied
#   warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
#   PURPOSE. See the GNU General Public License for more details.
#
#   You should have received a copy of the GNU General Public
#   License along with this program; if not, write to the Free
#   Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
#   Boston, MA 02110-1301, USA.
#
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#
import sys
import os
import re
import logging
import tempfile
import zipfile
import requests
import argparse
import json
import xml.etree.ElementTree as ETree
import html
from requests.exceptions import HTTPError, ConnectionError, Timeout, RequestException
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import wraps, partial
from time import sleep
from collections import defaultdict

# exit 3: init mapping of resultid and taskid failed
# exit 2: zip file over 32MB
# exit 1: testsuites didn't find in junit.xml
parser = argparse.ArgumentParser()
parser.add_argument('-j', '--job', required=True,
                    help='Beaker job id, format as J:233333 or 233333')
parser.add_argument('-u', '--url', required=True,
                    help='Report Portal instance URL (default: %(default)s)')
parser.add_argument('-p', '--project', required=True,
                    help='Report Portal project name, e.g. mshi_personal')
parser.add_argument('-t', '--token', required=True,
                    help='Report Portal token')
parser.add_argument('-d', '--debug', action='store_true',
                    help='enable debug mode')
parser.add_argument('-w', '--whiteboard', action='store_true',
                    help='Use beaker whiteboard as launch name, it may fail if whiteboard is too long.'
                         ' any invalid character in whiteborad will exchange as - ')
parser.add_argument('-n', '--launchname',
                    help='self define test name, it appear as test name on reportportal lunch plane'
                         'if not setting, the default name will appear as Beaker Job {JOB_ID}')

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

# must have urls
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


# RESULTOUTPUTFILE_URL = re.compile(r'resultoutputfile\.log$')


def retry_download(max_retries=10, delay=10):
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


class CaseProperty:
    def __init__(self, name):
        """
        initial property of failed cases
        """
        self.name = name
        """
        if system-out has url, it can parse a taskid, no matter (main) or other cases
        """
        self.taskid = ''
        """
        if system-out url exist in a non-main case, it can parse a resultid
        """
        self.resultid = ''
        """
        save all of logs from (main) case, no matter suffix .log
        """
        self.task_out_urls = []
        """
        save resultoutfiles.log from non-main case
        """
        self.sub_task_urls = []
        """
        save case property of failure
        """
        self.failure = False
        """
        save failure message 
        """
        self.failure_message = ''
        """
        if a sub test cases failed and has multiple url in systemout, we should search more detail log from taskout.log
        """
        self.new_block = ''
        """
        all of (main) log 
        """
        self.father_log = ''


class JUnitLogProcessor:
    def __init__(self, junit_xml_source, beaker_xml_source, from_string=False, debug=False):
        """
        :param junit_xml_source: XML string if from_string=True; otherwise a file path.
        :param beaker_xml_source: XML string come from beaker job url
        :param from_string: Indicates whether junit_xml_source is file (False) or a string (True)
        :param debug: enable debug log
        """
        self.debug = debug
        """this dict use for show relationship on reportportal"""
        self.host_role_map = defaultdict(str)  # key:hostname, value: role
        """make relationship between taskid and taskurl"""
        self.taskid_task_log_url = defaultdict(list)  # key:task_id, value:taskout_url
        """make relationship between taskid and resultid"""
        self.taskid_resultid = defaultdict(list)  # key:task_id, value:[resultid,..]
        """
        make relationship between url and context, this dick use when parse log.
        """
        self.url_context = defaultdict(str)  # key:logurl value: log
        """
        assume a uniq id as taskid_resultid for search log
        """
        self.testcases = dict()  # key:taskid_resultid value:CaseProperty()
        self.all_kernel_cases = list()
        self.all_kernel_main_cases = list()
        self.all_kernel_sub_cases = list()

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
            self.beaker_root = ETree.fromstring(beaker_xml_source)
            self._parse_beaker_xml(self.beaker_root)
        elif beaker_xml_source and from_string is not True:
            if not os.path.isfile(beaker_xml_source):
                raise FileNotFoundError(f"JUnit file not found: {junit_xml_source}")
            beaker_tree = ETree.parse(beaker_xml_source)
            self.beaker_root = beaker_tree.getroot()
            self._parse_beaker_xml(self.beaker_root)

    def _parse_beaker_xml(self, xml_root):
        """parse Beaker XML build the host-role mapping host_role_map[hostname] = CLIENTS/SERVERS"""
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
        Change the testsuite name to task_id + hostname + role. it will display on detail page on a launch
        """
        for ts in self.root.findall('testsuite'):
            ts_host = ts.get('hostname', '').strip()
            role = self.host_role_map.get(ts_host, 'UNKNOWN_ROLE')
            new_name = f"{role}".strip()
            ts.set('name', new_name)

    def double_escape(self, log_content):
        html_escaped = html.escape(log_content)
        return html_escaped

    def process_all_subcases(self, session: requests.Session):
        """handle all test cases"""
        # build mapping between taskid, resultid and log...etc
        self.flushing_all_tasks()
        self.download_log_urls(session)
        self.set_failedcase_error_text()
        self.got_full_log_from_father_task()
        # attach taskout.log phase to subcases
        self.attach_logs_to_subcases()

    def flushing_all_tasks(self):
        self.all_kernel_cases = [
            testcase for testcase in self.root.findall(".//testcase")
            if testcase.get("classname", "").startswith("/kernel")
            and testcase.find('failure') is not None
        ]
        self.all_kernel_main_cases = [
            testcase for testcase in self.all_kernel_cases
            if testcase.get("name", "").lower() == '(main)'
        ]
        self.all_kernel_sub_cases = [
            testcase for testcase in self.all_kernel_cases
            if testcase.get("name", "").lower() != '(main)'
        ]
        # first search the main
        for testcase in self.all_kernel_main_cases:
            classname = testcase.get("classname", "")
            system_out = testcase.find('system-out')
            if system_out is None or not system_out.text:
                logger.error(f"main case missing system-out on {classname}")
                sys.exit(1)
            # got url of taskout.log
            taskout_url = ""
            # remain_main_log = []
            for url in system_out.text.strip().splitlines():
                if 'taskout.log' in url.lower():
                    taskout_url = url
                # else:
                #    remain_main_log.append(url)
            if not taskout_url:
                logger.error(f"main case missing taskout.log, classname is: {classname}")
                sys.exit(1)
            task_match = TASK_ID_PATTERN.search(taskout_url)
            if not task_match:
                logger.warning("pattern task_id failed")
                continue
            task_id = task_match.group(1)
            self.taskid_task_log_url[task_id].append(taskout_url)
            # if remain_main_log:
            #     self.taskid_task_log_url[task_id].extend(remain_main_log)
        # second search the non-main
        for testcase in self.all_kernel_sub_cases:
            error_element = testcase.find('./error')
            if error_element:
                continue
            system_out = testcase.find('system-out')
            if system_out is None or system_out.text is None or len(system_out.text.strip().splitlines()) == 0:
                continue
            # assume task must have resultoutputfile.log
            outputfile_urls = [
                url.strip() for url in system_out.text.splitlines()
            ]
            if outputfile_urls is None:
                continue
            name = testcase.get('name', '').strip()
            subcase = CaseProperty(name)
            failure_element = testcase.find('./failure')
            subcase.resultid = None
            subcase.taskid = None
            if failure_element is not None:
                subcase.failure = True
                subcase.failure_message = failure_element.get('message', '')
            subcase.sub_task_urls = outputfile_urls
            for url in outputfile_urls:
                result_match = RESULT_ID_PATTERN.search(url)
                if result_match:
                    subcase.resultid = result_match.group(2)
                    subcase.taskid = result_match.group(1)
                    self.taskid_resultid[subcase.taskid].append(subcase.resultid)
                    subcase.task_out_urls = self.taskid_task_log_url.get(subcase.taskid, [])
                    if not subcase.task_out_urls and self.debug:
                        logger.debug(f"{subcase.taskid} has no taskout.log")
                    break
            if subcase.resultid is None or subcase.taskid is None:
                logger.error(f"can't got resultid or taskid from {testcase.get('classname')} {name}")
                sys.exit(3)
            combaine_id = f"{subcase.taskid}_{subcase.resultid}"
            self.testcases[combaine_id] = subcase

    def _get_taskout_by_task_id(self, task_id: str) -> str:
        task_out_urls = self.taskid_task_log_url.get(task_id)[0]
        if not task_out_urls:
            logger.error(f"the taskout.log url of task_id {task_id} not found")
            return ""
        return self.url_context.get(task_out_urls)

    @staticmethod
    def normalize_test_name(test_name):
        return re.sub(r"(?<=\w)[\W\s_]+(?=[\w\n])", "-", test_name)

    def set_failedcase_error_text(self):
        """
        :return: match log from taskout.log
        """
        for subcase in self.testcases.values():
            # assume only deal with failed task
            if subcase.failure:
                subcase.new_block += f"Below message come from junit.xml\n {subcase.failure_message}\n" if (
                    subcase.failure_message) else ""
                for url in subcase.sub_task_urls:
                    subcase.new_block += f"\n=== Come from url: {url} ===\n"
                    subcase.new_block += self.url_context.get(url)

                match_log_title = f"\n=== Matched Log from {subcase.taskid} taskout.log ===\n"
                no_match_log_title = f"\n=== No related log found in {subcase.taskid} taskout.log ===\n"
                normalize_name = self.normalize_test_name(subcase.name)
                # test case name from junit.xml and re-build a new regx
                case_pattern = re.sub(r"(?<=\w)-", "[\\\\W\\\\s_]+", normalize_name)
                pattern = re.compile(r'::\s{2,}' + fr'{case_pattern}')
                whole_task_out = self._get_taskout_by_task_id(subcase.taskid)
                match = pattern.search(whole_task_out)
                if not match:
                    # assume only one or no subcases
                    if len(self.taskid_resultid[subcase.taskid]) < 2:
                        subcase.new_block += match_log_title
                        subcase.new_block += whole_task_out
                    else:
                        subcase.new_block += no_match_log_title
                    continue
                done_match = re.search("Uploading resultoutputfile.log .done", whole_task_out[match.start():])
                if not done_match:
                    subcase.new_block += no_match_log_title
                    continue
                done_match_end = match.start() + done_match.end()
                subcase.new_block += match_log_title
                subcase.new_block += whole_task_out[match.start():done_match_end]

    def got_full_log_from_father_task(self):
        for subcase in self.testcases.values():
            if subcase.failure:
                for url in subcase.task_out_urls:
                    subcase.father_log += f"\n=== Come from url: {url} ===\n"
                    subcase.father_log += self.url_context.get(url)

    @staticmethod
    def search_taskid_and_resultid_from_system_out(system_out):
        for url in system_out.text.strip().splitlines():
            match = RESULT_ID_PATTERN.search(url)
            if match:
                return "_".join([match.group(1), match.group(2)])
        return None

    def attach_logs_to_subcases(self):
        """Deal with the subcases of kernel test cases"""
        for testcase in self.root.findall('.//testcase'):
            # Only handles non-main kernel test cases
            classname = testcase.get('classname', '')
            name = testcase.get("name", "").strip()
            if not classname.startswith("/kernel"):
                continue
            failure_element = testcase.find('failure')
            if name != '(main)':  # for sub kernel case
                system_out = testcase.find('system-out')
                # Deal with system-out, assume no output
                if system_out is None or system_out.text is None or len(system_out.text.strip().splitlines()) == 0:
                    if failure_element and failure_element.get('message'):
                        failure_element.text = f"test ${name} didn't has any system-out elements"
                        failure_element.text += failure_element.get('message')
                else:
                    taskid_resultid = self.search_taskid_and_resultid_from_system_out(system_out)
                    if not taskid_resultid:
                        logger.error(f"didn't found task_id on sub kernel test cases: {classname} {name}")
                        continue
                    subcase = self.testcases.get(taskid_resultid)
                    if not subcase:
                        logger.warning(f"didn't found subcase on sub kernel test cases: {classname} {name}")
                        continue
                    full_block = subcase.father_log
                    # Build log content
                    full_log_content = [system_out.text.strip()]
                    if full_block:
                        full_log_content.append(full_block)
                    system_out.text = '\n'.join(full_log_content)
                    if subcase.new_block and subcase.failure:
                        failure_element.set('message', 'fail')
                        failure_element.text = subcase.new_block
            elif name == '(main)':
                # delete failure element and move log to sub task.
                if failure_element is not None:
                    logger.info("delete failure element")
                    testcase.remove(failure_element)
                # taskout_url = ""
                # system_out = testcase.find('system-out')
                # for url in system_out.text.strip().splitlines():
                #     if 'taskout.log' in url.lower():
                #         taskout_url = url
                #         break
                # if not taskout_url:
                #     logger.error(f"main case missing taskout.log, classname is: {classname}")
                #     sys.exit(1)
                # task_match = TASK_ID_PATTERN.search(taskout_url)
                # if not task_match:
                #     logger.warning("pattern task_id failed")
                #     continue
                # task_id = task_match.group(1)
                # log_content = []
                # if system_out.text:
                #     log_content.append(system_out.text.strip())
                # if task_id:
                #     log_content.append(self._get_taskout_by_task_id(task_id))
                # system_out.text = '\n'.join(log_content)

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
        for item in self.taskid_task_log_url.values():
            tasks.extend(item)
        # all of taskout.log
        # all of resoultoutput.log
        for subcase in self.testcases.values():
            tasks.extend(subcase.sub_task_urls)
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
            future_map = {}
            for url in tasks:
                future = executor.submit(
                    partial(self._download_log_content, url=url, session=session)
                )
                future_map[future] = url

            for future in as_completed(future_map):
                url = future_map[future]
                try:
                    content = self.double_escape(future.result())
                    self.url_context[url] = str(content)
                except Exception as error:
                    logger.error(f"handle url failed {url}: {str(error)}")

    @retry_download(max_retries=30)
    def _download_log_content(self, url: str, session: requests.Session) -> str:
        logger.debug(f"instance self address: {hex(id(self))}")
        """download log"""
        try:
            response = session.get(
                url,
                timeout=(30, 60),
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
        backoff_factor=2.5,
        status_forcelist=[429, 500, 502, 503, 504, 520],
        allowed_methods=frozenset(['GET', 'POST']),
        respect_retry_after_header=True,
        connect=10,
        read=10,
        redirect=5,
        other=5
    )
    adapter = HTTPAdapter(
        max_retries=retries,
        pool_connections=50,
        pool_maxsize=100,
        pool_block=True
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
    if args.whiteboard:
        whiteboard = processor.beaker_root.find('whiteboard').text
        logger.info("got launch name from beaker xml whiteboard：%s", whiteboard)
        lunchname = sanitize_filename(whiteboard).strip()[:100]
    elif args.launchname:
        logger.info("got launch name from self define name：%s", args.launchname)
        lunchname = sanitize_filename(args.launchname).strip()[:100]
    else:
        lunchname = f"Beaker Job {JOB_ID}"
    rp_url = f"{RP_BASE}/api/v1/{RP_PROJECT}/launch/import"
    headers = {
        'Authorization': f'bearer {RP_TOKEN}',
        'accept': '*/*'
    }
    # multipart/form-data data
    # files = {'Field name': (file name, file object, MIME type)}
    with open(zip_source_path, 'rb') as f:
        files = {
            'file': (os.path.basename(zip_source_path), f, 'application/zip'),
            'launchImportRq': (
                None,
                json.dumps({
                    "description": f"Beaker Job {JOB_WEB_URL}",
                    "mode": "DEFAULT",
                    "name": f"{lunchname}"
                }),
                'application/json'
            )
        }
        logger.info("upload ReportPortal：%s", zip_source_path)
        resp = session.post(rp_url, headers=headers, files=files, timeout=(30, 600), verify=False, allow_redirects=True)
    resp.raise_for_status()
    # resp.json method to parse it into Python dict objects.
    data = resp.json()
    launch_uuid = data.get('data').get('id')
    launch_message = data.get('message')
    logger.info("upload successed，Launch UUID：%s", launch_message)
    get_url = f"{RP_BASE}/api/v1/{RP_PROJECT}/launch/{launch_uuid}"
    info = requests.get(get_url, headers=headers).json()
    launch_id = info['id']
    logger.info(f"Launch id is: {launch_id}")


if __name__ == "__main__":
    session_beaker = create_session()
    session_rp = create_session()

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
    file_size_bytes = os.path.getsize(zip_path)
    file_size_mb = file_size_bytes / (1024 * 1024)
    if file_size_mb > 32:
        logger.error(f"Warning: File size {file_size_mb:.2f}MB exceeds 32MB limit")
        sys.exit(2)
    else:
        logger.info(f"file size：{file_size_mb:.2f}MB")

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
