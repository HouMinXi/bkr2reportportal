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
# need install additional packages from 'pip install requests tqdm urllib3'
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
import gc
import resource
import tracemalloc
import time
import signal
from datetime import datetime, timezone
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from urllib.parse import urlparse
from concurrent.futures import ThreadPoolExecutor, as_completed, TimeoutError as FutureTimeoutError
from functools import wraps
from time import sleep
from collections import defaultdict
from tqdm import tqdm

# exit codes
# exit 9: memory error
# exit 8: error processing subcases
# exit 7: global timeout
# exit 6: total log size exceeds 500MB
# exit 5: single log file exceeds 50MB
# exit 4: got the size of log url failed
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
parser.add_argument('-a', '--attributes', action='append',
                    help='Add custom attributes to the launch. Format: key=value. Can be used multiple times. '
                         'If duplicate keys are provided, the last value will be used.'
                         'Example: --attributes "nic_driver=mlx5_core" -a "owner=tli"')

cli_args = parser.parse_args()
if cli_args.debug:
    logging.basicConfig(level=logging.DEBUG,
                        format='%(asctime)s %(levelname)s %(filename)s:%(lineno)d %(funcName)s: %(message)s')
    # Start memory tracing
    tracemalloc.start()
else:
    logging.basicConfig(level=logging.INFO,
                        format='%(asctime)s %(levelname)s %(filename)s:%(lineno)d %(funcName)s: %(message)s')

logger = logging.getLogger(__name__)
JOB_ID = cli_args.job.strip("J:")
RP_BASE = cli_args.url.removesuffix('/')
RP_PROJECT = cli_args.project
RP_TOKEN = cli_args.token

# must have urls
BEAKER_BASE = 'https://beaker.engineering.redhat.com'
JUNIT_URL = f"{BEAKER_BASE}/jobs/{JOB_ID}.junit.xml"
BEAKER_XML_URL = f"{BEAKER_BASE}/jobs/{JOB_ID}.xml"
JOB_WEB_URL = f"{BEAKER_BASE}/jobs/{JOB_ID}"

# Size limits
SINGLE_FILE_LIMIT = 50 * 1024 * 1024  # 50MB
TOTAL_SIZE_LIMIT = 300 * 1024 * 1024  # 300MB
ZIP_SIZE_LIMIT = 32 * 1024 * 1024  # 32MB
MEMORY_LIMIT = 1536 * 1024 * 1024  # 1536MB

# Timeout settings
TASKOUT_TIMEOUT = 1800  # 5 minutes for large taskout.log files
LARGE_FILE_TIMEOUT = 300  # 3 minutes for files > 10MB
MEDIUM_FILE_TIMEOUT = 120  # 2 minutes for files 1-10MB
SMALL_FILE_TIMEOUT = 60  # 1 minute for small files
SIZE_CHECK_TIMEOUT = 15  # 15 seconds for size check
GLOBAL_TIMEOUT = 3600  # 30 minutes global timeout

# Handling constant error strings
FAILURE_STRINGS = [
    r"Oops",
    r"BUG",
    r"Kernel panic",
    r"Call Trace",
    r"Call trace",
    r"cut here",
    r"Unit Hang",
    r"watchdog: BUG: soft lockup - CPU",
    r"saving vmcore",
    r"saving vmcore-dmesg.txt complete",
    r"Starting Kdump Vmcore Save Service",
]

# Use regular expressions to remove characters in the range of U+0000–U+001F (except tab U+0009, LF U+000A, CR U+000D)
INVALID_XML_CHARS_RE = re.compile(
    r'[\x00-\x08\x0B-\x0C\x0E-\x1F]'
)
# parse log type like:
# https://beaker.engineering.redhat.com/recipes/18712741/tasks/195099663/results/907694414/logs/dmesg.log
RESULT_ID_PATTERN = re.compile(
    r'\bhttps?://[^/]+/recipes/\d+/tasks/(\d+)/results/(\d+)/logs/\S*',
    re.IGNORECASE
)
# parse the task_id
TASK_ID_PATTERN = re.compile(
    r'\bhttps?://[^/]+/recipes/\d+/tasks/(\d+)(?:/|/results/\d+)?/logs/\S+\.log\b',
    re.IGNORECASE
)

# Set memory limits
try:
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))
    logger.info(f"Set global memory limit to {MEMORY_LIMIT / 1024 / 1024} MB")
except (ValueError, resource.error) as e:
    logger.warning(f"Unable to set memory limit: {e}")

# Disable bytecode caching(useful in docker env with non-root user)
sys.dont_write_bytecode = True


class CustomTimeoutError(Exception):
    pass


def timeout_handler(_signum, _frame):
    raise CustomTimeoutError("Operation timed out")


def log_memory_usage(prefix=""):
    """Record memory usage"""
    if cli_args.debug:
        current, peak = tracemalloc.get_traced_memory()
        logger.info(
            f"{prefix} Memory usage: Current = {current / 1024 / 1024:.2f} MB, Peak = {peak / 1024 / 1024:.2f} MB")


def get_download_timeout(url, file_size):
    """Returns an appropriate timeout based on the URL and file size"""
    # Uses a longer timeout for the taskout.log file
    if 'taskout.log' in url:
        return TASKOUT_TIMEOUT
    # Select the timeout period based on the file size.
    if file_size > 10 * 1024 * 1024:  # > 10MB
        return LARGE_FILE_TIMEOUT
    elif file_size > 1 * 1024 * 1024:  # > 1MB
        return MEDIUM_FILE_TIMEOUT
    else:
        return SMALL_FILE_TIMEOUT

def retry_download(max_retries=5, delay=2, backoff=2):
    """Retry decorator with exponential backoff for downloads"""
    def decorator(func):
        @wraps(func)
        def wrapper(*func_args, **func_kwargs):
            last_exception = None
            for attempt in range(1, max_retries + 1):
                try:
                    return func(*func_args, **func_kwargs)
                except Exception as error:
                    last_exception = error
                    logger.warning(
                        f"Attempt {attempt}/{max_retries} failed for {func_args[1] if len(func_args) > 1 else 'unknown'}: {error}")
                    if attempt == max_retries:
                        logger.error(f"All {max_retries} attempts failed")
                        break
                    sleep_time = delay * (backoff ** (attempt - 1))
                    logger.info(f"Retrying in {sleep_time}s...")
                    sleep(sleep_time)
            raise last_exception
        return wrapper
    return decorator


class CaseProperty:
    def __init__(self, name):
        """
        initial property of failed cases
        """
        self.name = name
        """
        Add classname attribute
        """
        self.classname = ''
        """
        if system-out has url, it can parse a taskid, no matter (main) or other cases
        """
        self.taskid = ''
        """
        if system-out url exist in a non-main case, it can parse a resultid
        """
        self.resultid = ''
        """
        save all of log urls from (main) case, no matter suffix .log
        """
        self.task_out_urls = []
        """
        save resultoutfiles.log url from non-main case
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
        Used to store debug-level taskout.log matching content
        """
        self.debug_block = ''


class JUnitLogProcessor:
    def __init__(self, junit_xml_source, beaker_xml_source, from_string=False, debug=False):
        """
        :param junit_xml_source: XML string if from_string=True; otherwise a file path.
        :param beaker_xml_source: XML string come from beaker job url
        :param from_string: Indicates whether junit_xml_source is file (False) or a string (True)
        :param debug: enable debug log
        """
        # Save the session reference (to be set later in process_all_subcases).
        self.session = None
        self.debug = debug
        self.total_downloaded_size = 0  # Track total downloaded size
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
        self._EXCLUDED_LOG_CASES = {
            '10_avc_check',
            '99_reboot',
            '10_localwatchdog',
            'exit_code'
        }
        # add time property
        self.launch_start_time = None
        self.launch_end_time = None

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
            self._parse_beaker_timing()
        elif beaker_xml_source and from_string is not True:
            if not os.path.isfile(beaker_xml_source):
                raise FileNotFoundError(f"JUnit file not found: {junit_xml_source}")
            beaker_tree = ETree.parse(beaker_xml_source)
            self.beaker_root = beaker_tree.getroot()
            self._parse_beaker_xml(self.beaker_root)
            self._parse_beaker_timing()

        log_memory_usage("After initialization")

    def _parse_beaker_timing(self):
        """
        Extract the earliest start time from the Beaker XML.
        Throw an exception if the earliest start time cannot be retrieved.
        :return: timestamp(str type)
        """
        try:
            # Get time directly from the recipe level
            for recipe in self.beaker_root.findall('.//recipe'):
                start_time_str = recipe.get('start_time')
                if start_time_str:
                    try:
                        # Parsing time format: "2025-11-14 02:28:13"
                        recipe_time = datetime.strptime(start_time_str, '%Y-%m-%d %H:%M:%S')
                        recipe_time = recipe_time.replace(tzinfo=timezone.utc)
                        if self.launch_start_time is None or recipe_time < self.launch_start_time:
                            self.launch_start_time = recipe_time
                            logger.info(f"Found recipe start time: {recipe_time} from recipe {recipe.get('id')}")
                    except ValueError as time_data_error:
                        logger.error(f"Failed to parse recipe start_time '{start_time_str}': {time_data_error}")
                        raise ValueError(f"Invalid start_time format in Beaker XML: {start_time_str}")
            if self.launch_start_time is None:
                raise ValueError("No valid start_time found in Beaker XML recipes")

            for recipe in self.beaker_root.findall('.//recipe'):
                finish_time_str = recipe.get('finish_time')
                if finish_time_str:
                    try:
                        recipe_time = datetime.strptime(finish_time_str, '%Y-%m-%d %H:%M:%S')
                        recipe_time = recipe_time.replace(tzinfo=timezone.utc)

                        if self.launch_end_time is None or recipe_time > self.launch_end_time:
                            self.launch_end_time = recipe_time
                    except ValueError as time_data_error:
                        logger.warning(f"Failed to parse recipe finish_time '{finish_time_str}': {time_data_error}")

            if self.launch_end_time:
                duration = self.launch_end_time - self.launch_start_time
                logger.info(
                    f"Beaker job actual timing: {self.launch_start_time} to {self.launch_end_time} (duration: {duration})")

        except Exception as extract_error:
            logger.error(f"Error extracting time from Beaker XML: {extract_error}")
            raise

    def get_launch_start_time_iso(self):
        """Get the launch start time in ISO format."""
        if self.launch_start_time is None:
            raise ValueError("Launch start time not available")

        iso_time = self.launch_start_time.isoformat(timespec='milliseconds').replace('+00:00', 'Z')
        logger.info(f"Launch start time (ISO): {iso_time}")
        return iso_time

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

    @staticmethod
    def double_escape(log_content):
        html_escaped = html.escape(log_content)
        return html_escaped

    def process_all_subcases(self, session: requests.Session):
        """
        Process all test cases with optimized memory usage
        """
        self.session = session
        # Set global timeout
        signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(GLOBAL_TIMEOUT)
        try:
            try:
                log_memory_usage("Before starting to process sub-use cases")
                # Build mapping between taskid, resultid and log
                self.flushing_all_tasks()
                gc.collect()
                log_memory_usage("After flushing_all_tasks")
            except Exception as flushing_all_tasks_error:
                logger.error(f"flushing_all_tasks failed: {str(flushing_all_tasks_error)}")

            try:
                # Download logs with robust retry mechanism
                self.download_logs_concurrently(session)
                gc.collect()
                log_memory_usage("After downloading logs")
            except Exception as download_logs_concurrently_error:
                logger.error(f"download_logs_concurrently failed: {str(download_logs_concurrently_error)}")

            try:
                self.set_failedcase_error_text()
                gc.collect()
                log_memory_usage("After setting the error text")
            except Exception as set_failedcase_error_text_error:
                logger.error(f"set_failedcase_error_text failed: {str(set_failedcase_error_text_error)}")

            try:
                self.attach_logs_to_subcases()
                gc.collect()
                log_memory_usage("After attaching logs to subcases")
            except Exception as attach_logs_to_subcases_error:
                logger.error(f"attach_logs_to_subcases failed: {str(attach_logs_to_subcases_error)}")
        except Exception as error:
            logger.error(f"process_all_subcases failed: {str(error)}")
        finally:
            # Cancel timeout
            signal.alarm(0)

    def _get_console_log_url(self, recipe_id):
        """Get the URL of console.log based on recipe_id"""
        try:
            # Find the corresponding console.log file for the recipe in the Beaker XML.
            console_elem = self.beaker_root.find(f'.//recipe[@id="{recipe_id}"]//log[@name="console.log"]')
            if console_elem is not None:
                return console_elem.get('href')
        except Exception as got_console_error:
            logger.warning(f"Failed to get console.log URL for recipe {recipe_id}: {got_console_error}")
        return None

    def download_logs_concurrently(self, session: requests.Session):
        """Download logs with robust retry mechanism and size tracking"""
        all_urls = set()

        # Add taskout log URL
        for urls in self.taskid_task_log_url.values():
            all_urls.update(urls)

        # Add subtask URL
        for subcase in self.testcases.values():
            all_urls.update(subcase.sub_task_urls)

        # Add a corresponding console.log for all panic tasks
        logger.info("Checking for panic tasks to add console.log...")
        panic_recipes = set()
        for task_elem in self.beaker_root.findall('.//task'):
            if task_elem.get('result') == 'Panic':
                task_id = task_elem.get('id')
                # Find the recipe that contains this task.
                for recipe_elem in self.beaker_root.findall('.//recipe'):
                    if recipe_elem.find(f'.//task[@id="{task_id}"]') is not None:
                        recipe_id = recipe_elem.get('id')
                        panic_recipes.add(recipe_id)
                        logger.info(f"Found panic task {task_id} in recipe {recipe_id}")
                        break

        # Add console.log to each panic recipe
        for recipe_id in panic_recipes:
            recipe_elem = self.beaker_root.find(f'.//recipe[@id="{recipe_id}"]')
            if recipe_elem is not None:
                console_elem = recipe_elem.find('.//log[@name="console.log"]')
                if console_elem is not None:
                    console_url = console_elem.get('href')
                    if console_url and console_url not in all_urls:
                        all_urls.add(console_url)
                        logger.info(f"Added console.log for panic recipe {recipe_id}: {console_url}")

        logger.info(f"{len(all_urls)} log files need to be downloaded.")

        # Check file sizes first with timeout
        logger.info("Checking file sizes...")
        url_sizes = {}
        total_estimated_size = 0

        for url in all_urls:
            size = self._get_content_length_with_timeout(url, session)
            url_sizes[url] = size

            if size > SINGLE_FILE_LIMIT:
                logger.error(
                    f"Log file {url} size {size / 1024 / 1024:.2f} MB exceeds {SINGLE_FILE_LIMIT / 1024 / 1024}MB limit")
                sys.exit(5)

            total_estimated_size += size
            if total_estimated_size > TOTAL_SIZE_LIMIT:
                logger.error(
                    f"Total estimated size {total_estimated_size / 1024 / 1024:.2f} MB exceeds {TOTAL_SIZE_LIMIT / 1024 / 1024}MB limit")
                sys.exit(6)

        logger.info(f"Total estimated size: {total_estimated_size / 1024 / 1024:.2f} MB")

        # Download files with adaptive concurrency
        self._download_with_adaptive_concurrency(all_urls, session, url_sizes)

    @staticmethod
    def _get_content_length_with_timeout(url: str, session: requests.Session) -> int:
        """Get content length with timeout and retry"""
        for attempt in range(3):
            try:
                signal.signal(signal.SIGALRM, timeout_handler)
                signal.alarm(SIZE_CHECK_TIMEOUT)
                try:
                    response = session.head(url, timeout=10, allow_redirects=True)
                    if response.status_code == 200:
                        content_length = response.headers.get('content-length')
                        if content_length:
                            signal.alarm(0)
                            return int(content_length)

                    # If HEAD fails, try GET but only read the header
                    response = session.get(url, stream=True, timeout=10, allow_redirects=True)
                    response.close()
                    content_length = response.headers.get('content-length')
                    signal.alarm(0)
                    if content_length:
                        return int(content_length)
                    return 0
                except CustomTimeoutError:
                    logger.warning(f"Size check timeout for {url}, attempt {attempt + 1}")
                    continue
            except Exception as signal_errors:
                logger.warning(f"Size check failed for {url}, attempt {attempt + 1}: {signal_errors}")
            finally:
                signal.alarm(0)

        logger.warning(f"Could not determine size for {url}, assuming 0")
        return 0

    def _download_with_adaptive_concurrency(self, all_urls, session, url_sizes):
        """Download files with adaptive concurrency based on file sizes"""
        urls_to_download = list(all_urls)
        completed_count = 0
        start_time = time.time()

        # Separate taskout.log from other files
        taskout_urls = [url for url in urls_to_download if 'taskout.log' in url]
        logger.info(f"Found {len(taskout_urls)} log files\n")
        other_urls = [url for url in urls_to_download if 'taskout.log' not in url]
        logger.info(f"Found {len(other_urls)} other files\n")

        if other_urls:
            logger.info("Downloading non-taskout files first...\n")
            self._download_file_group(other_urls, session, url_sizes, "non-taskout", completed_count, len(all_urls),
                                      start_time)

        if taskout_urls:
            logger.info("Downloading taskout.log files (this may take longer)...\n")
            self._download_file_group(taskout_urls, session, url_sizes, "taskout", completed_count, len(all_urls),
                                      start_time)

    def _download_file_group(self, urls, session, url_sizes, group_name, completed_count, total_files, start_time):
        """Download a group of files with appropriate settings"""
        batch_size = 3 if group_name == "taskout" else 8  # The taskout file uses smaller batches.

        for i in range(0, len(urls), batch_size):
            batch_urls = urls[i:i + batch_size]
            logger.info(f"Processing {group_name} batch {i // batch_size + 1}/{(len(urls) - 1) // batch_size + 1}")

            batch_results = self._download_batch(batch_urls, session, url_sizes, group_name)

            # Process results
            for url, success, content in batch_results:
                completed_count += 1
                if success and content is not None:
                    processed_content = self.double_escape(content)
                    self.url_context[url] = processed_content

                    elapsed = time.time() - start_time
                    rate = completed_count / elapsed if elapsed > 0 else 0
                    logger.info(f"Progress: {completed_count}/{total_files} "
                                f"({completed_count / total_files * 100:.1f}%) "
                                f"- {rate:.2f} files/sec - {os.path.basename(url)}")
                else:
                    logger.error(f"Failed to download {url}")

            # Check memory usage
            log_memory_usage(f"After {group_name} batch {i // batch_size + 1}")

            # Pauses between batches, especially for large files.
            sleep_time = 2 if group_name == "taskout" else 0.5
            time.sleep(sleep_time)

    def _download_batch(self, batch_urls, session, url_sizes, group_name):
        """Download a batch of URLs with timeout control"""
        results = []
        batch_total_size = sum(url_sizes.get(url, 0) for url in batch_urls)
        # Adjust the maximum number of worker threads based on file groups
        max_workers = min(len(batch_urls), 3 if group_name == "taskout" else 8)
        with tqdm(total=batch_total_size, unit='B', unit_scale=True,
              desc=f"Downloading {group_name} batch", leave=False) as pbar:
            with ThreadPoolExecutor(max_workers=max_workers) as executor:
                future_to_url = {}
                for url in batch_urls:
                    file_size = url_sizes.get(url, 0)
                    timeout = get_download_timeout(url, file_size)
                    future = executor.submit(self._download_single_file, url, session, file_size, timeout, pbar)
                    future_to_url[future] = (url, timeout)

                for future in as_completed(future_to_url):
                    url, timeout = future_to_url[future]
                    try:
                        # Set different future timeouts based on file type
                        future_timeout = timeout + 60  # Additional 60 seconds of processing time
                        result = future.result(timeout=future_timeout)
                        results.append((url, True, result))
                    except FutureTimeoutError:
                        logger.error(f"Download timeout for {url} (timeout: {timeout}s)")
                        results.append((url, False, None))
                    except Exception as unexpect_errors:
                        logger.error(f"Download failed for {url}: {unexpect_errors}")
                        results.append((url, False, None))

        return results

    @retry_download(max_retries=5, delay=2, backoff=2)
    def _download_single_file(self, url: str, session: requests.Session, expected_size: int, timeout: int,
                              pbar=None) -> str:
        """Download a single file with size tracking and timeout"""
        start_time = time.time()

        # Check console.log
        is_console_log = 'console.log' in url
        if not is_console_log and url in self.url_context:
            return self.url_context[url]
        if is_console_log and url in self.url_context:
            return self.url_context[url]
        # Check if we've already exceeded total size limit
        if self.total_downloaded_size > TOTAL_SIZE_LIMIT:
            logger.error(f"Total downloaded size {self.total_downloaded_size / 1024 / 1024:.2f}MB exceeds limit")
            sys.exit(6)

        try:
            logger.info(
                f"Downloading {url} with timeout {timeout}s, expected size: {expected_size / 1024 / 1024:.2f}MB")
            response = session.get(
                url,
                timeout=(10, timeout),
                headers={'Referer': BEAKER_BASE},
                stream=True
            )
            response.raise_for_status()

            content_parts = []
            downloaded_size = 0
            chunk_size = 64 * 1024  # 64KB chunks

            # Check if it is a redirected URL
            final_url = response.url
            if final_url != url:
                logger.debug(f"Redirected from {url} to {final_url}")

            for chunk in response.iter_content(chunk_size=chunk_size, decode_unicode=False):
                if time.time() - start_time > timeout:
                    raise CustomTimeoutError(f"Download exceeded {timeout}s timeout")

                if chunk:
                    chunk_size_actual = len(chunk)
                    content_parts.append(chunk)
                    downloaded_size += chunk_size_actual
                    if pbar:
                        pbar.update(chunk_size_actual)
                    # Check single file size limit
                    if downloaded_size > SINGLE_FILE_LIMIT:
                        logger.error(f"File {url} exceeds {SINGLE_FILE_LIMIT / 1024 / 1024}MB limit")
                        sys.exit(5)

                    # Check total size limit
                    self.total_downloaded_size += chunk_size_actual
                    if self.total_downloaded_size > TOTAL_SIZE_LIMIT:
                        logger.error(
                            f"Total downloaded size {self.total_downloaded_size / 1024 / 1024:.2f}MB exceeds {TOTAL_SIZE_LIMIT / 1024 / 1024}MB limit")
                        sys.exit(6)

            full_content = b''.join(content_parts)

            if 0 < expected_size != downloaded_size:
                logger.warning(
                    f"Downloaded size {downloaded_size} doesn't match expected size {expected_size} for {url}")

            try:
                decoded_content = full_content.decode('utf-8')
            except UnicodeDecodeError:
                decoded_content = full_content.decode('utf-8', errors='replace')

            elapsed = time.time() - start_time
            logger.info(f"Downloaded {url} in {elapsed:.2f}s, Size: {downloaded_size / 1024 / 1024:.2f}MB")
            if is_console_log:
                return clean_xml_text(decoded_content)
            else:
                # Other files are cached in url_context
                processed_content = clean_xml_text(decoded_content)
                self.url_context[url] = processed_content
                return processed_content

        except Exception as error:
            elapsed = time.time() - start_time
            logger.warning(f"Download failed for {url} after {elapsed:.2f}s: {str(error)}")
            raise

    def _is_panic_case(self, testcase):
        """Check if the test case corresponds to the Panic state in Beaker."""
        try:
            # Extract task ID from system-out
            system_out = testcase.find('system-out')
            logger.info(f"_is_panic_case: {system_out}, {testcase.get()}")
            if system_out is None or not system_out.text:
                return False

            # find the task url
            for url in system_out.text.strip().splitlines():
                task_match = TASK_ID_PATTERN.search(url)
                if task_match:
                    task_id = task_match.group(1)
                    # Find the results for this task in the Beaker XML.
                    task_elem = self.beaker_root.find(f'.//task[@id="{task_id}"]')
                    if task_elem is not None and task_elem.get('result') == 'Panic':
                        return True
        except Exception as handle_task_error:
            logger.debug(f"Error checking panic status: {handle_task_error}")

        return False

    def flushing_all_tasks(self):
        self.all_kernel_cases = [
            testcase for testcase in self.root.findall(".//testcase")
            if testcase.get("classname", "").startswith("/kernel")
                and (testcase.find('failure') is not None
                or self._is_panic_case(testcase))
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
            for url in system_out.text.strip().splitlines():
                if 'taskout.log' in url.lower():
                    taskout_url = url

            if not taskout_url:
                logger.error(f"main case missing taskout.log, classname is: {classname}")
                sys.exit(1)

            task_match = TASK_ID_PATTERN.search(taskout_url)
            if not task_match:
                logger.warning("pattern task_id failed")
                continue
            task_id = task_match.group(1)
            self.taskid_task_log_url[task_id].append(taskout_url)
            logger.debug(f"Added taskout.log for task_id {task_id}: {taskout_url}")

        # second search the non-main
        for testcase in self.all_kernel_sub_cases:
            classname = testcase.get("classname", "")
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
                    logger.debug(f"Matched URL: {url}, taskid: {subcase.taskid}, resultid: {subcase.resultid}")
                    self.taskid_resultid[subcase.taskid].append(subcase.resultid)
                    subcase.task_out_urls = self.taskid_task_log_url.get(subcase.taskid, [])
                    if not subcase.task_out_urls and self.debug:
                        logger.debug(f"{subcase.taskid} has no taskout.log")
                    break
                else:
                    task_match = TASK_ID_PATTERN.search(url)
                    if task_match:
                        subcase.taskid = task_match.group(1)
                        logger.debug(f"Extracted taskid from URL: {subcase.taskid}")
                        subcase.task_out_urls = self.taskid_task_log_url.get(subcase.taskid, [])
                        if not subcase.task_out_urls:
                            logger.warning(f"taskid {subcase.taskid} has no taskout.log URLs")

            if subcase.resultid is None or subcase.taskid is None:
                logger.warning(f"can't got resultid or taskid from {testcase.get('classname')} {name}")
                continue

            combaine_id = f"{subcase.taskid}_{subcase.resultid}"
            self.testcases[combaine_id] = subcase
            logger.debug(f"Added subcase: {combaine_id} for {classname} {name}")

    def _get_taskout_by_task_id(self, task_id: str) -> str:
        task_out_urls = self.taskid_task_log_url.get(task_id)
        if not task_out_urls:
            logger.error(f"the taskout.log url of task_id {task_id} not found")
            return ""
        return self.url_context.get(task_out_urls[0], "")

    @staticmethod
    def normalize_test_name(test_name):
        return re.sub(r"(?<=\w)[\W\s_]+(?=[\w\n])", "-", test_name)

    def set_failedcase_error_text(self):
        """
        :return: match log from taskout.log
        """
        # if job occurred panic
        has_panic = False
        for recipe in self.beaker_root.findall('.//recipe'):
            if recipe.get('result') == 'Panic':
                has_panic = True
                break

        # Panic should only be addressed if a panic actually occurs.
        if has_panic:
            self._process_panic_cases()
        else:
            logger.debug("No panic detected in this job, skipping panic processing")

        for subcase in self.testcases.values():
            # Skip use cases that have already been processed by panic
            if subcase.failure and "System Panic Detected" in subcase.failure_message:
                continue

            if subcase.failure:
                subcase.new_block = ""
                if subcase.failure_message:
                    subcase.new_block += f"Below message come from junit.xml\n{subcase.failure_message}\n"
                if subcase.name == '10_avc_check':
                    for url in subcase.sub_task_urls:
                        subcase.new_block += f"\n=== Come from url: {url} ===\n"
                        subcase.new_block += self.url_context.get(url)
                elif subcase.name in ['99_reboot', '10_localwatchdog']:
                    subcase.failure_message = subcase.name
                    subcase.new_block += f"Test case {subcase.name} failed\n"
                elif subcase.name == 'exit_code':
                    subcase.new_block += f"{subcase.failure_message}"
                else:
                    # assume a normal failed
                    resultoutput_added = False
                    for url in subcase.sub_task_urls:
                        if os.path.basename(urlparse(url).path) == "resultoutputfile.log":
                            content = self.url_context.get(url, "")
                            if content and not resultoutput_added:
                                subcase.new_block += f"\n=== Come from url: {url} ===\n"
                                subcase.new_block += content
                                resultoutput_added = True

                    match_log_title = f"\n=== Matched Log from {subcase.taskid} taskout.log ===\n"
                    # no_match_log_title = f"\n=== No related log found in {subcase.taskid} taskout.log ===\n"
                    normalize_name = self.normalize_test_name(subcase.name)
                    # test case name from junit.xml and re-build a new regx
                    case_pattern = re.sub(r"(?<=\w)-", "[\\\\W\\\\s_]+", normalize_name)
                    pattern = re.compile(r'::\s{2,}' + fr'{case_pattern}')
                    whole_task_out = self._get_taskout_by_task_id(subcase.taskid)
                    match = pattern.search(whole_task_out)
                    done_match = re.search("Uploading resultoutputfile.log .done", whole_task_out[match.start():])
                    if match and done_match:
                        done_match_end = match.start() + done_match.end()
                        subcase.new_block += match_log_title
                        subcase.new_block += whole_task_out[match.start():done_match_end]
                    else:
                        continue

    def _process_panic_cases(self):
        """Handle panic cases separately, targeting specific (none) test cases in kernel tasks"""
        panic_recipes = set()
        for recipe in self.beaker_root.findall('.//recipe'):
            if recipe.get('result') == 'Panic':
                panic_recipes.add(recipe.get('id'))
                logger.info(f"Found panic recipe: {recipe.get('id')}")

        # For each panic recipe, find the specific (none) test case in kernel tasks
        for recipe_id in panic_recipes:
            logger.info(f"Processing panic recipe: {recipe_id}")

            # Find the recipe element
            recipe_elem = self.beaker_root.find(f'.//recipe[@id="{recipe_id}"]')
            if recipe_elem is None:
                continue

            hostname = recipe_elem.get('system')
            if not hostname:
                logger.warning(f"No hostname found for panic recipe {recipe_id}")
                continue

            # Find the corresponding testsuite in junit.xml
            target_testsuite = None
            for testsuite in self.root.findall('testsuite'):
                if testsuite.get('hostname') == hostname:
                    target_testsuite = testsuite
                    break

            if target_testsuite is None:
                logger.warning(f"No testsuite found for hostname {hostname} in junit.xml")
                continue

            # Find all kernel (none) test cases that are not skipped
            target_testcases = []
            for testcase in target_testsuite.findall('testcase'):
                classname = testcase.get('classname', '')
                name = testcase.get('name', '').strip()
                skipped_elem = testcase.find('skipped')

                # Look for kernel test cases with name "(none)" that are not skipped
                if (classname.startswith("/kernel") and
                        name == "(none)" and
                        skipped_elem is None):
                    target_testcases.append(testcase)
                    logger.info(f"Found target (none) test case for panic: {classname}")

            # Process each target test case
            for target_testcase in target_testcases:
                console_url = self._get_console_log_url(recipe_id)
                panic_content = "=== SYSTEM PANIC DETECTED ===\n"
                panic_content += "Beaker job was terminated due to system panic/kernel crash\n"

                if console_url:
                    logger.info(f"Using console.log for panic analysis: {console_url}")
                    if console_url in self.url_context:
                        console_content = self.url_context.get(console_url)
                        if console_content:
                            logger.info(f"Found console.log in cache, size: {len(console_content)}")
                            console_analysis = self._extract_panic_from_console(console_content)
                            panic_content += "=== Console Log Analysis (showing panic-related errors) ===\n"
                            panic_content += console_analysis
                        else:
                            panic_content += "Console.log downloaded but content is empty\n"
                    else:
                        panic_content += f"Console.log available but not downloaded: {console_url}\n"
                else:
                    logger.warning(f"Console.log URL not found for recipe {recipe_id}")
                    panic_content += "Console.log URL not found in Beaker XML\n"

                # Add or update failure element in the target (none) test case
                failure_elem = target_testcase.find('failure')
                if failure_elem is None:
                    failure_elem = ETree.SubElement(target_testcase, 'failure')

                failure_elem.set('message', 'System Panic Detected')
                failure_elem.set('type', 'failure')
                failure_elem.text = panic_content
                logger.info(f"Found console log: {failure_elem.text[:100]}")

                classname = target_testcase.get('classname', '')
                logger.info(f"Successfully added panic failure to (none) test case: {classname}")

                # Create a corresponding CaseProperty object for the panic test case.
                # Since the panic use case does not have system-out,
                # we need to obtain task information from the Beaker XML.
                task_id = None
                for task_elem in recipe_elem.findall('.//task'):
                    if task_elem.get('name', '').startswith('/kernel'):
                        task_id = task_elem.get('id')
                        break
                if task_id:
                    # Create a unique combaine_id to identify this panic use case.
                    combaine_id = f"{task_id}_panic"
                    if combaine_id not in self.testcases:
                        subcase = CaseProperty("(none)")
                        subcase.taskid = task_id
                        subcase.resultid = "panic"  # Special markings
                        subcase.failure = True
                        subcase.failure_message = 'System Panic Detected'
                        subcase.new_block = panic_content

                        # Get the corresponding taskout.log URLs
                        subcase.task_out_urls = self.taskid_task_log_url.get(task_id, [])

                        self.testcases[combaine_id] = subcase
                        logger.info(f"Created CaseProperty for panic case: {combaine_id}")


    def get_father_log_content(self, subcase):
        if subcase.name in self._EXCLUDED_LOG_CASES:
            return ''
        return '\n'.join(
            f"=== Come from url: {url} ===\n{content}"
            for url in subcase.task_out_urls
            if (content := self.url_context.get(url))
        )

    @staticmethod
    def _extract_panic_from_console(console_content, context_lines=100):
        """
        Analyze the console log to extract error messages and their context.
        :param console_content: Console log content
        :param context_lines: Context line numbers
        :return: Formatted error message
        """
        if not console_content:
            return "No console log content available"

        lines = console_content.split('\n')
        error_blocks = []
        # Used to track row indexes that have already been processed, avoiding duplication.
        matched_indices = set()
        for i, line in enumerate(lines):
            # Check if the line has already been included in the previous error block.
            if i in matched_indices:
                continue

            for pattern in FAILURE_STRINGS:

                # Compute context scope
                if pattern in line:
                    start_line = max(0, i - context_lines)
                    end_line = min(len(lines), i + context_lines + 1)

                    # Mark these behaviors as handled to avoid repetition
                    for j in range(start_line, end_line):
                        matched_indices.add(j)
                    # Extract context block
                    context_block = lines[start_line:end_line]
                    error_blocks.append('\n'.join(context_block))
                    break

        if not error_blocks:
            return "No panic-related errors found in console log"
        # Formatted output, limiting the display of a maximum of 5 error blocks to avoid excessively long output.
        max_blocks = 10
        if len(error_blocks) > max_blocks:
            error_blocks = error_blocks[:max_blocks]
            error_blocks.append(f"... and {len(error_blocks) - max_blocks} more error blocks truncated")

        return "\n\n".join([f"=== Error Block {i + 1} ===\n{block}" for i, block in enumerate(error_blocks)])

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

            # check panic
            is_already_processed_by_panic = (
                    failure_element is not None and
                    failure_element.get('message') == 'System Panic Detected'
            )

            #If a panic has already occurred, ensure that the corresponding CaseProperty is also handled correctly.
            if is_already_processed_by_panic and name == "(none)":
                logger.debug(f"Processing panic case: {classname} {name}")

                for combaine_id, subcase in self.testcases.items():
                    logger.info(f"print combaine_id and subcase.resultid subcase.name: {combaine_id} {subcase.resultid} {subcase.name}")
                    if subcase.resultid == "panic" and subcase.name == "(none)":

                        if failure_element.text != subcase.new_block:
                            failure_element.text = subcase.new_block
                        logger.info(f"Updated panic failure element for {classname} {name}")
                        break
                continue

            is_panic = False
            system_out = testcase.find('system-out')
            if system_out is not None and system_out.text:
                taskid_resultid = self.search_taskid_and_resultid_from_system_out(system_out)
                if taskid_resultid:
                    subcase = self.testcases.get(taskid_resultid)
                    if subcase:
                        task_elem = self.beaker_root.find(f'.//task[@id="{subcase.taskid}"]')
                        if task_elem is not None and task_elem.get('result') == 'Panic':
                            is_panic = True

            if name != '(main)':  # for sub kernel case
                system_out = testcase.find('system-out')
                # # Handling special test cases: If the name is in _EXCLUDED_LOG_CASES,
                # copy the failure message to system-out.
                if name in self._EXCLUDED_LOG_CASES:
                    # Ensure system-out exists
                    if system_out is None:
                        system_out = ETree.SubElement(testcase, 'system-out')
                    # If there is a failure element and a message, copy its content to system-out.
                    if failure_element is not None:
                        failure_message = failure_element.get('message', '')
                        system_out_content = []
                        if failure_message:
                            system_out_content.append(f"Failure Message: {failure_message}")
                        if not system_out_content:
                            system_out_content.append(
                                f"Test case {name} failed - No detailed failure information available")
                        system_out.text = '\n'.join(system_out_content)
                        logger.debug(f"Set system-out for excluded test case {name}: {system_out.text[:100]}...")


                if system_out is None or system_out.text is None or len(system_out.text.strip().splitlines()) == 0:
                    if failure_element is not None and failure_element.get('message'):
                        if failure_element.text is None:
                            failure_element.text = ""
                        failure_element.text = (f"test {name} didn't has any system-out elements\n"
                                                f"{failure_element.get('message')}")
                else:
                    taskid_resultid = self.search_taskid_and_resultid_from_system_out(system_out)
                    if not taskid_resultid:
                        logger.error(f"didn't found task_id on sub kernel test cases: {classname} {name}")
                        continue
                    subcase = self.testcases.get(taskid_resultid)
                    if not subcase:
                        # not all the subcase failed
                        logger.debug(f"didn't found subcase on sub kernel test cases: {classname} {name}")
                        continue
                    else:
                        father_log_content = self.get_father_log_content(subcase)
                        # Build log content: raw system-out + father_log + debug_block
                        full_log_content = [system_out.text.strip()]
                        if father_log_content:
                            full_log_content.append(father_log_content)
                        if subcase.debug_block:
                            full_log_content.append(subcase.debug_block)
                        system_out.text = '\n'.join(full_log_content)

                    # Handle failure cases
                    if subcase.failure and hasattr(subcase, 'new_block') and subcase.new_block:
                        # Ensure failure element exists
                        if failure_element is None:
                            failure_element = ETree.SubElement(testcase, 'failure')
                        failure_element.set('message', 'fail')
                        failure_element.text = subcase.new_block

                    # panic use cases create or update the failure element
                    if is_panic and taskid_resultid:
                        subcase = self.testcases.get(taskid_resultid)
                        if subcase and hasattr(subcase, 'new_block') and subcase.new_block:
                            # If a failure element does not already exist, create one.
                            if failure_element is None:
                                failure_element = ETree.SubElement(testcase, 'failure')
                            failure_element.set('message', 'System Panic')
                            failure_element.set('type', 'panic')
                            failure_element.text = subcase.new_block
                            logger.info(f"Added panic failure element to {classname} {name}")
            elif name == '(main)':
                # delete failure element and move log to sub task.
                if failure_element is not None:
                    logger.info("delete failure element")
                    testcase.remove(failure_element)

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
                    lines = system_out.text.strip().split()
                    grouped[cls]['system_out'].extend(lines)
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

def create_session() -> requests.Session:
    session = requests.Session()
    retries = Retry(
        total=5,
        backoff_factor=1,
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=frozenset(['GET', 'POST']),
        respect_retry_after_header=True
    )
    adapter = HTTPAdapter(
        max_retries=retries,
        pool_connections=20,
        pool_maxsize=20,
        pool_block=False
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
    last_exception = None
    for attempt in range(3):
        try:
            r = session.get(download_url, timeout=(10, 30))
            r.raise_for_status()
            text = clean_xml_text(r.text)
            return text
        except Exception as error:
            logger.warning(f"Download attempt {attempt + 1} failed for {download_url}: {error}")
            if attempt < 2:
                sleep_time = 2 * (attempt + 1)
                logger.error(f"All download attempts failed for {download_url}")
                sleep(sleep_time)
    error_msg = f"All 3 download attempts failed for {download_url}: {last_exception}"
    logger.error(error_msg)
    raise Exception(error_msg) from last_exception

def write_xml_iteratively(root_element, output_file):
    """Streaming XML writing avoids loading it into memory all at once."""
    with open(output_file, 'wb') as f:
        def write_element(element, depth=0):
            indent = "  " * depth
            tag = element.tag
            attribs = "".join(f' {k}="{v}"' for k, v in element.items())

            if len(element) == 0 and not element.text:
                # empty element
                f.write(f"{indent}<{tag}{attribs}/>\n".encode('utf-8'))
            else:
                # Start tag
                f.write(f"{indent}<{tag}{attribs}>".encode('utf-8'))

                # Text content
                if element.text:
                    f.write(element.text.encode('utf-8'))

                # child elements
                if len(element) > 0:
                    f.write(b'\n')
                    for child in element:
                        write_element(child, depth + 1)
                    f.write(indent.encode('utf-8'))

                # End tag
                f.write(f"</{tag}>\n".encode('utf-8'))
        write_element(root_element)

def create_zip_with_streaming(processor_obj, zip_file_path, job_id):
    """Create ZIP files using streaming method"""
    with zipfile.ZipFile(zip_file_path, 'w', zipfile.ZIP_DEFLATED) as z:
        arcname = sanitize_filename(f"bkr-junit-{job_id}.xml")

        # First write to a temporary file, then add it to the ZIP.
        with tempfile.NamedTemporaryFile(mode='wb', delete=False) as tmp_xml:
            tmp_xml_path = tmp_xml.name
        try:
            # Streaming XML
            write_xml_iteratively(processor_obj.root, tmp_xml_path)
            # Add temporary files to ZIP
            z.write(tmp_xml_path, arcname)
        finally:
            # Clean up temporary files
            try:
                os.unlink(tmp_xml_path)
            except OSError:
                pass

def upload_to_rp(zip_source_path: str, session: requests.Session, xml_instance=None):
    if cli_args.whiteboard:
        whiteboard = xml_instance.beaker_root.find('whiteboard')
        whiteboard_text = whiteboard.text if whiteboard is not None else ""
        logger.info("got launch name from beaker xml whiteboard：%s", whiteboard_text)
        lunchname = sanitize_filename(whiteboard_text).strip()[:100] if whiteboard_text else f"Beaker Job {JOB_ID}"
    elif cli_args.launchname:
        logger.info("got launch name from self define name：%s", cli_args.launchname)
        lunchname = sanitize_filename(cli_args.launchname).strip()[:100]
    else:
        lunchname = f"Beaker Job {JOB_ID}"

    rp_url = f"{RP_BASE}/api/v1/{RP_PROJECT}/launch/import"
    headers = {
        'Authorization': f'bearer {RP_TOKEN}',
    }

    # Get file size
    file_size = os.path.getsize(zip_source_path)
    file_size_megabyte = file_size / 1024 / 1024

    logger.info(f"Uploading ZIP file: {file_size_megabyte:.2f} MB")

    attributes = [{
        "key": "beaker_job_id",
        "system": False,
        "value": JOB_ID
    }]
    custom_attrs = {}

    # Add user-defined properties
    if cli_args.attributes:
        for attr in cli_args.attributes:
            try:
                if '=' in attr:
                    key, value = attr.split('=', 1)
                    key = key.strip()
                    value = value.strip()
                    if key and value:
                        if key in custom_attrs:
                            logger.info(f"Overwriting attribute '{key}': '{custom_attrs[key]}' -> '{value}'")
                        custom_attrs[key] = value
                    else:
                        logger.warning(f"Ignoring invalid attribute format: {attr}")
                else:
                    logger.warning(f"Ignoring malformed attribute (missing '='): {attr}")
            except Exception as parse_error:
                logger.warning(f"Failed to parse attribute '{attr}': {parse_error}")

    for key, value in custom_attrs.items():
        if key.lower() != 'beaker_job_id':
            attributes.append({
                "key": key,
                "system": False,
                "value": value
            })
            logger.info(f"Added custom attribute: {key}={value}")
        else:
            logger.warning(f"Skipping reserved attribute key: {key}")

    # The start time must be obtained from the Beaker XML; otherwise, an error will occur and the program will exit.
    if xml_instance is None:
        logger.error("JUnitLogProcessor instance is required for timing information")
        sys.exit(1)

    try:
        start_time_utc = xml_instance.get_launch_start_time_iso()
    except Exception as got_time_error:
        logger.error(f"Failed to get start time from Beaker XML: {got_time_error}")
        sys.exit(1)

    # Build JSON data
    launch_data = {
        "attributes": attributes,
        "description": f"Beaker Job {JOB_WEB_URL}",
        "mode": "DEFAULT",
        "name": f"{lunchname}",
        "startTime": start_time_utc
    }

    logger.info(f"Launch data JSON: {json.dumps(launch_data, indent=2)}")

    # multipart/form-data data
    with open(zip_source_path, 'rb') as f:
        files = {
            'file': (os.path.basename(zip_source_path), f, 'application/x-zip-compressed'),
            'launchImportRq': (
                None,
                json.dumps(launch_data),
                'application/json'
            )
        }

        logger.info("Uploading to ReportPortal: %s", zip_source_path)
        logger.info("URL: %s", rp_url)
        logger.info("Headers: %s", headers)

        try:
            resp = session.post(rp_url,
                                headers=headers,
                                files=files,
                                timeout=(60, 600),
                                verify=True,
                                allow_redirects=True
                                )

            # Detailed response logs
            logger.info(f"Response status code: {resp.status_code}")
            logger.info(f"Response headers: {dict(resp.headers)}")

            if resp.status_code != 200:
                logger.error(f"Response content: {resp.text}")
                # Attempt to parse error messages
                if "start time" in resp.text.lower() or "time" in resp.text.lower():
                    logger.error(f"Time-related error. Launch start time was: {start_time_utc}")

            resp.raise_for_status()

        except requests.exceptions.HTTPError as http_error:
            logger.error(f"HTTP Error: {http_error}")
            if 'resp' in locals():
                logger.error(f"Response text: {resp.text}")
            raise
        except Exception as unexpected_error:
            logger.error(f"Upload failed: {unexpected_error}")
            raise

    data = resp.json()
    launch_uuid = data.get('data', {}).get('id')
    launch_message = data.get('message')
    logger.info("Upload successful, Launch UUID: %s", launch_message)

    # Get Launch Details
    get_url = f"{RP_BASE}/api/v1/{RP_PROJECT}/launch/{launch_uuid}"
    try:
        info_resp = session.get(get_url, headers=headers)
        info_resp.raise_for_status()
        info = info_resp.json()
        launch_id = info.get('id')
        logger.info(f"Launch id is: {launch_id}")
    except Exception as launch_error:
        logger.warning(f"Could not get launch details: {launch_error}")


if __name__ == "__main__":
    # Set memory limits
    try:
        resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))
        logger.info(f"Set main process memory limit to {MEMORY_LIMIT / 1024 / 1024}MB")
    except (ValueError, resource.error) as e:
        logger.warning(f"Unable to set memory limit: {e}")

    # Disable bytecode caching
    sys.dont_write_bytecode = True

    session_beaker = create_session()
    session_rp = create_session()

    try:
        logger.info(f"download JUnit XML: {JUNIT_URL}")
        junit_xml = download_text(JUNIT_URL, session_beaker)
        logger.info(f"download Beaker XML: {BEAKER_XML_URL}")
        beaker_xml = download_text(BEAKER_XML_URL, session_beaker)
    except Exception as beaker_element_error:
        logger.error(f"Downloading JUnit XML failed: {beaker_element_error}")
        sys.exit(1)

    logger.info("organize test result...")
    try:
        processor = JUnitLogProcessor(
            junit_xml,
            beaker_xml_source=beaker_xml,
            from_string=True,
            debug=cli_args.debug
        )
    except Exception as init_JUnitLogProcessor_failed:
        logger.error(f"Failed to initialize processor: {init_JUnitLogProcessor_failed}")
        sys.exit(1)

    logger.info("Reorganizing XML...")
    processor.re_org()

    # Process all sub-cases
    logger.info("Processing sub-use cases...")
    download_session = create_session()
    try:
        processor.process_all_subcases(download_session)
    except TimeoutError:
        logger.error(f"Global timeout of {GLOBAL_TIMEOUT}s exceeded")
        sys.exit(7)
    except Exception as e:
        logger.error(f"Error processing subcases: {e}")
        sys.exit(8)
    finally:
        download_session.close()

    # generated ZIP
    logger.info("Generated ZIP file...")
    with tempfile.NamedTemporaryFile(delete=False, suffix=".zip") as tmpzip:
        zip_path = tmpzip.name
    try:
        create_zip_with_streaming(processor, zip_path, JOB_ID)
    except MemoryError:
        logger.error("Insufficient memory!!!")
        sys.exit(9)

    logger.info("create ZIP：%s", zip_path)
    file_size_bytes = os.path.getsize(zip_path)
    file_size_mb = file_size_bytes / (1024 * 1024)
    if file_size_mb > ZIP_SIZE_LIMIT / (1024 * 1024):
        logger.error(f"Warning: File size {file_size_mb:.2f}MB exceeds {ZIP_SIZE_LIMIT / 1024 / 1024}MB limit")
        sys.exit(2)
    else:
        logger.info(f"file size：{file_size_mb:.2f}MB")

    # upload
    try:
        upload_to_rp(zip_path, session_rp, processor)
    except Exception as e:
        logger.exception(f"Failed to upload or update description: {e}")
        sys.exit(1)

    # cleanup
    del processor
    gc.collect()

    try:
        os.remove(zip_path)
    except OSError:
        pass

    # Close session
    session_beaker.close()
    session_rp.close()
    if cli_args.debug:
        tracemalloc.stop()

    logger.info("All completed, please check Report Portal")