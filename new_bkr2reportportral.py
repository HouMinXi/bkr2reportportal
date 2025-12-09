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
import gc
import resource
import tracemalloc
import time
import signal
from datetime import datetime, timezone
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
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

EXCLUDED_LOG_CASES = {
    '10_avc_check',
    '99_reboot',
    '10_localwatchdog',
    'exit_code'
}
# Regular expressions used to escape special characters in XML
XML_ENTITY_PATTERN = re.compile(r'&(?!(amp|lt|gt|quot|apos|#x[0-9a-fA-F]+|#\d+);)')

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


class JobStatus:
    """Class to track job status and determine processing strategy"""

    def __init__(self, beaker_root):
        self.beaker_root = beaker_root
        # Try to get job-level result and status
        self.job_result = beaker_root.get('result')
        self.job_status = beaker_root.get('status')

        self.recipe_results = []
        self._analyze_recipes()

        # If job-level attributes are missing, infer from recipes
        if self.job_result is None or self.job_status is None:
            self._infer_job_status_from_recipes()

        logger.info(f"Job Status: Result={self.job_result}, Status={self.job_status}")

    def _analyze_recipes(self):
        """Analyze all recipes in the job"""
        for recipe in self.beaker_root.findall('.//recipe'):
            recipe_info = {
                'id': recipe.get('id'),
                'result': recipe.get('result'),
                'status': recipe.get('status'),
                'system': recipe.get('system'),
                'has_panic': recipe.get('result') == 'Panic',
                'has_warn': recipe.get('result') == 'Warn',
                'has_fail': recipe.get('result') == 'Fail',
                'has_pass': recipe.get('result') == 'Pass',
                'is_cancelled': recipe.get('status') == 'Cancelled',
                'is_aborted': recipe.get('status') == 'Aborted',
                'is_completed': recipe.get('status') == 'Completed'
            }
            self.recipe_results.append(recipe_info)
            logger.info(f"Recipe {recipe_info['id']}: result={recipe_info['result']}, status={recipe_info['status']}")

    def _infer_job_status_from_recipes(self):
        """Infer job status from recipe statuses when job-level attributes are missing"""
        if not self.recipe_results:
            self.job_result = 'Unknown'
            self.job_status = 'Unknown'
            return

        # Priority: Panic > Fail > Warn > Pass
        results = [r['result'] for r in self.recipe_results]
        statuses = [r['status'] for r in self.recipe_results]

        # Determine overall result
        if 'Panic' in results:
            self.job_result = 'Panic'
        elif 'Fail' in results:
            self.job_result = 'Fail'
        elif 'Warn' in results:
            self.job_result = 'Warn'
        elif 'Pass' in results:
            self.job_result = 'Pass'
        else:
            self.job_result = 'Unknown'

        # Determine overall status
        # Priority: Aborted > Cancelled > Completed
        if 'Aborted' in statuses:
            self.job_status = 'Aborted'
        elif 'Cancelled' in statuses:
            self.job_status = 'Cancelled'
        elif 'Completed' in statuses:
            self.job_status = 'Completed'
        else:
            self.job_status = 'Unknown'

        logger.info(f"Inferred job status from recipes: Result={self.job_result}, Status={self.job_status}")

    def should_process_job(self):
        """Determine if we should process this job at all"""
        # If job is Pass and not forced, skip it
        if self.job_result == 'Pass':
            return False
        return True

    def need_console_log(self):
        """Determine if we need console.log for panic analysis"""
        for recipe in self.recipe_results:
            if recipe['has_panic']:
                return True
        return False

    def has_panic_recipe(self):
        """Check if any recipe has panic"""
        return any(r['has_panic'] for r in self.recipe_results)

    def has_warn_aborted_recipe(self):
        """Check if any recipe has Warn+Aborted"""
        return any(r['has_warn'] and r['is_aborted'] for r in self.recipe_results)

    def has_fail_completed_recipe(self):
        """Check if any recipe has Fail+Completed"""
        return any(r['has_fail'] and r['is_completed'] for r in self.recipe_results)

    def get_panic_recipes(self):
        """Get list of recipe IDs with panic"""
        return [r['id'] for r in self.recipe_results if r['has_panic']]

    def get_panic_systems(self):
        """Get list of systems with panic"""
        return [r['system'] for r in self.recipe_results if r['has_panic']]

    def get_warn_aborted_recipes(self):
        """Get list of recipe IDs with Warn+Aborted"""
        return [r['id'] for r in self.recipe_results if r['has_warn'] and r['is_aborted']]

    def get_fail_completed_recipes(self):
        """Get list of recipe IDs with Fail+Completed"""
        return [r['id'] for r in self.recipe_results if r['has_fail'] and r['is_completed']]

    def get_all_recipe_statuses(self):
        """Get summary of all recipe statuses"""
        summary = {}
        for recipe in self.recipe_results:
            key = f"{recipe['result']}_{recipe['status']}"
            summary[key] = summary.get(key, 0) + 1
        return summary


class TestCaseInfo:
    """Information about a test case"""
    def __init__(self, name):
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
        self.error = False
        """save original error message"""
        self.error_message = ''
        self.skipped = False
        """save original skip message"""
        self.skipped_message = ''
        """
        if a sub test cases failed and has multiple url in systemout, we should search more detail log from taskout.log
        """
        self.new_block = ''
        """
        Used to store debug-level taskout.log matching content
        """
        self.debug_block = ''


class BeakerJobProcessor:
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

        # Initialize job status analyzer
        if from_string:
            self.beaker_root = ETree.fromstring(beaker_xml_source)
        else:
            if not os.path.isfile(beaker_xml_source):
                raise FileNotFoundError(f"Beaker XML file not found: {beaker_xml_source}")
            beaker_tree = ETree.parse(beaker_xml_source)
            self.beaker_root = beaker_tree.getroot()

        self.job_status = JobStatus(self.beaker_root)

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

        # Validate XML structure
        if self.root.tag != 'testsuites':
            logger.error(f"Received XML is not a valid JUnit testsuites")
            sys.exit(1)

        # parse beaker xml
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
            # If still no valid start time found, try to get from result elements
            if self.launch_start_time is None:
                for result in self.beaker_root.findall('.//result'):
                    start_time_str = result.get('start_time')
                    if start_time_str:
                        try:
                            result_time = datetime.strptime(start_time_str, '%Y-%m-%d %H:%M:%S')
                            result_time = result_time.replace(tzinfo=timezone.utc)
                            if self.launch_start_time is None or result_time < self.launch_start_time:
                                self.launch_start_time = result_time
                                logger.info(
                                    f"Found result start time: {result_time} from result {result.get('id')}")
                        except ValueError as time_data_error:
                            logger.warning(
                                f"Failed to parse result start_time '{start_time_str}': {time_data_error}")

            if self.launch_start_time is None:
                raise ValueError("No valid start_time found in Beaker XML recipes")

            # Get latest finish time
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

            # Also try to get finish time from result elements
            for result in self.beaker_root.findall('.//result'):
                # Result elements might not have finish_time, but we can use start_time if no recipe finish_time found
                if self.launch_end_time is None:
                    start_time_str = result.get('start_time')
                    if start_time_str:
                        try:
                            result_time = datetime.strptime(start_time_str, '%Y-%m-%d %H:%M:%S')
                            result_time = result_time.replace(tzinfo=timezone.utc)
                            if self.launch_end_time is None or result_time > self.launch_end_time:
                                self.launch_end_time = result_time
                        except ValueError as time_data_error:
                            logger.warning(
                                f"Failed to parse result start_time as finish time '{start_time_str}': {time_data_error}")
            if self.launch_end_time:
                duration = self.launch_end_time - self.launch_start_time
                logger.info(
                    f"Beaker job actual timing: {self.launch_start_time} to {self.launch_end_time} (duration: {duration})")

        except Exception as extract_error:
            logger.error(f"Error extracting time from Beaker XML: {extract_error}")
            # Set a fallback time
            self.launch_start_time = datetime.now(timezone.utc)
            self.launch_end_time = None
            logger.warning(f"Using fallback start time due to error: {self.launch_start_time}")

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
    def normalize_test_name(test_name):
        """Standardized test names for regular expression matching"""
        return re.sub(r"(?<=\w)[\W\s_]+(?=[\w\n])", "-", test_name)

    def _get_taskout_by_task_id(self, task_id: str) -> str:
        """Retrieve taskout.log content based on task_id"""
        task_out_urls = self.taskid_task_log_url.get(task_id)
        if not task_out_urls:
            logger.debug(f"task_id {task_id}没有找到taskout.log URL")
            return ""
        return self.url_context.get(task_out_urls[0], "")

    def process_all_testcases(self, session: requests.Session):
        """
        Process all test cases with optimized memory usage
        """
        self.session = session
        # Set global timeout
        signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(GLOBAL_TIMEOUT)

        try:
            try:
                # Step 1: Build mappings
                log_memory_usage("Before starting to process sub-use cases")
                self._build_task_mappings()
                gc.collect()
                log_memory_usage("After flushing_all_tasks")
            except Exception as flushing_all_tasks_error:
                logger.error(f"flushing_all_tasks failed: {str(flushing_all_tasks_error)}")

            try:
                # Step 2: Download logs
                self.download_logs_concurrently(session)
                gc.collect()
                log_memory_usage("After downloading logs")
            except Exception as download_logs_concurrently_error:
                logger.error(f"download_logs_concurrently failed: {str(download_logs_concurrently_error)}")

            try:
                # Step 3: Process failures and errors
                self._process_failures_and_errors()
                gc.collect()
                log_memory_usage("After setting the error text")
            except Exception as set_process_failures_and_errors:
                logger.error(f"_process_failures_and_errors failed: {str(set_process_failures_and_errors)}")

            try:
                # Step 4: Process panic cases
                if self.job_status.need_console_log():
                    self._process_panic_cases()
                    gc.collect()
                    log_memory_usage("After processing panic cases")
            except Exception as need_console_log:
                logger.error(f"need_console_log failed: {str(need_console_log)}")
        except Exception as error:
            logger.error(f"process_all_subcases failed: {str(error)}")
        finally:
            # Cancel timeout
            signal.alarm(0)

    def _build_task_mappings(self):
        """Build mappings between task IDs, result IDs and log URLs"""
        # Process all test cases in the job
        all_test_cases = self.root.findall(".//testcase")

        # First pass: Collect all (main) test cases and their taskout.log URLs
        # We'll collect all taskout.log URLs but only process those with failing tests
        for testcase in all_test_cases:
            if testcase.get("name", "").strip().lower() == '(main)':
                system_out = testcase.find('system-out')
                if system_out is None or not system_out.text:
                    continue

                # Extract taskout.log URL
                taskout_url = ""
                for url in system_out.text.strip().splitlines():
                    if 'taskout.log' in url.lower():
                        taskout_url = url
                        break

                if taskout_url:
                    task_match = TASK_ID_PATTERN.search(taskout_url)
                    if task_match:
                        task_id = task_match.group(1)
                        self.taskid_task_log_url[task_id].append(taskout_url)
                        logger.debug(f"Added taskout.log for task_id {task_id}: {taskout_url}")

        # Second pass: Process non-(main) test cases
        for testcase in all_test_cases:
            name = testcase.get("name", "").strip()
            if name.lower() == '(main)':
                continue

            # Check for failure, error, or skipped status
            failure_elem = testcase.find('failure')
            error_elem = testcase.find('error')
            skipped_elem = testcase.find('skipped')

            # If none of these elements exist, it's a passed test case - skip it
            if failure_elem is None and error_elem is None and skipped_elem is None:
                logger.debug(f"Skipping passed test case: {name}")
                continue

            system_out = testcase.find('system-out')
            if system_out is None or not system_out.text:
                continue

            # Collect ALL log URLs from system-out for this test case
            log_urls = []
            for url in system_out.text.strip().splitlines():
                # Skip empty lines
                if not url.strip():
                    continue
                # Collect all .log files
                if '.log' in url.lower():
                    log_urls.append(url)

            if not log_urls:
                continue

            # Create TestCaseInfo object
            testcase_info = TestCaseInfo(name)
            testcase_info.classname = testcase.get('classname', '')

            if failure_elem is not None:
                testcase_info.failure = True
                testcase_info.failure_message = failure_elem.get('message', '')
            elif error_elem is not None:
                testcase_info.error = True
                testcase_info.error_message = error_elem.get('message', '')
            elif skipped_elem is not None:
                testcase_info.skipped = True
                testcase_info.skipped_message = skipped_elem.get('message', '')

            testcase_info.sub_task_urls = log_urls

            # Extract task ID and result ID
            for url in log_urls:
                result_match = RESULT_ID_PATTERN.search(url)
                if result_match:
                    testcase_info.taskid = result_match.group(1)
                    testcase_info.resultid = result_match.group(2)

                    # Get corresponding taskout.log URLs
                    testcase_info.task_out_urls = self.taskid_task_log_url.get(testcase_info.taskid, [])

                    # Store in mappings
                    self.taskid_resultid[testcase_info.taskid].append(testcase_info.resultid)

                    # Use taskid_resultid as unique key
                    unique_id = f"{testcase_info.taskid}_{testcase_info.resultid}"
                    self.testcases[unique_id] = testcase_info
                    logger.debug(f"Added test case: {unique_id} - {testcase_info.classname} {name}")
                    break

        # Remove taskout.log URLs for tasks that don't have any failing/error/skipped test cases
        # We need to check which tasks actually have non-pass test cases
        tasks_with_non_pass_cases = set()
        for testcase_info in self.testcases.values():
            if testcase_info.taskid:
                tasks_with_non_pass_cases.add(testcase_info.taskid)

        # Filter out taskout.log URLs for tasks that don't have non-pass test cases
        tasks_to_remove = []
        for task_id in self.taskid_task_log_url:
            if task_id not in tasks_with_non_pass_cases:
                tasks_to_remove.append(task_id)

        for task_id in tasks_to_remove:
            logger.debug(f"Removing taskout.log URLs for task {task_id} (all test cases passed)")
            del self.taskid_task_log_url[task_id]

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

        # Add resultoutputfile.log URLs
        for testcase_info in self.testcases.values():
            all_urls.update(testcase_info.sub_task_urls)

        # Add console.log for panic cases if needed
        if self.job_status.need_console_log():
            for recipe_id in self.job_status.get_panic_recipes():
                console_url = self._get_console_log_url(recipe_id)
                if console_url and console_url not in all_urls:
                    all_urls.add(console_url)
                    logger.info(f"Added console.log for panic recipe {recipe_id}: {console_url}")

        logger.info(f"Need to download {len(all_urls)} log files")

        if not all_urls:
            logger.info("No logs to download (all test cases passed)")
            return

        # Check file sizes first with timeout
        logger.info("Checking file sizes...")
        url_sizes = {}
        total_estimated_size = 0

        for url in all_urls:
            size = self._get_content_length_with_timeout(url, session)
            url_sizes[url] = size

            if size > SINGLE_FILE_LIMIT:
                logger.error(f"Log file {url} size {size / 1024 / 1024:.2f} MB exceeds limit")
                sys.exit(5)

            total_estimated_size += size
            if total_estimated_size > TOTAL_SIZE_LIMIT:
                logger.error(f"Total estimated size {total_estimated_size / 1024 / 1024:.2f} MB exceeds limit")
                sys.exit(6)

        logger.info(f"Total estimated size: {total_estimated_size / 1024 / 1024:.2f} MB")

        # Download files
        self._download_files(all_urls, session, url_sizes)

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

    def _download_files(self, all_urls, session, url_sizes):
        """Download files with concurrency control"""
        urls_to_download = list(all_urls)
        completed_count = 0
        start_time = time.time()

        # Separate taskout.log from other files
        taskout_urls = [url for url in urls_to_download if 'taskout.log' in url]
        other_urls = [url for url in urls_to_download if 'taskout.log' not in url]

        logger.info(f"Found {len(taskout_urls)} taskout.log files and {len(other_urls)} other files")

        # Download other files first
        if other_urls:
            logger.info("Downloading non-taskout files first...")
            self._download_file_batch(other_urls, session, url_sizes, completed_count, len(all_urls), start_time)

        # Then download taskout.log files
        if taskout_urls:
            logger.info("Downloading taskout.log files...")
            self._download_file_batch(taskout_urls, session, url_sizes, completed_count, len(all_urls), start_time)

    def _download_file_batch(self, urls, session, url_sizes, completed_count, total_files, start_time):
        """Download a batch of files"""
        batch_size = 8
        for i in range(0, len(urls), batch_size):
            batch_urls = urls[i:i + batch_size]
            logger.info(f"Processing batch {i // batch_size + 1}/{(len(urls) - 1) // batch_size + 1}")

            batch_results = self._download_batch(batch_urls, session, url_sizes)

            # Process results
            for url, success, content in batch_results:
                completed_count += 1
                if success and content is not None:
                    processed_content = clean_xml_text(content)
                    self.url_context[url] = processed_content

                    elapsed = time.time() - start_time
                    rate = completed_count / elapsed if elapsed > 0 else 0
                    logger.info(f"Progress: {completed_count}/{total_files} "
                                f"({completed_count / total_files * 100:.1f}%) "
                                f"- {rate:.2f} files/sec - {os.path.basename(url)}")
                else:
                    logger.error(f"Failed to download {url}")

            log_memory_usage(f"After batch {i // batch_size + 1}")
            time.sleep(0.5)

    def _download_batch(self, batch_urls, session, url_sizes):
        """Download a batch of URLs"""
        results = []
        batch_total_size = sum(url_sizes.get(url, 0) for url in batch_urls)

        with tqdm(total=batch_total_size, unit='B', unit_scale=True,
                  desc="Downloading batch", leave=False) as pbar:
            with ThreadPoolExecutor(max_workers=min(len(batch_urls), 8)) as executor:
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

        # Check if already downloaded
        if url in self.url_context:
            return self.url_context[url]

        # Check size limits
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
            chunk_size = 64 * 1024  # 64KB

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

            processed_content = clean_xml_text(decoded_content)
            self.url_context[url] = processed_content
            return processed_content

        except Exception as error:
            elapsed = time.time() - start_time
            logger.warning(f"Download failed for {url} after {elapsed:.2f}s: {str(error)}")
            raise

    def _process_failures_and_errors(self):
        """Process all failure and error test cases"""
        for unique_id, testcase_info in self.testcases.items():
            if testcase_info.skipped:
                continue

            testcase_info.new_block = ""

            # Add failure or error message if present
            if testcase_info.failure and testcase_info.failure_message:
                testcase_info.new_block += f"=== Failure Message ===\n{testcase_info.failure_message}\n\n"
            elif testcase_info.error and testcase_info.error_message:
                testcase_info.new_block += f"=== Error Message ===\n{testcase_info.error_message}\n\n"

            if testcase_info.failure:
                if testcase_info.name == '10_avc_check':
                    # For avc_check, look for avc.log
                    for url in testcase_info.sub_task_urls:
                        if 'avc.log' in url.lower():
                            content = self.url_context.get(url, "")
                            if content:
                                testcase_info.new_block += f"\n=== From avc.log ===\n"
                                testcase_info.new_block += content
                                break
                    # If no avc.log, fall back to any log
                    if not testcase_info.new_block or "=== From avc.log ===" not in testcase_info.new_block:
                        for url in testcase_info.sub_task_urls:
                            content = self.url_context.get(url, "")
                            if content:
                                filename = os.path.basename(url)
                                testcase_info.new_block += f"\n=== From {filename} ===\n"
                                testcase_info.new_block += content
                                break
                elif testcase_info.name in ['99_reboot', '10_localwatchdog']:
                    testcase_info.failure_message = testcase_info.name
                    testcase_info.new_block += f"Test case {testcase_info.name} failed\n"
                elif testcase_info.name == 'exit_code':
                    testcase_info.new_block += f"{testcase_info.failure_message}"
                else:
                    resultoutput_added = False
                    # Common failure test cases - always try resultoutputfile.log first
                    for url in testcase_info.sub_task_urls:
                        if 'resultoutputfile.log' in url.lower():
                            content = self.url_context.get(url, "")
                            if content:
                                testcase_info.new_block += f"\n=== From resultoutputfile.log ===\n"
                                testcase_info.new_block += content
                                resultoutput_added = True
                                break  # Only add first resultoutputfile.log

                    # If no resultoutputfile.log found, try to get any log
                    if not resultoutput_added:
                        for url in testcase_info.sub_task_urls:
                            content = self.url_context.get(url, "")
                            if content:
                                filename = os.path.basename(url)
                                testcase_info.new_block += f"\n=== From {filename} ===\n"
                                testcase_info.new_block += content
                                break
                    # Only add taskout.log content if we can precisely match it
                    # AND we haven't added resultoutputfile.log content (if we have, we don't need taskout.log)
                    if testcase_info.task_out_urls:
                        whole_task_out = self._get_taskout_by_task_id(testcase_info.taskid)

                        if whole_task_out:
                            # Try to precisely match the test case in taskout.log
                            normalize_name = self.normalize_test_name(testcase_info.name)
                            case_pattern = re.sub(r"(?<=\w)-", "[\\\\W\\\\s_]+", normalize_name)
                            pattern = re.compile(r'::\s{2,}' + fr'{case_pattern}')

                            match = pattern.search(whole_task_out)
                            if match:
                                # Search for "Uploading resultoutputfile.log .done"
                                done_match = re.search(r"Uploading resultoutputfile.log\s*\.done",
                                                       whole_task_out[match.start():])
                                if done_match:
                                    done_match_end = match.start() + done_match.end()
                                    testcase_info.new_block += f"\n=== From taskout.log (precise match) ===\n"
                                    testcase_info.new_block += whole_task_out[match.start():done_match_end]

            # For non-failure cases, add resultoutputfile.log content if available
            elif not testcase_info.failure and not testcase_info.error:
                for url in testcase_info.sub_task_urls:
                    if 'resultoutputfile.log' in url.lower():
                        content = self.url_context.get(url, "")
                        if content:
                            testcase_info.new_block += f"=== Result Output File ===\n{content}\n\n"
                            break

    def _process_panic_cases(self):
        """Handle panic cases"""
        for recipe_id in self.job_status.get_panic_recipes():
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

            # Process test cases in this testsuite
            has_failure_cases = False
            for testcase in target_testsuite.findall('testcase'):
                # Add panic information to failure cases
                failure_elem = testcase.find('failure')
                if failure_elem is not None:
                    has_failure_cases = True
                    # Update existing failure element with panic info
                    console_url = self._get_console_log_url(recipe_id)
                    panic_content = "=== SYSTEM PANIC DETECTED ===\n"

                    if console_url and console_url in self.url_context:
                        console_content = self.url_context.get(console_url)
                        if console_content:
                            logger.info(f"Found console.log in cache, size: {len(console_content)}")
                            console_analysis = self._extract_panic_from_console(console_content)
                            panic_content += "=== Console Log Analysis (showing panic-related errors) ===\n"
                            panic_content += console_analysis

                    # Append panic info to existing failure
                    existing_text = failure_elem.text or ""
                    failure_elem.text = existing_text + "\n\n" + panic_content if existing_text else panic_content
                    failure_elem.set('message', 'System Panic Detected')
                    break
            # If no failure cases exist, add a new testcase for panic
            if not has_failure_cases:
                # Find the last testcase in this testsuite to get classname
                last_testcase = None
                testcases = target_testsuite.findall('testcase')
                if testcases:
                    last_testcase = testcases[-1]

                # Create new testcase for panic
                new_testcase = ETree.Element('testcase')

                # Use classname from last testcase or a default
                if last_testcase:
                    classname = last_testcase.get('classname', '')
                else:
                    # If no testcases, use a default based on the task
                    for task in self.beaker_root.findall('.//task'):
                        if task.get('recipe_id') == recipe_id:
                            classname = task.get('name', 'unknown')
                            break
                    else:
                        classname = 'unknown'

                new_testcase.set('classname', classname)
                new_testcase.set('name', 'SYSTEM PANIC DETECTED')
                new_testcase.set('time', '0')

                # Create failure element
                failure_elem = ETree.SubElement(new_testcase, 'failure')
                failure_elem.set('message', 'System Panic Detected')

                # Add panic information
                console_url = self._get_console_log_url(recipe_id)
                panic_content = "=== SYSTEM PANIC DETECTED ===\n"

                if console_url and console_url in self.url_context:
                    console_content = self.url_context.get(console_url)
                    if console_content:
                        console_analysis = self._extract_panic_from_console(console_content)
                        panic_content += "=== Console Log Analysis (showing panic-related errors) ===\n"
                        panic_content += console_analysis
                else:
                    panic_content += "No console.log available for analysis. Please check Beaker job logs.\n"
                    panic_content += f"Beaker job URL: {JOB_WEB_URL}\n"
                    panic_content += f"Recipe ID: {recipe_id}\n"
                    panic_content += f"System: {hostname}\n"

                failure_elem.text = panic_content

                # Add system-out with links to relevant logs
                system_out = ETree.SubElement(new_testcase, 'system-out')
                log_links = []

                # Add console.log link if available
                if console_url:
                    log_links.append(console_url)

                # Add other relevant log links from the recipe
                for log_elem in recipe_elem.findall('.//log'):
                    log_url = log_elem.get('href')
                    if log_url and log_url not in log_links:
                        log_links.append(log_url)

                if log_links:
                    system_out.text = "\n".join(log_links)

                # Add the new testcase to the testsuite
                target_testsuite.append(new_testcase)
                logger.info(f"Added panic testcase for recipe {recipe_id} in testsuite {hostname}")

    @staticmethod
    def _extract_panic_from_console(console_content, context_lines=50):
        """Extract panic-related errors from console log"""
        if not console_content:
            return "No console log content available"

        lines = console_content.split('\n')
        error_blocks = []

        for i, line in enumerate(lines):
            for pattern in FAILURE_STRINGS:
                if pattern in line:
                    start_line = max(0, i - context_lines)
                    end_line = min(len(lines), i + context_lines + 1)
                    context_block = lines[start_line:end_line]
                    error_blocks.append('\n'.join(context_block))
                    break

        if not error_blocks:
            return "No panic-related errors found in console log"

        max_blocks = 5
        if len(error_blocks) > max_blocks:
            error_blocks = error_blocks[:max_blocks]

        return "\n\n".join([f"=== Error Block {i + 1} ===\n{block}" for i, block in enumerate(error_blocks)])

    def _attach_logs_to_testcases(self):
        """Attach logs to test cases in the JUnit XML"""
        for testcase in self.root.findall('.//testcase'):
            name = testcase.get("name", "").strip()
            if name.lower() == '(main)':
                # Skip (main) test cases - they will be removed later
                continue

            # Check if this is a panic testcase we added
            is_panic_testcase = name == 'SYSTEM PANIC DETECTED'

            # Find corresponding testcase info
            testcase_info = None
            if not is_panic_testcase:
                for unique_id, info in self.testcases.items():
                    if info.name == name:
                        testcase_info = info
                        break

            #  Update system-out with URLs if we have testcase_info
            if testcase_info is not None:
                system_out = testcase.find('system-out')
                if system_out is None:
                    system_out = ETree.SubElement(testcase, 'system-out')

                    # Keep original URLs in system-out
                    urls_text = ""
                    if hasattr(testcase_info, 'sub_task_urls') and testcase_info.sub_task_urls:
                        urls_text = "\n".join(testcase_info.sub_task_urls)
                    if hasattr(testcase_info, 'task_out_urls') and testcase_info.task_out_urls:
                        if urls_text:
                            urls_text += "\n" + "\n".join(testcase_info.task_out_urls)
                        else:
                            urls_text = "\n".join(testcase_info.task_out_urls)

                    system_out.text = urls_text

            # Handle failure elements - ensure they have text
            failure_elem = testcase.find('failure')
            if failure_elem is not None and not is_panic_testcase:
                # For regular test cases, ensure failure element has text content
                if failure_elem.text is None or not failure_elem.text.strip():
                    failure_message = failure_elem.get('message', 'Test Failure')
                    failure_elem.text = failure_message

            # Handle error elements - ensure they have text
            error_elem = testcase.find('error')
            if error_elem is not None:
                # Always ensure error element has text content
                if error_elem.text is None or not error_elem.text.strip():
                    error_message = error_elem.get('message', 'Test Error')
                    error_elem.text = error_message

            # If we have testcase_info with new_block, add it to the appropriate element
            if testcase_info is not None and hasattr(testcase_info, 'new_block') and testcase_info.new_block:
                if hasattr(testcase_info, 'failure') and testcase_info.failure:
                    failure_elem = testcase.find('failure')
                    if failure_elem is not None:
                        # Append new_block to existing failure text
                        existing_text = failure_elem.text or ""
                        failure_elem.text = existing_text + "\n\n" + testcase_info.new_block if existing_text \
                            else testcase_info.new_block
                elif hasattr(testcase_info, 'error') and testcase_info.error:
                    error_elem = testcase.find('error')
                    if error_elem is not None:
                        # Append new_block to existing error text
                        existing_text = error_elem.text or ""
                        error_elem.text = existing_text + "\n\n" + testcase_info.new_block if existing_text \
                            else testcase_info.new_block
                elif not hasattr(testcase_info, 'failure') and not hasattr(testcase_info, 'error'):
                    # For non-failure/error cases, add to system-out
                    system_out = testcase.find('system-out')
                    if system_out is None:
                        system_out = ETree.SubElement(testcase, 'system-out')
                    existing_text = system_out.text or ""
                    system_out.text = existing_text + "\n\n" + testcase_info.new_block if existing_text else testcase_info.new_block

    def _clean_and_organize(self):
        """Clean and organize the JUnit XML"""
        # Remove all (main) test cases from the XML
        self._remove_main_testcases()

        self._rename_testsuite()

        # Remove any empty system-out elements
        for testcase in self.root.findall('.//testcase'):
            system_out = testcase.find('system-out')
            if system_out is not None and (system_out.text is None or not system_out.text.strip()):
                testcase.remove(system_out)

        # Update testsuite statistics after removing (main) nodes
        self._update_testsuite_stats()

        if self.debug:
            ETree.indent(self.root, space='  ')
            print('--- Final XML ---')
            print(ETree.tostring(self.root, encoding='unicode'))
            print('--- End ---')

    def _remove_main_testcases(self):
        """Remove all (main) testcase nodes from the XML"""
        main_count = 0
        # Find all testsuites
        for testsuite in self.root.findall('testsuite'):
            # Find all (main) testcases in this testsuite
            main_testcases = testsuite.findall('testcase[@name="(main)"]')
            for testcase in main_testcases:
                testsuite.remove(testcase)
                main_count += 1

        logger.info(f"Removed {main_count} (main) testcase nodes from XML")

    def _update_testsuite_stats(self):
        """Update testsuite statistics after removing (main) nodes"""
        for testsuite in self.root.findall('testsuite'):
            testcases = testsuite.findall('testcase')
            tests = len(testcases)
            failures = 0
            errors = 0
            skipped = 0

            for testcase in testcases:
                if testcase.find('failure') is not None:
                    failures += 1
                elif testcase.find('error') is not None:
                    errors += 1
                elif testcase.find('skipped') is not None:
                    skipped += 1

            # Update testsuite attributes
            testsuite.set('tests', str(tests))
            testsuite.set('failures', str(failures))
            testsuite.set('errors', str(errors))
            testsuite.set('skipped', str(skipped))

            logger.debug(
                f"Updated testsuite {testsuite.get('id')}: tests={tests}, failures={failures}, errors={errors}, skipped={skipped}")

    def process(self, session: requests.Session):
        """Main processing function"""
        # Check if we should process this job
        if not self.job_status.should_process_job():
            return False

        # Process test cases
        self.process_all_testcases(session)

        # Attach logs to test cases
        self._attach_logs_to_testcases()

        # Clean and organize XML
        self._clean_and_organize()

        return True


def clean_xml_text(text: str) -> str:
    """Remove invalid XML characters"""
    return INVALID_XML_CHARS_RE.sub('', text)


def sanitize_filename(name: str) -> str:
    """Sanitize filename for safe usage"""
    return re.sub(r'(?u)[^-\w.]', '_', name)


def create_session() -> requests.Session:
    """Create a requests session with retry configuration"""
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
    """Download text content from URL"""
    logger.debug(f"Downloading from: {download_url}")
    last_exception = None
    for attempt in range(3):
        try:
            r = session.get(download_url, timeout=(10, 30))
            r.raise_for_status()
            text = clean_xml_text(r.text)
            return text
        except Exception as error:
            logger.warning(f"Download attempt {attempt + 1} failed for {download_url}: {error}")
            last_exception = error
            if attempt < 2:
                sleep_time = 2 * (attempt + 1)
                sleep(sleep_time)

    error_msg = f"All download attempts failed for {download_url}: {last_exception}"
    logger.error(error_msg)
    raise Exception(error_msg) from last_exception


def write_xml_iteratively(root_element, output_file):
    """Write XML to file iteratively to save memory, with proper escaping of XML special characters"""
    with open(output_file, 'w', encoding='utf-8') as f:
        def write_element(element, depth=0):
            indent = "  " * depth
            tag = element.tag
            attribs = "".join(f' {k}="{v}"' for k, v in element.items())

            if len(element) == 0 and not element.text and not element.tail:
                # empty element
                f.write(f"{indent}<{tag}{attribs}/>\n")
            else:
                # Start tag
                f.write(f"{indent}<{tag}{attribs}>")

                # Text content
                if element.text:
                    # Use regular expressions to escape unescaped '&' characters.
                    text = XML_ENTITY_PATTERN.sub('&amp;', element.text)
                    # Escape other XML special characters
                    text = text.replace('<', '&lt;')
                    text = text.replace('>', '&gt;')
                    # Double quotes and single quotes do not need to be escaped in XML text; they are only required in attribute values.
                    f.write(text)

                # child elements
                if len(element) > 0:
                    f.write('\n')
                    for child in element:
                        write_element(child, depth + 1)
                    f.write(indent)

                # End tag
                f.write(f"</{tag}>\n")
        write_element(root_element)


def create_zip_with_streaming(processor, zip_file_path, job_id):
    """Create ZIP file with streaming XML writing"""
    with zipfile.ZipFile(zip_file_path, 'w', zipfile.ZIP_DEFLATED) as z:
        arcname = sanitize_filename(f"bkr-junit-{job_id}.xml")

        # First write to a temporary file, then add it to the ZIP.
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', delete=False) as tmp_xml:
            tmp_xml_path = tmp_xml.name
        try:
            write_xml_iteratively(processor.root, tmp_xml_path)
            z.write(tmp_xml_path, arcname)
        finally:
            # Clean up temporary files
            try:
                os.unlink(tmp_xml_path)
            except OSError:
                pass


def upload_to_reportportal(zip_source_path: str, session: requests.Session, processor):
    """Upload processed results to ReportPortal"""
    # Determine launch name
    if cli_args.whiteboard:
        whiteboard = processor.beaker_root.find('whiteboard')
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
    logger.info(f"Uploading ZIP file: {file_size / 1024 / 1024:.2f} MB")

    # Build attributes
    attributes = [
        {
            "key": "beaker_job_id",
            "system": False,
            "value": JOB_ID
        },
        {
            "key": "beaker_job_result",
            "system": False,
            "value": processor.job_status.job_result
        },
        {
            "key": "beaker_job_status",
            "system": False,
            "value": processor.job_status.job_status
        }
    ]

    # Add user-defined properties
    if cli_args.attributes:
        for attr in cli_args.attributes:
            try:
                if '=' in attr:
                    key, value = attr.split('=', 1)
                    key = key.strip()
                    value = value.strip()
                    if key and value:
                        attributes.append({
                            "key": key,
                            "system": False,
                            "value": value
                        })
                        logger.info(f"Added custom attribute: {key}={value}")
            except Exception as attr_error:
                logger.warning(f"Failed to parse attribute '{attr}': {attr_error}")

    # Get start time
    try:
        start_time_utc = processor.get_launch_start_time_iso()
    except Exception as time_error:
        logger.error(f"Failed to get start time from Beaker XML: {time_error}")
        sys.exit(1)

    # Build launch data
    launch_data = {
        "attributes": attributes,
        "description": f"Beaker Job {JOB_WEB_URL}\nResult: {processor.job_status.job_result}, Status: {processor.job_status.job_status}",
        "mode": "DEFAULT",
        "name": lunchname,
        "startTime": start_time_utc
    }

    logger.info(f"Launch data: {json.dumps(launch_data, indent=2)}")

    # Upload to ReportPortal
    with open(zip_source_path, 'rb') as f:
        files = {
            'file': (os.path.basename(zip_source_path), f, 'application/x-zip-compressed'),
            'launchImportRq': (
                None,
                json.dumps(launch_data),
                'application/json'
            )
        }

        logger.info(f"Uploading to ReportPortal: {rp_url}")

        try:
            resp = session.post(
                rp_url,
                headers=headers,
                files=files,
                timeout=(60, 600),
                verify=True,
                allow_redirects=True
            )

            logger.info(f"Response status code: {resp.status_code}")

            if resp.status_code != 200:
                logger.error(f"Response content: {resp.text}")
                resp.raise_for_status()

            data = resp.json()
            launch_uuid = data.get('data', {}).get('id')
            launch_message = data.get('message')
            logger.info(f"Upload successful: {launch_message}")

            # Get launch details
            get_url = f"{RP_BASE}/api/v1/{RP_PROJECT}/launch/{launch_uuid}"
            info_resp = session.get(get_url, headers=headers)
            info_resp.raise_for_status()
            info = info_resp.json()
            launch_id = info.get('id')
            logger.info(f"Launch ID: {launch_id}")

        except Exception as request_error:
            logger.error(f"Upload failed: {request_error}")
            raise


def main():
    """Main function"""
    # Set memory limits
    try:
        resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))
        logger.info(f"Set memory limit to {MEMORY_LIMIT / 1024 / 1024}MB")
    except (ValueError, resource.error) as setting_mermory_error:
        logger.warning(f"Unable to set memory limit: {setting_mermory_error}")

    # Disable bytecode caching
    sys.dont_write_bytecode = True

    # Create sessions
    session_beaker = create_session()
    session_rp = create_session()

    try:
        # Download XML files
        junit_xml = download_text(JUNIT_URL, session_beaker)

        beaker_xml = download_text(BEAKER_XML_URL, session_beaker)

    except Exception as download_error:
        logger.error(f"Failed to download XML files: {download_error}")
        sys.exit(1)

    # Process the job
    try:
        processor = BeakerJobProcessor(
            junit_xml,
            beaker_xml_source=beaker_xml,
            from_string=True,
            debug=cli_args.debug
        )
    except Exception as e:
        logger.error(f"Failed to initialize processor: {e}")
        sys.exit(1)

    # Log job status
    logger.info(f"Job Status: Result={processor.job_status.job_result}, Status={processor.job_status.job_status}")

    # Process test cases
    download_session = create_session()
    try:
        # Check if we should process this job
        if not processor.job_status.should_process_job():
            logger.info(f"Skipping Pass job {JOB_ID}. Use --force-pass to upload anyway.")
            sys.exit(0)

        # Process all test cases
        processor.process(download_session)

    except TimeoutError:
        logger.error(f"Global timeout of {GLOBAL_TIMEOUT}s exceeded")
        sys.exit(7)
    except Exception as e:
        logger.error(f"Error processing test cases: {e}")
        sys.exit(8)
    finally:
        download_session.close()

    # Create ZIP file
    logger.info("Creating ZIP file...")
    with tempfile.NamedTemporaryFile(delete=False, suffix=".zip") as tmpzip:
        zip_path = tmpzip.name

    try:
        create_zip_with_streaming(processor, zip_path, JOB_ID)
    except MemoryError:
        logger.error("Insufficient memory!")
        sys.exit(9)

    logger.info("create ZIP：%s", zip_path)
    # Check ZIP file size
    file_size_bytes = os.path.getsize(zip_path)

    file_size_mb = file_size_bytes / (1024 * 1024)
    logger.info(f"ZIP file size: {file_size_mb:.2f}MB")

    if file_size_mb > ZIP_SIZE_LIMIT / (1024 * 1024):
        logger.error(f"ZIP file size {file_size_mb:.2f}MB exceeds limit")
        sys.exit(2)
    else:
        logger.info(f"file size：{file_size_mb:.2f}MB")

    # Upload to ReportPortal
    try:
        upload_to_reportportal(zip_path, session_rp, processor)
    except Exception as e:
        logger.error(f"Failed to upload to ReportPortal: {e}")
        sys.exit(1)

    # Cleanup
    del processor
    gc.collect()

    try:
        os.remove(zip_path)
    except OSError:
        pass

    # Close sessions
    session_beaker.close()
    session_rp.close()

    if cli_args.debug:
        tracemalloc.stop()

    logger.info("Processing completed successfully!")


if __name__ == "__main__":
    main()