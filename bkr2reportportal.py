#!/usr/bin/env python3

import requests
from xml.etree import ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
import argparse
import zipfile
import re

parser = argparse.ArgumentParser()

parser.add_argument('-j', '--job', help='Beaker job id, format as J:233333 or 233333', required=True)
parser.add_argument('-u', '--url', help='Report Portal instance URL (default: %(default)s)', default='https://reportportal-rhelkernel.apps.ocp-c1.prod.psi.redhat.com')
parser.add_argument('-p', '--project', help='Report Portal project name, e.g. mshi_personal', required=True)
parser.add_argument('-t', '--token', help='Report Portal token', required=True)
parser.add_argument('-w', '--whiteboard', action='store_true', help='Use beaker whiteboard as launch name, it may fail if whiteboard is too long')

args = parser.parse_args()

BKR_JOB = args.job.strip("J:")
REPORT_PORTAL_TOKEN = args.token
INSTANCE_URL = args.url.removesuffix('/')
PROJECT_NAME = args.project
ZIP_FILE_NAME = f'/tmp/bkr-junit-{BKR_JOB}.zip'
xml_url = f"https://beaker.engineering.redhat.com/jobs/{BKR_JOB}.junit.xml"
bkr_xml = f"https://beaker.engineering.redhat.com/jobs/{BKR_JOB}.xml"
job_url = f"https://beaker.engineering.redhat.com/jobs/{BKR_JOB}"

print(f'INSTANCE_URL: {INSTANCE_URL}')
print(f'PROJECT_NAME: {PROJECT_NAME}')
# print("The original beaker junit file:", xml_url)

def download_file(url):
    response = requests.get(url)
    if response.status_code == 200:
        # Replace invalid XML characters
        content = response.text
        content = content.replace('\x08', '')
        content = content.replace('\x00', '')
        return content
    else:
        return f"Failed to download the file: {url}"

# Download beaker style xml file and get the whiteboard
response = requests.get(bkr_xml)
whiteboard = ET.fromstring(response.content).find('whiteboard').text

# Download beaker style xml file and get the whiteboard as a base junit file name:
if args.whiteboard:
    if whiteboard:
        ZIP_FILE_NAME = f'/tmp/bkr-{BKR_JOB}-{whiteboard.strip()[:100]}.zip'

# Download the junit xml file
response = requests.get(xml_url)
if response.status_code != 200:
    print(f"Failed to download the XML file: {xml_url}")
    exit(1)

root = ET.fromstring(response.text)

# Some items are shown as "(none)" or "(main)" in Report Portal, so make them more readable
for testcase in root.iter('testcase'):
    name = testcase.get('name')

    if name in ['(none)', '(main)']:
        classname = testcase.get('classname')
        testcase.set('name', f"{name} {classname}")

executor = ThreadPoolExecutor(max_workers=50)
futures = []

print("Downloading taskout.log and resultoutputfile.log files, this may take a while...")

for system_out in root.iter('system-out'):
    if system_out.text:
        lines = system_out.text.strip().split('\n')

        for i, line in enumerate(lines):
            url = line.strip()
            
            # Only download taskout.log and resultoutputfile.log
            if 'taskout.log' in url or 'resultoutputfile.log' in url:
                # Download the content in a separate thread and store the Future object
                future = executor.submit(download_file, url)
                futures.append((future, system_out, i))

# Wait for all downloads to complete and replace "system-out" elements with the content of logs
for future, system_out, i in futures:
    if system_out.text:
        lines = system_out.text.strip().split('\n')
        lines[i] = lines[i] + '\n' + future.result()
        system_out.text = '\n'.join(lines)

updated_xml_string = ET.tostring(root, encoding='utf-8').decode('utf-8')
# Remove Escape and All Control Characters (XML-safe)
# avoid the xml error: errorCode":40035,"message":"Error while importing the file.
# Error during parsing the xml file: \'An invalid XML character (Unicode: 0x1b) was
# found in the element content of the document.
cleaned_xml_string = re.sub(r'[\x00-\x08\x0B\x0C\x0E-\x1F]', '', updated_xml_string)
updated_xml_string = cleaned_xml_string

with zipfile.ZipFile(ZIP_FILE_NAME, 'w', zipfile.ZIP_DEFLATED) as myzip:
    with myzip.open(f'bkr-junit-{BKR_JOB}.xml', 'w') as myfile:
        myfile.write(updated_xml_string.encode())

# Upload the zip file to Report Portal
import_url = f"{INSTANCE_URL}/api/v1/{PROJECT_NAME}/launch/import"
headers = {
    # 'Content-Type': 'multipart/form-data',
    'Authorization': f'bearer {REPORT_PORTAL_TOKEN}',
    'accept': '*/*',
}

with open(ZIP_FILE_NAME, 'rb') as f:
    files = {'file': f}
    print(f"Uploading '{ZIP_FILE_NAME}' to Report Portal...")
    response = requests.post(import_url, headers=headers, files=files)

print(response.content)
if response.status_code == 200:
    print(f"Done, see the result in {INSTANCE_URL}/ui/#{PROJECT_NAME}/launches/all")
    msg = response.text
    uuid = re.search(r'([a-zA-Z0-9]+-)+[a-zA-Z0-9]+', msg).group(0)
    get_url = f"{INSTANCE_URL}/api/v1/{PROJECT_NAME}/launch/uuid/{uuid}"
    res = requests.get(get_url, headers=headers)
    launch_data = res.json()
    update_url = f"{INSTANCE_URL}/api/v1/{PROJECT_NAME}/launch/{launch_data['id']}/update"
    update_data = {
        # "attributes": [
        #     {
        #         "key": "mykey",
        #         "value": "myvalue"
        #     }
        # ],
        "description": f"{job_url}\n{whiteboard}",
        # "mode": "DEFAULT"
    }
    res = requests.put(update_url, headers=headers, json=update_data)

else:
    if response.status_code == 400:
        print("Please make sure your beaker job is finished.")
    exit(1)
