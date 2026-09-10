#!/usr/bin/env python3
"""Fail on common credential patterns, without printing matching values."""
import re
import subprocess
from pathlib import Path

patterns = [
    rb'gh[pousr]_[A-Za-z0-9]{30,}',
    rb'github_pat_[A-Za-z0-9_]{40,}',
    rb'AKIA[0-9A-Z]{16}',
    rb'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----',
    rb'sk-(?:proj-)?[A-Za-z0-9_-]{40,}',
]
paths = subprocess.check_output(['git', 'ls-files', '-z']).split(b'\0')
findings = []
for raw in paths:
    if not raw:
        continue
    path = Path(raw.decode('utf-8'))
    if path.is_symlink():
        raise SystemExit('Publication source contains a symlink: ' + str(path))
    if any(re.search(pattern, path.read_bytes()) for pattern in patterns):
        findings.append(str(path))
if findings:
    raise SystemExit('Potential credentials; inspect these files privately:\n' + '\n'.join(findings))
print('No common credential patterns detected in tracked files.')
