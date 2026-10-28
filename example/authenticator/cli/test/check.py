#!/usr/bin/env python3
"""Drive the real interactive executable, never an OTP mock."""
import json
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT))
from tools.project_tools.support import toolchain
_,env,_=toolchain(ROOT/'example/authenticator/core')
binary=ROOT/'example/authenticator/build/frontend/authenticator'
fixtures=json.loads((ROOT/'example/authenticator/test/uri-fixtures.json').read_text())
def run(script):
    p=subprocess.run([str(binary)],input=script,text=True,capture_output=True,env=env,timeout=20)
    assert p.returncode==0,p.stderr
    assert 'GEZDGNBV' not in p.stdout and 'MY====' not in p.stdout,p.stdout
    return p.stdout
for uri in fixtures['valid']:
    output=run('uri\n'+uri+'\nlist\nquit\n')
    assert 'Added account 1.' in output,output
for uri in fixtures['invalid']:
    output=run('uri\n'+uri+'\nlist\nquit\n')
    assert 'Added account' not in output and 'No accounts.' in output,(uri,output)
output=run('help\nhelp code\nadd\nalice\nExample\nGEZDGNBVGY3TQOJQGEZDGNBVGY3TQOJQ\n8\n30\ncode 1 59\ncode 1 1111111109\nrename 1\nAlice renamed\nExample\nlist\nremove 1\ncode 1 59\nlist\nquit\n')
for expected in ['Commands:', 'Example: code 1 59', '94287082 | 1s remaining', '07081804 | 1s remaining','Alice renamed','Removed.','No accounts.']:
    assert expected in output,(expected,output)
output=run('add\nalice\n\nGEZDGNBVGY3TQOJQGEZDGNBVGY3TQOJQ\n\n\ncode 1 29\ncode 1 30\nquit\n')
assert '755224 | 1s remaining' in output and '287082 | 30s remaining' in output,output
assert 'No accounts.' in run('list\n')
assert 'Invalid command' in run('authSha1\nquit\n')
print(f'CLI passed: {len(fixtures["valid"])} valid / {len(fixtures["invalid"])} rejected URIs; help, RFC codes, rename/remove, EOF and fresh session.')
