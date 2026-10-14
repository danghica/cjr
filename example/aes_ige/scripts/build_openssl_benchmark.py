#!/usr/bin/env python3
"""Build the native comparator and record the actual toolchain/library."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
def build(binary):
    prefix = os.environ.get('OPENSSL_PREFIX')
    if not prefix:
        prefix = subprocess.check_output(['brew', '--prefix', 'openssl@3'], text=True).strip()
    prefix = Path(prefix).resolve()
    cc = shutil.which(os.environ.get('CC', 'cc'))
    if not cc:
        raise RuntimeError('C compiler not found; set CC')
    library = prefix / 'lib' / ('libcrypto.dylib' if sys.platform == 'darwin' else 'libcrypto.so')
    command = [cc, '-std=c11', '-D_POSIX_C_SOURCE=200809L', '-O2', '-Wall', '-Wextra',
               '-I'+str(prefix/'include'), str(ROOT/'benchmark/openssl_ige_bench.c'),
               str(library), '-Wl,-rpath,'+str(prefix/'lib'), '-o', str(binary)]
    environment=os.environ.copy()
    if sys.platform == 'darwin':
        environment.pop('SDKROOT', None)
        environment['SDKROOT']=subprocess.check_output(['xcrun','--show-sdk-path'],env=environment,text=True).strip()
    subprocess.run(command, env=environment, check=True)
    data = dict(compiler=subprocess.check_output([cc,'--version'], text=True).strip(),
                compile_command=command, library=str(library.resolve()),
                library_sha256=hashlib.sha256(library.read_bytes()).hexdigest(),
                openssl=subprocess.check_output([str(prefix/'bin/openssl'),'version','-a'],text=True).strip(),
                api='AES_ige_encrypt; AES_set_encrypt_key; AES_set_decrypt_key',
                acceleration='Default library dispatch; no capability overrides. Hardware instruction use has not been separately established.',
                capabilities_environment={k:v for k,v in os.environ.items() if k.startswith('OPENSSL_')})
    output = ROOT/'benchmark/results/openssl-metadata.json'
    output.write_text(json.dumps(data,indent=2)+'\n')
    return data
if __name__ == '__main__':
    build(Path(sys.argv[1]))
