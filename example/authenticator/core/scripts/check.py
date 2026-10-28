#!/usr/bin/env python3
"""Extract the actual CJR terms and test compiled code against independent Python oracles."""
import argparse
import base64
import hashlib
import hmac
import json
import os
from pathlib import Path
import random
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
PROJECT = ROOT / 'example/authenticator/core'
sys.path.insert(0, str(ROOT))
from tools.project_tools.examples import coq_flags
from tools.project_tools.support import toolchain


def extract():
    coqtop = os.environ.get('COQTOP', str(Path.home() / '.opam/default/bin/coqtop'))
    query = ('From Coq Require Import String.\n'
             'From cjr.authenticator Require Import extract.\n'
             'Open Scope string_scope.\nEval vm_compute in authenticator_cj.\n')
    proc = subprocess.run([coqtop, '-quiet', *coq_flags()], cwd=ROOT,
                          input=query, text=True, capture_output=True, check=True)
    match = re.search(r'=\s*"(.*)"(?:%string)?\s*:\s*string', proc.stdout, re.S)
    if not match or 'Error:' in proc.stderr:
        raise RuntimeError(proc.stdout + proc.stderr)
    code = match.group(1).replace('""', '"')
    if 'unsupported' in code:
        raise RuntimeError('Unsupported CJR extraction form')
    (PROJECT / 'extracted/authenticator.cj').write_text(code)


def array(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def vectors():
    rng = random.Random(6238)
    rows = []
    for n in [0, 1, 3, 55, 56, 63, 64, 65, 119, 120, 127, 128, 1024, 2048]:
        data = bytes(rng.randrange(256) for _ in range(n))
        rows.append(f'        checkSha({array(data)}, {array(hashlib.sha1(data).digest())})')
    rows.append(f'        checkSha([97, 98, 99], {array(hashlib.sha1(b"abc").digest())})')
    for klen in [1, 20, 63, 64, 65, 80, 128]:
        for mlen in [0, 8, 55, 56, 64, 1024]:
            key = bytes(rng.randrange(256) for _ in range(klen))
            msg = bytes(rng.randrange(256) for _ in range(mlen))
            expected = hmac.digest(key, msg, 'sha1')
            rows.append(f'        checkHmac({array(key)}, {array(msg)}, {array(expected)})')
    for key_start, key_len, msg_start, msg_len in [(0, 20, 0, 20), (0, 80, 16, 64), (32, 32, 0, 64)]:
        shared = bytes(rng.randrange(256) for _ in range(96))
        expected = hmac.digest(shared[key_start:key_start+key_len], shared[msg_start:msg_start+msg_len], 'sha1')
        rows.append(f'        checkAliasedHmac({array(shared)}, {key_start}, {key_len}, {msg_start}, {msg_len}, {array(expected)})')
    key = b'12345678901234567890'
    for t, expected in [(59,94287082),(1111111109,7081804),(1111111111,14050471),
                        (1234567890,89005924),(2000000000,69279037),(20000000000,65353130)]:
        rows.append(f'        @Expect(authTotp(key, 20, {t}, 30, 8), {expected})')
    for i, expected in enumerate([755224,287082,359152,969429,338314,254676,287922,162583,399871,520489]):
        rows.append(f'        @Expect(authHotp(key, 20, {i}, 6), {expected})')
    for i in range(50):
        t = rng.choice([0,29,30,31,59,60,9223372036854775807,rng.randrange(10**12)])
        period = rng.choice([1,30,60,2147483647])
        digits = rng.choice([6,8])
        digest = hmac.digest(key, (t//period).to_bytes(8,'big'), 'sha1')
        off = digest[-1] & 15
        expected = (int.from_bytes(digest[off:off+4],'big') & 0x7fffffff) % 10**digits
        rows.append(f'        @Expect(authTotp(key, 20, {t}, {period}, {digits}), {expected})')
        rows.append(f'        @Expect(authRemaining({t}, {period}), {period-t%period})')
    for n in [1,2,3,4,5,6,20,63,64,127,128]:
        data = bytes(rng.randrange(256) for _ in range(n))
        encoded = base64.b32encode(data)
        for variant in [encoded,encoded.rstrip(b'='),encoded.lower()]:
            rows.append(f'        checkBase32({array(variant)}, {array(data)})')
    return '''@Test
class OracleTests {
    @TestCase
    func independentVectors(): Unit {
        let key = allocWords(20)
        fillWords(key, [49,50,51,52,53,54,55,56,57,48,49,50,51,52,53,54,55,56,57,48])
''' + '\n'.join(rows) + '''
        releaseWords(key)
    }
}
'''


def run_tests():
    cjc, env, version = toolchain(PROJECT)
    build = ROOT / 'example/authenticator/build'
    build.mkdir(parents=True, exist_ok=True)
    oracle = build / 'oracle_test.cj'
    oracle.write_text(vectors())
    binary = build / 'core-tests'
    command = [str(cjc),'--test','-O2',str(PROJECT/'extracted/authenticator.cj'),
               str(PROJECT/'test/authenticator_test.cj'),str(oracle),'-o',str(binary)]
    compiled = subprocess.run(command, env=env, text=True, capture_output=True)
    (build/'compile.log').write_text(compiled.stdout+compiled.stderr)
    if compiled.returncode:
        print(compiled.stdout+compiled.stderr)
        raise RuntimeError('Cangjie compilation failed')
    proc = subprocess.run([str(binary),'--no-progress','--no-color'], env=env, text=True, capture_output=True)
    output = proc.stdout+proc.stderr
    (build/'execution.log').write_text(output)
    passed = re.findall(r'\[\s*PASSED\s*\]\s+CASE:\s+(\w+)',output)
    expected = sum(len(re.findall(r'@TestCase\b', p.read_text()))
                   for p in [PROJECT/'test/authenticator_test.cj',oracle])
    report = {'status':'passed' if proc.returncode==0 and len(passed)==expected else 'failed',
              'compiler':version,'cases':passed,'expected_cases':expected,
              'source_sha256':hashlib.sha256((PROJECT/'extracted/authenticator.cj').read_bytes()).hexdigest(),
              'oracle':'Python hashlib/hmac/base64 and RFC 4226/6238 fixtures'}
    (build/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(output)
    if report['status']!='passed':
        raise RuntimeError('Runtime tests failed')

if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument('--extract-only',action='store_true')
    modes.add_argument('--test-only',action='store_true')
    args=parser.parse_args()
    if not args.test_only:
        extract()
    if not args.extract_only:
        run_tests()
