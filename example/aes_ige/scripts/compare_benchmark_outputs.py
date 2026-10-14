#!/usr/bin/env python3
"""Compare every output byte and final IV for all timed throughput workloads."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT.parents[1]))
from tools.project_tools.support import toolchain
from build_openssl_benchmark import build

def records(output):
    return [line[line.index('VERIFY,'):] for line in output.splitlines() if 'VERIFY,' in line]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark-binary", type=Path)
    args=parser.parse_args()
    cjc, env, version = toolchain(ROOT)
    with tempfile.TemporaryDirectory(prefix='aes-ige-differential-') as scratch:
        c=Path(scratch)/'openssl'; cj=Path(scratch)/'cangjie'
        provenance=build(c)
        subprocess.run([str(cjc),str(ROOT/'extracted/aes_ige.cj'),
                        str(ROOT/'benchmark/differential.cj'),'--test','-O2','-o',str(cj)],
                       env=env,check=True,timeout=900,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        expected=records(subprocess.check_output([str(c),'--verify'],text=True,timeout=120))
        actual=records(subprocess.check_output([str(cj)],env=env,text=True,timeout=120))
        if actual != expected:
            raise RuntimeError(f'Full-byte differential comparison failed: {len(actual)} vs {len(expected)} records; first difference '+str(next(((a,b) for a,b in zip(actual,expected) if a!=b), None)))
        assert len(actual)==25002, len(actual)
        data=dict(status='passed',date_utc=datetime.now(timezone.utc).isoformat(),
                  workloads=18, records=len(actual), compared_bytes=len(actual)*16,
                  coverage='Complete encryption/decryption outputs and 32-byte final IVs, all key sizes and message sizes',
                  compiler=version,library=provenance['library'],library_sha256=provenance['library_sha256'],
                  output_sha256=hashlib.sha256(('\n'.join(actual)+'\n').encode()).hexdigest())
        (ROOT/'benchmark/results/differential.json').write_text(json.dumps(data,indent=2)+'\n')
        print(f"Compared {data['compared_bytes']} bytes across 18 workloads, including final IVs")
    if args.benchmark_binary:
        subprocess.run([str(cjc),str(ROOT/'extracted/aes_ige.cj'),
                        str(ROOT.parents[1]/'tools/project_tools/benchmark_common.cj'),
                        str(ROOT/'benchmark/aes_ige_bench.cj'),'--test','-O2','-o',str(args.benchmark_binary)],
                       env=env,check=True,timeout=900)
if __name__=='__main__': main()
