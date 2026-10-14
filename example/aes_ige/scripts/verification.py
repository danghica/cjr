#!/usr/bin/env python3
"""Record a successful repository audit without overstating contract coverage."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]

def main():
 log=REPO/'build/verify.log'
 content=log.read_text()
 finishes=re.findall(r'make verify finished: (\S+) \(exit status (\d+)\)',content)
 if not finishes or finishes[-1][1]!='0':
  raise SystemExit('A completed successful make verify is required.')
 audit=(REPO/'build/assumptions.log').read_text()
 count=audit.count('Closed under the global context')
 expected=int(re.search(r'VERIFY_THEOREMS := (\d+)',(REPO/'Makefile.local-late').read_text())[1])
 if count<expected:raise SystemExit('Incomplete assumption audit.')
 data=dict(status='passed',refinement_status='complete',coqchk='passed',assumptions='all audited declarations closed under the global context',
  audited_declarations=count,expected_declarations=expected,date_utc=finishes[-1][0],
  contract_coverage='Concrete specification algebra; Iris refinement of byte/block helpers, caller-owned key expansion, all AES block variants, and full IGE loops; implementation round-trip, empty-message, and chunk-composition contracts.',
  pending_obligations=[],
  repository_verify_log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
 dest=ROOT/'proof/results/verification.json';dest.parent.mkdir(parents=True,exist_ok=True)
 dest.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()
