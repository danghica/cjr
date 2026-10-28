#!/usr/bin/env python3
"""Build and exercise both real adapters; record source-fingerprinted evidence."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import frontends


def main():
    report_path=frontends.APP/'build/frontend-report.json'
    passed=False
    try:
        frontends.cli()
        frontends.ui()  # Compiles SwiftUI and runs Swift/C/Cangjie integration.
        subprocess.run(['python3',str(frontends.APP/'cli/test/check.py')],
                       cwd=frontends.ROOT,check=True)
        passed=True
    finally:
        files=[p for folder in ('cli','ui','scripts','test')
               for p in (frontends.APP/folder).rglob('*')
               if p.suffix in ('.cj','.swift','.c','.h','.py','.json')]
        report={
            'status':'passed' if passed else 'failed',
            'recorded_at':datetime.now(timezone.utc).isoformat(),
            'checks':['Cangjie CLI build and interactive integration',
                      'SwiftUI development bundle build',
                      'Swift to C to Cangjie real-core integration',
                      'Shared URI fixtures: 5 accepted / 18 rejected',
                      'RFC vectors, leading zeroes, defaults and time boundaries',
                      'Session isolation, rejection, capacity, rename/remove, lifetime',
                      'FFI output capacity rejection'],
            'visual_interaction':'not validated: desktop automation timed out',
            'core_extraction_sha256':hashlib.sha256((frontends.APP/'core/extracted/authenticator.cj').read_bytes()).hexdigest(),
            'sources':{str(p.relative_to(frontends.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
        }
        report_path.write_text(json.dumps(report,indent=2)+'\n')
    print('Frontend acceptance passed; report:',report_path)

if __name__=='__main__':
    main()
