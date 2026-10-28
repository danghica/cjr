#!/usr/bin/env python3
"""Check every authenticator proof object and audit every declared theorem."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
CORE = ROOT / 'example/authenticator/core'
sys.path.insert(0, str(ROOT))
from tools.project_tools.examples import coq_flags


def main():
    sources = sorted((CORE / 'rocq').glob('*.v'))
    for source in sources:
        compiled = source.with_suffix('.vo')
        if not compiled.is_file() or compiled.stat().st_mtime_ns < source.stat().st_mtime_ns:
            raise RuntimeError(f'Stale or missing proof object for {source.relative_to(ROOT)}; run make proofs')
    modules = ['cjr.authenticator.' + source.stem for source in sources]
    declarations = []
    for source in sources:
        text = source.read_text()
        if re.search(r'\b(?:Admitted|Abort)\s*\.|^\s*(?:(?:Local|Global)\s+)?Axioms?\s', text, re.M):
            raise RuntimeError(f'Incomplete or axiomatic proof in {source.relative_to(ROOT)}')
        declarations.extend('cjr.authenticator.' + source.stem + '.' + name
                            for name in re.findall(r'^(?:(?:Local|Global)\s+)?(?:Lemma|Theorem|Example|Corollary|Fact|Proposition)\s+(\w+)', text, re.M))
    manifest_path = CORE / 'contracts.json'
    manifest = json.loads(manifest_path.read_text())
    contracts = {name: 'cjr.authenticator.' + theorem
                 for group in ('application_port', 'library_operations', 'internal_helpers')
                 for name, theorem in manifest[group].items()}
    emitted = set(re.findall(r'\bFn\s+"([^"]+)"', (CORE / 'rocq/extract.v').read_text()))
    if set(contracts) != emitted:
        raise RuntimeError('Exported functions and core/contracts.json do not match')
    missing = sorted(set(contracts.values()) - set(declarations))
    if missing:
        raise RuntimeError('Missing exported implementation contracts: ' + ', '.join(missing))
    output = ROOT / 'example/authenticator/build'
    output.mkdir(parents=True, exist_ok=True)
    opam = Path.home() / '.opam/default/bin'
    checker = os.environ.get('COQCHK', str(opam / 'coqchk'))
    top = os.environ.get('COQTOP', str(opam / 'coqtop'))
    query = ''.join('Require Import ' + module + '.\n' for module in modules)
    query += ''.join('Print Assumptions ' + name + '.\n' for name in declarations)
    with ThreadPoolExecutor(max_workers=2) as checks:
        checked_future = checks.submit(subprocess.run,
            [checker, '-silent', *coq_flags(), *modules], cwd=ROOT,
            text=True, capture_output=True)
        audit_future = checks.submit(subprocess.run,
            [top, '-quiet', *coq_flags()], cwd=ROOT, input=query,
            text=True, capture_output=True)
        checked, audit = checked_future.result(), audit_future.result()
    (output / 'proof-check.log').write_text(checked.stdout + checked.stderr)
    audit_text = audit.stdout + audit.stderr
    (output / 'proof-assumptions.log').write_text(audit_text)
    closed = audit_text.count('Closed under the global context')
    passed = (checked.returncode == audit.returncode == 0 and closed == len(declarations)
              and not re.search(r'\bError:|^Axioms:', audit_text, re.M))
    report = dict(status='passed' if passed else 'failed', coverage='listed_export_contracts',
                  contracts=contracts, trusted_boundary=manifest['trusted_boundary'],
                  contract_manifest_sha256=hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
                  remaining_obligations='example/authenticator/docs/proof-status.html', modules=modules,
                  declarations=declarations, expected_closed=len(declarations), closed=closed,
                  sources={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in sources})
    (output / 'proof-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Core coqchk: {checked.returncode}; assumptions: {closed}/{len(declarations)} closed.')
    if not passed:
        raise RuntimeError('Core proof verification failed; see example/authenticator/build/proof-*.log')


if __name__ == '__main__':
    main()
