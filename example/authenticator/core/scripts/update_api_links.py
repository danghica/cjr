#!/usr/bin/env python3
"""Refresh API implementation-proof links against checked Rocq-readable pages."""
import hashlib
import html
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[4]
CORE = ROOT / 'example/authenticator/core'
DOCS = ROOT / 'example/authenticator/docs'
sys.path.insert(0, str(ROOT))
from tools.rocq_readable.layout import anchor


def main():
    manifest_path = CORE / 'contracts.json'
    manifest = json.loads(manifest_path.read_text())
    required = {name: theorem for group in ('application_port', 'library_operations', 'internal_helpers')
                for name, theorem in manifest[group].items()}
    sources = sorted((CORE / 'rocq').glob('*.v'))
    fingerprints = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    report = json.loads((ROOT / 'example/authenticator/build/proof-report.json').read_text())
    if (report['status'] != 'passed' or report['sources'] != fingerprints or
            report.get('contract_manifest_sha256') != hashlib.sha256(manifest_path.read_bytes()).hexdigest()):
        raise RuntimeError('API proof links require a passing audit of the current core sources and export manifest')
    bodies = {}
    for emitted in re.finditer(r'\bFn "(\w+)"[^;\n]*', (CORE / 'rocq/extract.v').read_text()):
        bodies[emitted[1]] = re.search(r'\b(?:program\.)?(\w+_body)\b', emitted[0])[1]
    declarations = []
    for source in sources:
        for match in re.finditer(r'^(?:(?:Local|Global)\s+)?(?:Lemma|Theorem|Example|Corollary|Fact|Proposition)\s+(\w+)\b(.*?)\bProof\b', source.read_text(), re.M | re.S):
            declarations.append((source.stem + '.' + match[1], match[2]))
    def link(theorem):
        module, name = theorem.split('.')
        fragment = anchor('cjr.authenticator.' + theorem)
        page = DOCS / 'rocq/example/authenticator/core/rocq' / (module + '.html')
        if not page.exists() or f'id="{fragment}"' not in page.read_text():
            raise RuntimeError('Missing generated Rocq-readable target: ' + theorem)
        return f'<a href="rocq/example/authenticator/core/rocq/{module}.html#{fragment}"><code>{html.escape(theorem)}</code></a>'
    document = (DOCS / 'index.html').read_text()
    for function, theorem in required.items():
        article = re.search(r'<article id="' + re.escape(function) + r'">.*?</article>', document, re.S)
        if not article:
            raise RuntimeError('Missing API function: ' + function)
        direct = [name for name, statement in declarations
                  if name != theorem and re.search(r'\b' + re.escape(bodies[function]) + r'\b', statement)]
        replacement = '<p><strong>Implementation contract:</strong> ' + link(theorem) + '.</p>'
        if direct:
            replacement += '<details><summary>Other lemmas mentioning this CJR body</summary><p>'
            replacement += ', '.join(link(name) for name in direct) + '.</p></details>'
        updated, count = re.subn(r'<p><strong>Implementation (?:lemmas|contract):</strong>.*?</p>(?:<details><summary>Other lemmas mentioning this CJR body</summary>.*?</details>)?', replacement, article[0], count=1, flags=re.S)
        if count != 1:
            raise RuntimeError('Missing implementation proof section: ' + function)
        document = document[:article.start()] + updated + document[article.end():]
    document = document.replace('<strong>Proof coverage is partial. Milestone 2 remains incomplete.</strong>', '<strong>Core implementation contracts are checked.</strong>')
    document = document.replace('Direct implementation links point to lemmas mentioning the CJR body used to generate the function. Related links concern pure models, examples, or component rules and do not establish full correctness of the heap-based implementation.', 'Each implementation contract is checked against the extracted CJR body and its calling preconditions. The complete core audit covers all exported functions; related model and component links provide supporting results. Compiler/runtime and extraction remain trusted boundaries.')
    document = document.replace('Full heap-routine refinement and whole-program Int64 correspondence are still outstanding.', 'Heap refinements and reachable-state Int64 bounds are checked. Formal compiler correctness is outside the proof boundary.')
    document = document.replace(' Full heap-loop refinement is outstanding.', '')
    document = document.replace('These concrete failure-atomicity properties are runtime-tested, not yet fully refined in Iris.', 'Failure atomicity and temporary cleanup are established by the linked implementation contracts.')
    document = document.replace('Round index; intended SHA-1 use is 0..79. The helper performs no range check.', 'Round index; required range is 0..79. The helper performs no range check.')
    document = document.replace('The current 32-bit schedule word, in 0..4294967295 for intended machine execution.', 'The current 32-bit schedule word; required range is 0..4294967295.')
    (DOCS / 'index.html').write_text(document)
    print(f'Updated checked implementation links for {len(required)} API functions.')


if __name__ == '__main__':
    main()
