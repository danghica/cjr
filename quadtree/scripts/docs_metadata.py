#!/usr/bin/env python3
from common import ROOT,hashes,write_json
style=ROOT/'docs/rocq/style.css'
css='''\n/* Keep long proof-free syntax inside its own scroll area on narrow screens. */
main, article { min-width: 0; box-sizing: border-box; }
article { max-width: 100%; overflow-x: hidden; }
pre { min-width: 0; max-width: 100%; box-sizing: border-box; }
'''
current=style.read_text()
if 'Keep long proof-free syntax inside its own scroll area' not in current:
    style.write_text(current+css)
write_json(ROOT/'docs/metadata.json',{'sources':hashes(),'renderer':'rocq_readable; coq-lsp AST backend'})
