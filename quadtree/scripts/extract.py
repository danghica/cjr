#!/usr/bin/env python3
"""Reproducible syntax-directed extraction, with no postprocessing of code."""
import pathlib, subprocess, re, json, hashlib, os
ROOT = pathlib.Path(__file__).resolve().parents[1]
COQC = os.environ.get('COQC', '/Users/danghica/.opam/default/bin/coqc')
FLAGS = ['-R', str(ROOT.parent/'theories'), 'cjr', '-Q', str(ROOT), 'cjr.quadtree']
def hashes():
    paths = sorted(ROOT.rglob('*.v')) + [ROOT.parent/'theories/examples/cj_print.v', ROOT.parent/'theories/lang.v']
    return {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else '../'+str(p.relative_to(ROOT.parent)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
def main():
    out = ROOT/'extracted'; out.mkdir(exist_ok=True)
    probe = ROOT/'algorithm/print.v'
    probe.write_text('From Coq Require Import String.\nLocal Open Scope string_scope.\nFrom cjr.quadtree.algorithm Require Import extract.\nFrom cjr.examples Require Import cj_print.\nEval vm_compute in print_prog quadtree_program.\n')
    try:
        r = subprocess.run([COQC, *FLAGS, str(probe)], text=True, capture_output=True, check=True)
        m = re.fullmatch(r'\s*=\s*"(.*)"\s*:\s*string\s*', r.stdout, re.S)
        if not m: raise RuntimeError('Unexpected Coq string output: '+r.stdout[:200])
        code=m.group(1).replace('""','"')
        (out/'quadtree.cj').write_text(code+'\n')
    finally:
        for p in probe.parent.glob('print.*'):
            if p.suffix in {'.v','.vo','.vos','.vok','.glob'}: p.unlink()
        hidden=probe.parent/'.print.aux'
        if hidden.exists(): hidden.unlink()
    (out/'metadata.json').write_text(json.dumps({'method':'vm_compute shared print_prog; Coq string decoding only','sources': hashes(),'files':['quadtree.cj']},indent=2,sort_keys=True)+'\n')
if __name__=='__main__': main()
