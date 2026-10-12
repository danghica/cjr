#!/usr/bin/env python3
"""Reproducible syntax-directed extraction, with no postprocessing of code."""
import pathlib, subprocess, re, os, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT.parents[1]))
from tools.project_tools.examples import coq_flags
from tools.project_tools.support import hashes,write_json
COQC = os.environ.get('COQC', '/Users/danghica/.opam/default/bin/coqc')
FLAGS = coq_flags()
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
    write_json(out/'metadata.json',{'method':'vm_compute shared print_prog; Coq string decoding only','sources': hashes(ROOT),'files':['quadtree.cj']})
if __name__=='__main__': main()
