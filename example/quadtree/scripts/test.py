#!/usr/bin/env python3
import subprocess, sys, re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT.parents[1]))
from tools.project_tools.support import toolchain,metadata,write_json
cjc,env,version=toolchain(ROOT)
results=ROOT/'test/results';results.mkdir(exist_ok=True)
binary=results/'quadtree-tests'
flags=['--test','-O2']
r=subprocess.run([str(cjc),*flags,str(ROOT/'extracted/quadtree.cj'),str(ROOT/'test/quadtree_test.cj'),'-o',str(binary)],env=env,text=True,capture_output=True)
(results/'compile.log').write_text(r.stdout+r.stderr)
if r.returncode:
    write_json(results/'report.json',metadata(ROOT,version,flags)|{'status':'failed','exit_status':r.returncode,'cases':[],'stdout':r.stdout,'stderr':r.stderr})
    print(r.stdout+r.stderr);sys.exit(r.returncode)
r=subprocess.run([str(binary),'--no-progress','--no-color'],env=env,text=True,capture_output=True)
(results/'execution.log').write_text(r.stdout+r.stderr)
passed=re.findall(r'\[\s*PASSED\s*\]\s+CASE:\s+(\w+)',r.stdout)
expected=['emptyAndUnit','boundsQuadrantsAndRectangles','insertionAlgebra','unionDistribution','seededSequencesAndPermutations']
status=r.returncode or (0 if sorted(passed)==sorted(expected) else 1)
write_json(results/'report.json',metadata(ROOT,version,flags)|{'status':'passed' if status==0 else 'failed','exit_status':status,'stdout':r.stdout,'stderr':r.stderr,'seed':20261010,'random_operations':4000,'pair_orders':36,'insertion_permutations':4,'cases':passed})
print(r.stdout+r.stderr);sys.exit(status)
