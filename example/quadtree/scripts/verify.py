#!/usr/bin/env python3
"""Kernel-check all local modules and audit every local lemma/theorem."""
import subprocess,os,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT.parents[1]))
from tools.project_tools.examples import coq_flags
from tools.project_tools.support import write_json,hashes
coqc=os.environ.get('COQC',str(__import__('pathlib').Path.home()/'.opam/default/bin/coqc'))
coqchk=os.environ.get('COQCHK',str(__import__('pathlib').Path.home()/'.opam/default/bin/coqchk'))
flags=coq_flags()
files=sorted(ROOT.rglob('*.v'));modules=[];audit=[]
for p in files:
    if p.name=='audit.v':continue
    text=p.read_text()
    if re.search(r'\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b',text):raise RuntimeError('Forbidden proof escape in '+str(p))
    module='cjr.quadtree.'+'.'.join(p.relative_to(ROOT).with_suffix('').parts);modules.append(module)
    audit.append('Require Import '+module+'.')
    for name in re.findall(r'^\s*(?:Lemma|Theorem|Corollary)\s+([\w]+)',text,re.M):audit.append('Print Assumptions '+module+'.'+name+'.')
results=ROOT/'proof/results';results.mkdir(exist_ok=True)
auditfile=ROOT/'proof/audit.v';auditfile.write_text('\n'.join(audit)+'\n')
write_json(results/'verification.json',{'status':'failed','sources':hashes(ROOT),'reason':'verification has not completed'})
r=subprocess.run([coqchk,'-silent',*flags,*modules],text=True,capture_output=True)
(results/'coqchk.log').write_text('Command: '+ ' '.join([coqchk,'-silent',*flags,*modules])+'\nExit status: '+str(r.returncode)+'\n'+r.stdout+r.stderr)
if r.returncode:print((r.stdout+r.stderr)[-5000:]);sys.exit(r.returncode)
r=subprocess.run([coqc,*flags,str(auditfile)],text=True,capture_output=True)
(results/'assumptions.log').write_text(r.stdout+r.stderr)
if r.returncode or 'Axioms:' in r.stdout+r.stderr:print(r.stdout+r.stderr);sys.exit(1)
count=sum(line.startswith('Print Assumptions') for line in audit)
if r.stdout.count('Closed under the global context')!=count:raise RuntimeError('Incomplete assumption audit')
write_json(results/'verification.json',{'status':'passed','coqchk':'passed','assumptions':'closed under the global context','audited_declarations':count,'sources':hashes(ROOT),'contract_coverage':'Iris contracts cover make, insertion, membership and range; rejected/duplicate insertions and all queries preserve the original structural witness. Concrete composition theorems establish insertion commutativity/idempotence, repeated queries and range distribution over specification-level union.'})
print(f'coqchk passed; {count} declarations closed under the global context')
