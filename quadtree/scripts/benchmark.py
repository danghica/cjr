#!/usr/bin/env python3
import subprocess,sys,csv,collections,statistics,math,re
from common import ROOT,toolchain,metadata,write_json
cjc,env,version=toolchain();results=ROOT/'benchmark/results';results.mkdir(exist_ok=True)
binary=results/'quadtree-benchmark';flags=['--test','-O2']
# Include oracle utilities; the test class is excluded by the test runner filter.
cmd=[str(cjc),*flags,*map(str,[ROOT/'extracted/quadtree.cj',ROOT/'test/quadtree_test.cj',ROOT/'benchmark/native.cj',ROOT/'benchmark/bench.cj']),'-o',str(binary)]
r=subprocess.run(cmd,env=env,text=True,capture_output=True);(results/'compile.log').write_text(r.stdout+r.stderr)
if r.returncode:
    write_json(results/'metadata.json',metadata(version,flags)|{'status':'failed','exit_status':r.returncode})
    print(r.stdout+r.stderr);sys.exit(r.returncode)
rows=[]
for process in range(3):
    e=env|{'QT_PROCESS':str(process)}
    r=subprocess.run([str(binary),'--filter=QuadtreeBenchmark.*','--no-progress','--no-color'],env=e,text=True,capture_output=True)
    (results/f'process-{process}.log').write_text(r.stdout+r.stderr)
    if r.returncode: print(r.stdout+r.stderr);sys.exit(r.returncode)
    for line in re.findall(r"BENCH,[^\r\n\x1b]+",r.stdout):
        if line.startswith('BENCH,'):
            dist,n,work,impl,trial,reps,ns,ops,check=line.split(',')[1:]
            rows.append(dict(process=process,distribution=dist,n=int(n),workload=work,implementation=impl,trial=int(trial),repetitions=int(reps),nanoseconds=int(ns),operations=int(ops),checksum=int(check),ns_per_operation=int(ns)/int(ops)))
    print(f'process {process+1}/3 complete: {len(rows)} samples',flush=True)
if len(rows)!=3*3*3*7*3*7:raise RuntimeError(f'Expected 3969 samples, got {len(rows)}')
with (results/'raw.csv').open('w') as out:
    w=csv.DictWriter(out,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
groups=collections.defaultdict(list)
for row in rows:groups[(row['distribution'],row['n'],row['workload'],row['implementation'])].append(row['ns_per_operation'])
summary=[]
for (dist,n,work,impl),values in sorted(groups.items()):
    q1,_,q3=statistics.quantiles(values,n=4,method='inclusive')
    summary.append(dict(distribution=dist,n=n,workload=work,implementation=impl,samples=len(values),median_ns=statistics.median(values),q1_ns=q1,q3_ns=q3,iqr_ns=q3-q1))
write_json(results/'summary.json',summary)
write_json(results/'metadata.json',metadata(version,flags)|{'status':'passed','processes':3,'trials':7,'warmups':2,'calibration_ns':20000000,'samples':len(rows),'seed':20261010,'allocation_budget':262144,'validation':'Complete oracle results outside timing; checked checksums inside every batch','order':'(implementation + trial + process) modulo 3'})
