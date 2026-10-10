#!/usr/bin/env python3
"""Assemble an offline index from renderer navigation, never guessed anchors."""
from html import escape
from html.parser import HTMLParser
from urllib.parse import urlsplit,unquote
import json,re,os,subprocess,sys
from common import ROOT,hashes,write_json
E=escape
class Page(HTMLParser):
    def __init__(self,text):
        super().__init__();self.ids=set();self.links=[];self.declarations=[];self.nav=False;self.current=None;self.label='';self.feed(text)
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if 'id' in a:self.ids.add(a['id'])
        for k in ['href','src']:
            if k in a:self.links.append(a[k])
        if tag=='nav' and a.get('aria-label')=='Declarations':self.nav=True
        if self.nav and tag=='a':self.current=a['href'];self.label=''
    def handle_data(self,data):
        if self.current:self.label+=data
    def handle_endtag(self,tag):
        if tag=='a' and self.current:self.declarations.append((self.current,self.label));self.current=None
        if tag=='nav':self.nav=False

def page(path,title,body):
    css=os.path.relpath(ROOT/'docs/report.css',path.parent);home=os.path.relpath(ROOT/'index.html',path.parent)
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(f'<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{E(title)}</title><link rel="stylesheet" href="{E(css)}"><main><header><div class="eyebrow">CJR · QUADTREE</div><h1>{E(title)}</h1><a href="{E(home)}">Report index</a></header>{body}<footer>Offline report. All links and assets stay within this example.</footer></main></html>')
def artifact(rel):
    p=ROOT/rel
    if not p.exists():raise RuntimeError('Missing artifact: '+rel)
    return json.loads(p.read_text())
def fresh(data,label,current):
    recorded=data.get('sources',{})
    for key,value in recorded.items():
        if current.get(key)!=value:raise RuntimeError(f'Stale {label}: {key}')
    if not recorded:raise RuntimeError('Missing source hashes: '+label)
    if label!='extraction' and set(recorded)!=set(current):raise RuntimeError('Source inventory changed since '+label)
def clean(text):return re.sub(r'\x1b(?:\[[0-?]*[ -/]*[@-~]|.)','',text)
def main():
    current=hashes();verification=artifact('proof/results/verification.json');test=artifact('test/results/report.json');bench=artifact('benchmark/results/metadata.json');docs=artifact('docs/metadata.json');extraction=artifact('extracted/metadata.json')
    for label,data in [('verification',verification),('tests',test),('benchmarks',bench),('documentation',docs),('extraction',extraction)]:fresh(data,label,current)
    for label,data in [('verification',verification),('tests',test),('benchmarks',bench)]:
        if data['status']!='passed':raise RuntimeError('Failed '+label)
    renderer=artifact('docs/rocq/report.json')
    if any(f.get('errors') for f in renderer.get('files',[])):raise RuntimeError('Renderer reported errors')
    plots=[ROOT/f'benchmark/results/{d}.svg' for d in ['uniform','cluster','prefix']]
    if not all(p.exists() for p in plots):raise RuntimeError('Missing benchmark charts; run scripts/plot.py with matplotlib')
    groups={k:[] for k in ['Specification and model','Algorithm and extraction','Ownership predicates','Correctness','Algebraic laws']}
    for path in sorted((ROOT/'docs/rocq').rglob('*.html')):
        if path.name=='index.html':continue
        for anchor,name in Page(path.read_text()).declarations:
            rel=os.path.relpath(path,ROOT)
            group='Specification and model' if '/spec/' in rel else 'Algorithm and extraction' if '/algorithm/' in rel else 'Ownership predicates' if path.stem=='ownership' else 'Correctness'
            if any(x in name for x in ['commutative','idempotent','repeated','distributes','union']):group='Algebraic laws'
            groups[group].append(f'<li><a href="{E(rel+anchor)}">{E(name)}</a></li>')
    sources=[]
    for path in sorted((ROOT/'extracted').glob('*.cj')):
        view=path.with_suffix('.html');page(view,path.name,'<pre>'+E(path.read_text())+'</pre>')
        sources.append(f'<li><a href="{E(os.path.relpath(path,ROOT))}">{E(path.name)}</a> · <a href="{E(os.path.relpath(view,ROOT))}">HTML source</a></li>')
    cases=''.join(f'<li><span class="badge">Passed</span> {E(c)}</li>' for c in test['cases'])
    page(ROOT/'test/report.html','Runtime test report',f'<p><span class="badge">Passed</span> Five test groups on unchanged extracted code.</p><ul>{cases}</ul><p>Seed {test["seed"]}; {test["random_operations"]:,} randomized operations; {test["pair_orders"]} point-pair orders; reverse and three rotated insertion permutations; full set comparison.</p><h2>Execution</h2><pre>{E(clean(test["stdout"]))}</pre><h2>Compiler and provenance</h2><pre>{E(json.dumps({k:v for k,v in test.items() if k not in ["stdout","stderr"]},indent=2))}</pre><p><a href="results/report.json">JSON report</a> · <a href="results/compile.log">Compilation log</a> · <a href="results/execution.log">Execution log</a></p>')
    summary=artifact('benchmark/results/summary.json');rows=''.join('<tr>'+''.join(f'<td>{E(str(r[k]))}</td>' for k in ['distribution','n','workload','implementation'])+f'<td>{r["median_ns"]:.1f}</td><td>{r["iqr_ns"]:.1f}</td><td>{r["samples"]}</td></tr>' for r in summary)
    charts=''.join(f'<h2>{d.capitalize()} distribution</h2><img src="results/{d}.svg" alt="{d} benchmark medians and IQR">' for d in ['uniform','cluster','prefix'])
    methodology='<p>Three implementations: CJR extracted code, an independent native quadtree with the same fixed-domain subdivision policy, and a flat collection with hash-indexed membership and range scanning. The native baseline stores children in an ArrayList; extracted code stores four child fields, so the measured comparison includes layout costs. Uniform points span the depth-30 domain; clustered points occupy a 256-square; shared-prefix points fill a 128-wide grid near the origin.</p><p>Two warmup batches, independent calibration toward 20 ms, seven trials in each of three fresh processes. Implementation order rotates by trial and process. Construction and query repetition limits bound allocation; capped batches may take less than 20 ms. Complete results are checked against the flat oracle outside timing; checked checksums are consumed inside each batch. Construction, hits and misses report ns per point; range workloads report ns per query. Allocation and GC costs are included.</p>'
    page(ROOT/'benchmark/report.html','Benchmark report',methodology+charts+'<h2>Timing summaries</h2><div class="scroll"><table><thead><tr><th>Distribution</th><th>Points</th><th>Workload</th><th>Implementation</th><th>Median ns/op</th><th>IQR ns/op</th><th>Trials</th></tr></thead><tbody>'+rows+'</tbody></table></div><h2>Downloads</h2><p><a href="results/raw.csv">Raw CSV observations</a> · <a href="results/summary.json">Summary JSON</a> · <a href="results/metadata.json">Machine, compiler and source hashes</a></p><details><summary>Recorded metadata</summary><pre>'+E(json.dumps(bench,indent=2))+'</pre></details>')
    decls=''.join(f'<h3>{E(group)}</h3><ul class="declarations">'+''.join(entries)+'</ul>' for group,entries in groups.items())
    coverage=E(verification.get('contract_coverage',''))
    rendered=sum(f['declarations'] for f in renderer.get('files',[]))
    unsupported=sum(len(f.get('unsupported',[])) for f in renderer.get('files',[]))
    body=f'<p>An integer-point quadtree over a fixed half-open square. This report connects proof-free Rocq declarations, directly extracted Cangjie, runtime validation and measured performance.</p><nav><a href="#declarations">Definitions and lemmas</a><a href="#extracted">Extracted Cangjie</a><a href="test/report.html">Runtime test report</a><a href="benchmark/report.html">Benchmark report</a></nav><h2>Verification summary</h2><p><span class="badge">Kernel checked</span> {verification["audited_declarations"]} declarations audited; assumptions closed under the global context.</p><p>{coverage}</p><p>Iris weakest-precondition contracts express partial correctness: if a call returns, the postcondition holds. The reference algebra uses point-set equality; query list order and fresh result allocations are not observable in that equality.</p><p><a href="proof/results/coqchk.log">coqchk log</a> · <a href="proof/results/assumptions.log">Assumption audit</a> · <a href="proof/results/verification.json">Verification metadata</a> · <a href="docs/rocq/report.json">Renderer coverage and diagnostics</a></p><p>{rendered} rendered declarations; {unsupported} unsupported or unmapped construct entries retain their source representation; no renderer errors.</p><details><summary>Renderer diagnostics</summary><pre>{E(json.dumps(renderer,indent=2))}</pre></details><h2 id="extracted">Extracted Cangjie</h2><ul>'+''.join(sources)+'</ul><p>The generated code is unchanged by the tests and benchmarks. <a href="extracted/metadata.json">Extraction provenance</a>.</p><h2 id="declarations">Definitions and lemmas</h2>'+decls
    page(ROOT/'index.html','Quadtree specification and validation',body)
    check_links()
    write_json(ROOT/'docs/link-check.json',{'status':'passed','html_files':len(list(ROOT.rglob('*.html'))),'boundary':'quadtree/; every local destination and fragment resolved'})
    print('Report assembled; all local links and declaration anchors resolve.')
def check_links():
    pages={p.resolve():Page(p.read_text()) for p in ROOT.rglob('*.html')}
    for source,parsed in pages.items():
        for link in parsed.links:
            u=urlsplit(link)
            if u.scheme or u.netloc:raise RuntimeError('External URL: '+link)
            dest=(source.parent/unquote(u.path)).resolve() if u.path else source
            if not dest.is_relative_to(ROOT):raise RuntimeError('Link leaves example: '+link)
            if not dest.is_file():raise RuntimeError('Missing link target: '+str(dest))
            if u.fragment and (dest not in pages or unquote(u.fragment) not in pages[dest].ids):raise RuntimeError('Missing anchor: '+link)
if __name__=='__main__':main()
