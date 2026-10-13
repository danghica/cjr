import fs from 'node:fs/promises';
import {constants as fsConstants} from 'node:fs';
import path from 'node:path';
import {fileURLToPath, pathToFileURL} from 'node:url';
import {createRequire} from 'node:module';
import {slides} from './content.mjs';
const dir=path.dirname(fileURLToPath(import.meta.url));
const root=path.resolve(dir,'../..');
const runtimeRoot=process.env.CJR_RUNTIME_ROOT || '/Users/danghica/.cache/codex-runtimes/codex-primary-runtime/dependencies';
const modules=process.env.CJR_NODE_MODULES || path.join(runtimeRoot,'node/node_modules');
process.env.RUNTIME_NODE_MODULES=modules;
const req=createRequire(path.join(modules,'package.json'));
const {Presentation,PresentationFile}=await import(pathToFileURL(req.resolve('@oai/artifact-tool')).href);
const skill=process.env.CJR_PRESENTATIONS_SKILL || '/Users/danghica/.codex/plugins/cache/openai-primary-runtime/presentations/26.1007.11041/skills/presentations';
const {finalizePresentation,applyPresentationChartFont}=await import(pathToFileURL(path.join(skill,'container_tools/artifact_tool_utils.mjs')).href);
const build=path.join(dir,'.build'); await fs.mkdir(build,{recursive:true});
const colors=['#245C9D','#6F889E','#C18438'];
const font='Arial';
const {createCanvas}=req('@napi-rs/canvas');
const measure=createCanvas(1,1).getContext('2d');
const p=Presentation.create({slideSize:{width:1280,height:720}});
p.theme.defaultFont=font;
const emptyLine={fill:'none',width:0};
function text(s,value,x,y,w,h,size=28,color='#253345',bold=false,mono=false){
 const shape=s.shapes.add({geometry:'textbox',position:{left:x,top:y,width:w,height:h},fill:'none',line:emptyLine});
 shape.text=value;shape.text.style={fontFamily:mono?'Menlo':font,typeface:mono?'Menlo':font,fontSize:size,color,bold,verticalAlignment:'top',insets:0,wrap:true};
 return shape;
}
function list(s,items,x,y,w,size=28,gap=92){
 measure.font=`${size}px Arial`;
 for(const item of items){
  let lines=1,line='';
  for(const word of item.split(' ')){const next=line?line+' '+word:word;if(measure.measureText(next).width>w-4){lines++;line=word;}else line=next;}
  const height=Math.ceil(lines*size*1.24)+5;
  text(s,item,x,y,w,height,size); y+=Math.max(gap,height+18);
 }
}
function header(s,title,n){text(s,title,64,42,1150,92,44,'#183F71',true);text(s,String(n).padStart(2,'0'),1180,675,38,24,16,'#667488');}
function columns(s,d,y=178){text(s,d.leftTitle,64,y,535,48,29,'#245C9D',true);text(s,d.rightTitle,672,y,535,48,29,'#245C9D',true);list(s,d.left,64,y+62,535,28,88);list(s,d.right,672,y+62,535,28,88);}
function takeaway(s,t,y=610){if(t)text(s,t,64,y,1130,60,25,'#183F71',true);}
async function data(name){const b=path.join(root,'example',name,'benchmark/results');return {rows:JSON.parse(await fs.readFile(path.join(b,'summary.json'),'utf8')),meta:JSON.parse(await fs.readFile(path.join(b,'metadata.json'),'utf8'))};}
function chart(s,{x,y,w,h,title,categories,series,unit}){
 const c=s.charts.add('bar',{position:{left:x,top:y,width:w,height:h},title,titleTextStyle:{fontSize:24,fill:'#253345',bold:true},categories,series:series.map((r,i)=>({...r,values:r.values.map(v=>Number(v.toPrecision(12))),fill:colors[i]})),hasLegend:true,legend:{position:'bottom',overlay:false,textStyle:{fontSize:20}},barOptions:{direction:'column',grouping:'clustered',gapWidth:100},xAxis:{textStyle:{fontSize:20},line:{fill:'#9EABBA',width:1}},yAxis:{min:0,title:{text:unit,textStyle:{fontSize:20}},textStyle:{fontSize:18},numberFormatCode:'0.0',majorGridlines:{fill:'#DFE5ED',width:1}},chartFill:'#FFFFFF',plotAreaFill:'#FFFFFF'});
 applyPresentationChartFont(c,{fontFamily:font});return c;
}
function uncertainty(s,rows,{x=64,y=550,w=1130,size=21,label='Q1–Q3'}={}){
 text(s,label,x,y,w,28,size,'#536376');
 text(s,rows.join('\n'),x,y+32,w,72,size,'#536376');
}
function scaled(v,f=1){return (v/f).toFixed(f===1?2:2);}
function ranges(rows,f=1){return rows.map(r=>`${r.implementation}: ${scaled(r.q1_ns,f)}–${scaled(r.q3_ns,f)}`).join('   ');}
async function addImage(s,filename,x,y,w,h){const b=await fs.readFile(path.join(dir,'assets',filename));s.images.add({blob:b.buffer.slice(b.byteOffset,b.byteOffset+b.byteLength),contentType:'image/png',alt:'Actual Rocq-readable interface screenshot',fit:'contain',position:{left:x,top:y,width:w,height:h}});}
const benchmarks={};for(const n of ['list','list_rev','hash_map','quadtree'])benchmarks[n]=await data(n);
for(const [i,d] of slides.entries()){
 const s=p.slides.add();s.background.fill='#FFFFFF';header(s,d.title,i+1);
 let more='';
 if(d.kind==='cover'){
  text(s,d.subtitle,64,226,1110,160,48,'#253345',true);
  text(s,d.body,64,445,990,110,34,'#245C9D');
 }else if(d.kind==='code'){
  text(s,d.code,64,190,580,340,d.code.split('\n').length>7?25:29,'#253345',false,true);
  text(s,d.rightTitle,704,180,490,62,29,'#245C9D',true);
  list(s,d.right,704,250,490,27,85);
 }else if(d.kind==='equation'){
  text(s,d.equation,64,160,1150,130,d.equation.includes('adequate')?35:38,'#245C9D',true);
  text(s,d.equationCaption,64,300,1150,54,24,'#536376');
  columns(s,d,390);
 }else if(d.kind==='three'){
  for(const [j,item] of d.items.entries()){
   const y=185+j*140;text(s,item[0],64,y,370,65,34,'#245C9D',true);text(s,item[1],460,y,730,90,32);
  }
 }else if(d.kind==='steps'){
  for(const [j,item] of d.items.entries()){
   const y=168+j*102;text(s,item[0],64,y,250,52,30,'#245C9D',true);text(s,item[1],354,y,845,75,28);
  }takeaway(s,d.takeaway);
 }else if(d.kind==='listChart'){
  const {rows,meta}=benchmarks.list;const ns=[256,4096,16384];
  for(const [j,c] of ['list_traverse','list_build_scan'].entries())chart(s,{x:64+j*600,y:155,w:552,h:350,title:j?'Build and scan':'Traversal',categories:ns.map(String),series:['CJR','Std'].map(name=>({name:name==='Std'?'Std LinkedList':name,values:ns.map(n=>rows.find(r=>r.case===c&&r.n===n&&r.implementation===name).median_ns)})),unit:'ns / element'});
  uncertainty(s,['Traversal, n=16,384  '+ranges(rows.filter(r=>r.n===16384&&r.case==='list_traverse')),'Build + scan, n=16,384  '+ranges(rows.filter(r=>r.n===16384&&r.case==='list_build_scan'))],{y:520,label:'Interquartile ranges, ns / element'});
  text(s,'Historical local run dated '+meta.date_utc.slice(0,10)+'. 21 observations per point. Different node representations.',64,646,1120,34,20,'#536376');
  more=JSON.stringify(rows,null,2)+'\nMetadata: '+JSON.stringify(meta.protocol)+'\nCompiler: '+meta.compiler+'\nMachine: '+JSON.stringify(meta.machine);
 }else if(d.kind==='reverseChart'){
  const {rows,meta}=benchmarks.list_rev;const ns=[256,4096,16384];
  chart(s,{x:64,y:155,w:690,h:390,title:'Median time per full reversal',categories:ns.map(String),series:['CJR','Native'].map(name=>({name,values:ns.map(n=>rows.find(r=>r.n===n&&r.implementation===name).median_ns/1000)})),unit:'µs / reversal'});
  text(s,'Equivalent native algorithm',820,168,380,52,27,'#245C9D',true);
  list(s,['Prebuilt lists. Two reversals per timed batch.','Sentinel allocation and GC included.','Full sequence checks outside timing.'],820,240,380,25,98);
  uncertainty(s,ns.map(n=>`${n.toLocaleString('en-US')} nodes  ${ranges(rows.filter(r=>r.n===n),1000)}`),{y:540,size:19,label:'Interquartile ranges, µs / reversal'});
  text(s,'New local run dated '+meta.date_utc.slice(0,10)+'. 3 processes × 7 trials. Independently calibrated batches.',64,650,1130,32,20,'#536376');
  more=JSON.stringify(rows,null,2)+'\nProtocol: '+JSON.stringify(meta.protocol)+'\nCompiler: '+meta.compiler+'\nMachine: '+JSON.stringify(meta.machine);
 }else if(d.kind==='hashChart'){
  const {rows,meta}=benchmarks.hash_map;
  chart(s,{x:64,y:156,w:552,h:360,title:'Regular lookups, n = 16,384',categories:['Hit','Miss'],series:['CJR','Std'].map(name=>({name:name==='Std'?'Std HashMap':name,values:['hashmap_hit','hashmap_miss'].map(c=>rows.find(r=>r.n===16384&&r.case===c&&r.implementation===name).median_ns)})),unit:'ns / lookup'});
  chart(s,{x:664,y:156,w:552,h:360,title:'Colliding hits, n = 4,096',categories:['Colliding keys'],series:['CJR','Std'].map(name=>({name:name==='Std'?'Std HashMap':name,values:[rows.find(r=>r.n===4096&&r.case==='hashmap_collision'&&r.implementation===name).median_ns]})),unit:'ns / lookup'});
  uncertainty(s,['Regular hit  '+ranges(rows.filter(r=>r.n===16384&&r.case==='hashmap_hit')),'Colliding hit  '+ranges(rows.filter(r=>r.n===4096&&r.case==='hashmap_collision'))],{y:535,label:'Interquartile ranges, ns / lookup. Charts use different vertical scales.'});
  text(s,'Historical local run dated '+meta.date_utc.slice(0,10)+'. 21 observations per point. Baselines differ in representation.',64,650,1130,32,20,'#536376');more=JSON.stringify(rows,null,2)+'\nCompiler: '+meta.compiler+'\nMachine: '+JSON.stringify(meta.machine);
 }else if(d.kind==='quadChart'){
  const {rows,meta}=benchmarks.quadtree;const ds=['uniform','cluster','prefix'];
  const selected=rows.filter(r=>r.n===16384&&r.workload==='selective');
  chart(s,{x:64,y:155,w:745,h:385,title:'Selective range queries, n = 16,384',categories:['Uniform','Clustered','Shared prefix'],series:['CJR','Native','Flat'].map(name=>({name,values:ds.map(d=>selected.find(r=>r.distribution===d&&r.implementation===name).median_ns/1000)})),unit:'µs / query'});
  text(s,'Three comparators',850,168,350,50,27,'#245C9D',true);list(s,['CJR extracted quadtree','Independent native quadtree','Hash-indexed flat collection'],850,235,350,25,84);
  text(s,'Query-result allocation is timed. Broad queries can favour different implementations.',850,493,350,115,24);
  uncertainty(s,ds.map(d=>`${d}  ${ranges(selected.filter(r=>r.distribution===d),1000)}`),{y:548,w:760,size:18,label:'Interquartile ranges, µs / query'});
  text(s,'Historical local run dated '+meta.date_utc.slice(0,10)+'. 21 observations per point. Median and IQR.',64,655,1120,26,20,'#536376');more=JSON.stringify(selected,null,2)+'\nOther workloads: '+JSON.stringify(rows)+'\nCompiler: '+meta.compiler+'\nMachine: '+JSON.stringify(meta.machine);
 }else if(d.kind==='readable'){
  text(s,'Rocq declaration',64,156,535,50,28,'#245C9D',true);text(s,d.code,64,230,550,250,25,'#253345',false,true);
  text(s,'Rendered statement excerpt',674,156,535,50,28,'#245C9D',true);
  await addImage(s,'reverse-contract.png',674,213,535,397);
  text(s,'Both retain the CJR and invariant typeclass context. The rendering omits the proof script.',64,625,1130,55,24,'#536376');
 }else if(d.kind==='navigation'){
  await addImage(s,'dependency-navigation.png',64,165,690,400);
  text(s,d.rightTitle,800,160,410,86,29,'#245C9D',true);list(s,d.right,800,270,410,25,76);takeaway(s,d.takeaway,625);
 }else {columns(s,d);takeaway(s,d.takeaway);}
 s.speakerNotes.text=d.notes+'\n\nSources\n'+d.sources.join('\n')+(more?'\n\nBenchmark evidence (unrounded)\n'+more:'');
}
// Export evidence previews and a draft before package validation.
for(const [i,s] of p.slides.items.entries()){
 const b=await p.export({slide:s,format:'png',scale:1});await fs.writeFile(path.join(build,`slide-${String(i+1).padStart(2,'0')}.png`),new Uint8Array(await b.arrayBuffer()));
 const l=await s.export({format:'layout'});await fs.writeFile(path.join(build,`slide-${i+1}.layout.json`),await l.text());
}
const candidate=path.join(build,'candidate.pptx');await (await PresentationFile.exportPptx(p)).save(candidate);
const finalPath=process.env.CJR_SLIDES_OUTPUT || path.join(dir,'cjr.pptx');
const validatedDir=path.join(build,`final-${process.pid}`);await fs.mkdir(validatedDir,{recursive:true});
const validatedPath=path.join(validatedDir,'cjr.pptx');
await finalizePresentation({workspaceDir:dir,candidatePath:candidate,finalPath:validatedPath,pythonExecutable:process.env.CJR_RUNTIME_PYTHON || path.join(runtimeRoot,'python/bin/python3'),integrityValidatorPath:path.join(skill,'container_tools/inspect_presentation_package_integrity.py'),layoutValidatorPath:path.join(skill,'container_tools/inspect_presentation_layout_geometry.py'),layoutArgs:['--expected-slide-size-emu','12192000,6858000','--validate-heading-fit'],explicitTotalSlideCount:28,requiredNativeChartOwnerSlides:[20,22,24,26],requiredNativeTableOwnerSlides:[],materializeLiteralChartWorkbooks:true,fontPolicy:{basis:'design',families:[font,'Menlo']},verifyArtifactToolImport:true,receiptPath:path.join(build,`validation-${process.pid}.json`)});
await fs.copyFile(validatedPath,finalPath,fsConstants.COPYFILE_EXCL);
console.log('Created '+finalPath);
