// Offline visual/layout acceptance. PLAYWRIGHT_MODULE and CHROME are configurable.
const path=require('path');const fs=require('fs');
const {chromium}=require(process.env.PLAYWRIGHT_MODULE||'/Users/danghica/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
const root=path.resolve(__dirname,'..');
(async()=>{
  const browser=await chromium.launch({headless:true,executablePath:process.env.CHROME||'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome'});
  const page=await browser.newPage();const results=[];
  fs.mkdirSync(path.join(root,'docs/visual'),{recursive:true});
  const targets=['index.html','docs/rocq/spec/model.html','docs/rocq/proof/algebra.html','extracted/quadtree.html','test/report.html','benchmark/results/report.html'];
  for(const width of [1280,390]){
    await page.setViewportSize({width,height:900});
    for(const target of targets){
      await page.goto('file://'+path.join(root,target));
      const r=await page.evaluate(()=>({title:document.title,width:innerWidth,body:document.documentElement.scrollWidth,wrapping:[...document.querySelectorAll('pre')].map(p=>getComputedStyle(p).whiteSpace)}));
      if(r.body>width+1)throw Error('Page overflow: '+target+' at '+width);
      if(r.wrapping.some(w=>w!=='pre'))throw Error('Unexpected source wrapping: '+target);
      const file=target.replace(/\//g,'-').replace(/\.html$/,'')+'-'+width+'.png';
      await page.screenshot({path:path.join(root,'docs/visual',file)});results.push({target,width,...r,screenshot:file});
    }
  }
  fs.writeFileSync(path.join(root,'docs/visual/checks.json'),JSON.stringify({status:'passed',pages:results},null,2)+'\n');
  await browser.close();console.log('Desktop and narrow layouts passed.');
})().catch(e=>{console.error(e);process.exitCode=1});
