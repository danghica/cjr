const fs = require('fs');
const path = require('path');
const {chromium} = require(process.env.PLAYWRIGHT_MODULE || '/Users/danghica/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright');
(async () => {
 const root=path.resolve(__dirname,'../../..');
 const browser=await chromium.launch({headless:true,executablePath:process.env.CHROME || '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome'});
 const page=await browser.newPage({viewport:{width:1280,height:900},deviceScaleFactor:2});
 await page.goto('file://'+path.join(root,'example/list_rev/docs/rocq/rocq/list_rev.html'));
 const article=page.locator('article').filter({has:page.locator('h2', {hasText:/^reverse_spec$/})});
 await article.screenshot({path:path.join(__dirname,'reverse-contract-full.png')});
 // Capture the statement region at readable scale. Context is explicitly
 // retained in the slide caption and presenter notes, outside this excerpt.
 const pre=article.locator('pre.pseudocode');
 await pre.evaluate(el=>{el.style.fontSize='24px';el.style.lineHeight='1.35'});
 const box=await pre.boundingBox();
 await page.screenshot({path:path.join(__dirname,'reverse-contract.png'),clip:{x:box.x+45,y:box.y+32.4*7,width:610,height:32.4*7.2}});
 await page.setViewportSize({width:1280,height:1600});
 await page.goto('file://'+path.join(root,'example/list_rev/docs/rocq/index.html'));
 await page.selectOption('#graph-view','focus');
 await page.fill('#graph-focus','cjr.examples.list_rev.reverse_twice_spec');
 await page.locator('#graph-focus').dispatchEvent('change');
 await page.locator('#graph-fit').click();
 const bounds=await page.locator('.graph-node').evaluateAll(nodes=>{
  const boxes=nodes.map(n=>n.getBoundingClientRect());
  const x=Math.min(...boxes.map(b=>b.x))-16, y=Math.min(...boxes.map(b=>b.y))-16;
  return {x,y,width:Math.max(...boxes.map(b=>b.right))-x+16,height:Math.max(...boxes.map(b=>b.bottom))-y+16};
 });
 await page.screenshot({path:path.join(__dirname,'dependency-navigation.png'),clip:bounds});
 await browser.close();
 console.log('Captured existing Rocq-readable pages.');
})().catch(e=>{console.error(e);process.exitCode=1});
