"""Local toolchain and provenance utilities shared by report builders."""
from pathlib import Path
import os, subprocess, hashlib, json, platform, re, tempfile
ROOT=Path(__file__).resolve().parents[1]
DEFAULT_CJC=Path.home()/'cangjiebuild/software/cangjie/bin/cjc'
def toolchain():
    cjc=Path(os.environ.get('CJC',str(DEFAULT_CJC)))
    home=Path(os.environ.get('CANGJIE_HOME',str(cjc.parent.parent)))
    env=os.environ.copy(); env['CANGJIE_HOME']=str(home)
    env['DYLD_LIBRARY_PATH']=str(home/'runtime/lib/darwin_aarch64_cjnative')
    if 'SDKROOT' in os.environ: env['SDKROOT']=os.environ['SDKROOT']
    elif platform.system()=='Darwin':
        sdk=Path(subprocess.check_output(['xcrun','--show-sdk-path'],text=True).strip())
        # LLVM bundled with Cangjie 1.0.5 predates Apple's arm64e.x1 TAPI target.
        # Copy linker stubs only; normalize target labels without changing symbols.
        compat=Path(tempfile.gettempdir())/'cjr-quadtree-sdk'
        for p in (sdk/'usr/lib').rglob('*.tbd'):
            if p.is_symlink(): continue
            target=compat/p.relative_to(sdk);target.parent.mkdir(parents=True,exist_ok=True)
            text=re.sub(r'arm64e\.x1-[\w]+\s*,?\s*','',p.read_text())
            text=re.sub(r',\s*\]', ' ]',text).replace('arm64e-','arm64-')
            if not target.exists() or target.read_text()!=text: target.write_text(text)
        link=compat/'usr/lib/libSystem.tbd'
        if not link.is_symlink(): link.symlink_to('libSystem.B.tbd')
        env['SDKROOT']=str(compat)
    version=subprocess.check_output([str(cjc),'--version'],env=env,text=True).strip()
    if '1.0.5' not in version: raise RuntimeError('Cangjie 1.0.5 required; found '+version)
    return cjc, env, version
def hashes():
    sources=sorted(p for p in ROOT.rglob('*') if p.is_file() and p.suffix in {'.v','.cj','.py','.cjs'} and 'results' not in p.parts and p.name!='print.v')
    sources += [ROOT/'_CoqProject',ROOT/'Makefile',ROOT/'README.md',ROOT/'docs/report.css',ROOT.parent/'theories/examples/cj_print.v',ROOT.parent/'theories/lang.v',ROOT.parent/'tools/rocq_readable/renderings.json']
    return {os.path.relpath(p,ROOT):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
def metadata(version, flags):
    return {'sources':hashes(),'compiler':version,'flags':flags,'machine':platform.uname()._asdict(),'sdk':os.environ.get('SDKROOT','macOS TAPI compatibility copy: arm64e.x1 removed, arm64e labels normalized to arm64')}
def write_json(path,data):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
