#!/usr/bin/env python3
"""Build adapters from the audited extraction; never regenerate/rewrite the core."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[3]
APP=ROOT/'example/authenticator'
BUILD=APP/'build/frontend'
sys.path.insert(0,str(ROOT))
from tools.project_tools.support import toolchain

def prepare():
    report=json.loads((APP/'build/proof-report.json').read_text())
    if report['status']!='passed': raise RuntimeError('Core proof gate has not passed')
    current={str(p.relative_to(ROOT)) for p in (APP/'core/rocq').glob('*.v')}
    if current!=set(report['sources']):
        raise RuntimeError('Core module set changed since the proof audit')
    for name, digest in report['sources'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
            raise RuntimeError('Core sources changed since the proof audit')
    if hashlib.sha256((APP/'core/contracts.json').read_bytes()).hexdigest()!=report['contract_manifest_sha256']:
        raise RuntimeError('Contract manifest changed since the proof audit')
    runtime=json.loads((APP/'build/report.json').read_text())
    source=(APP/'core/extracted/authenticator.cj').read_text()
    if runtime['status']!='passed' or hashlib.sha256(source.encode()).hexdigest()!=runtime['source_sha256']:
        raise RuntimeError('Extraction does not match runtime evidence')
    footer='main(): Unit {\n    ()\n}\n'
    if not source.endswith(footer): raise RuntimeError('Unexpected extraction entry point')
    BUILD.mkdir(parents=True,exist_ok=True)
    core=BUILD/'core.cj';core.write_text(source[:-len(footer)])
    return core

def run(cmd,env=None):
    subprocess.run([str(x) for x in cmd],cwd=ROOT,env=env,check=True)

def cli():
    core=prepare();c,env,_=toolchain(APP/'core')
    run([c,'-O2','--set-runtime-rpath',core,*sorted((APP/'cli').glob('*.cj')),'-o',BUILD/'authenticator'],env)

def swift_command():
    developer=Path(os.environ.get('DEVELOPER_DIR','/Applications/Xcode.app/Contents/Developer'))
    compiler=developer/'Toolchains/XcodeDefault.xctoolchain/usr/bin/swiftc'
    sdk=developer/'Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk'
    if not compiler.is_file() or not sdk.is_dir():
        raise RuntimeError('A complete Xcode installation is required for SwiftUI (set DEVELOPER_DIR)')
    return [compiler,'-sdk',sdk,'-target','arm64-apple-macosx14.0',
            '-module-cache-path',BUILD/'swift-cache','-parse-as-library','-O']

def ui():
    core=prepare(); c,env,_=toolchain(APP/'core')
    library=BUILD/'libauthenticator.dylib'
    # A build-only package header and removal of the extraction's empty main.
    packaged=BUILD/'library.cj';packaged.write_text('package authenticatorbridge\n'+core.read_text())
    bridge=BUILD/'bridge.cj';bridge.write_text('package authenticatorbridge\n'+(APP/'ui/bridge.cj').read_text())
    run([c,'-O2','--output-type=dylib','--dy-std',packaged,bridge,'-o',library],env)
    runtime=Path(env['CANGJIE_HOME'])/'runtime/lib/darwin_aarch64_cjnative'
    header=Path(os.environ.get('CANGJIE_RUNTIME_INCLUDE',str(Path(env['CANGJIE_HOME']).parents[1]/'cangjie_runtime/runtime/src')))
    if not (header/'Cangjie.h').exists():
        raise RuntimeError('Cangjie 1.0.5 runtime Cangjie.h required (set by SDK source installation)')
    run(['clang','-fstack-protector-strong','-O2','-mmacosx-version-min=14.0','-c',APP/'ui/runtime.c','-I'+str(header),
         '-DAUTH_LIBRARY="'+str(library)+'"','-o',BUILD/'runtime.o'])
    bundle=BUILD/'Authenticator.app/Contents'
    (bundle/'MacOS').mkdir(parents=True,exist_ok=True)
    (bundle/'Info.plist').write_text('''<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
<key>CFBundleExecutable</key><string>Authenticator</string>
<key>CFBundleIdentifier</key><string>org.cjr.authenticator</string>
<key>CFBundleName</key><string>Authenticator</string>
<key>CFBundlePackageType</key><string>APPL</string>
<key>CFBundleVersion</key><string>1</string>
<key>NSHighResolutionCapable</key><true/>
</dict></plist>''')
    swift_sources=[APP/'ui/AccountPort.swift',APP/'ui/CoreSession.swift']
    link=['-import-objc-header',APP/'ui/AuthenticatorBridge.h',BUILD/'runtime.o',
          '-L'+str(BUILD),'-lauthenticator','-L'+str(runtime),'-lcangjie-runtime',
          '-Xlinker','-rpath','-Xlinker',BUILD,'-Xlinker','-rpath','-Xlinker',runtime]
    run([*swift_command(),*swift_sources,APP/'ui/AuthenticatorApp.swift',
         *link,'-o',bundle/'MacOS/Authenticator'])
    run(['codesign','--force','--sign','-',bundle.parent])
    run([*swift_command(),*swift_sources,APP/'ui/test/Integration.swift',*link,'-o',BUILD/'swift-tests'])
    run([BUILD/'swift-tests',APP/'test/uri-fixtures.json'])
    return runtime

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('target',choices=['cli','ui']);args=parser.parse_args()
    if args.target=='cli': cli()
    else: ui()
