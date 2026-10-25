#!/usr/bin/env python3
"""Resumable turbo-lean verifier for Op1 standalone WordStage pipelines."""
import argparse, hashlib, json, os, pathlib, subprocess, sys, time
ROOT = pathlib.Path(__file__).resolve().parents[1]
STATUS = ROOT / '.maxwell' / 'op1-status'
TURBO_SHA = '8f24bf8911'

def sha(path):
    return subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip()
def run(fn, passes):
    STATUS.mkdir(parents=True, exist_ok=True)
    out = STATUS / f'{fn}.json'
    if out.exists() and json.loads(out.read_text()).get('status') == 'passed':
        print(f'{fn}: cached'); return True
    files=[]
    for i in passes:
        p=ROOT/'submission/InitECandidate/Proofs/WordStages'/f'Pass{fn}_{i}.lean'
        if not p.exists(): raise FileNotFoundError(p)
        files.append(p)
    result={'fn_id':fn,'source_sha':sha(files[0]),'turbo_lean_sha':TURBO_SHA,'axioms':None,'olean_bytes':None,'status':'running'}
    out.write_text(json.dumps(result,indent=2)+'\n')
    for p in files:
        cp=subprocess.run(['turbo-lean','check','--project-dir',str(ROOT),str(p)],cwd=ROOT,text=True,capture_output=True)
        if cp.returncode:
            result['status']='failed'; result['error']=cp.stdout[-4000:]+cp.stderr[-4000:]; out.write_text(json.dumps(result,indent=2)+'\n'); return False
    result['status']='passed'; out.write_text(json.dumps(result,indent=2)+'\n'); print(f'{fn}: passed'); return True

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('fns',nargs='*',default=['64','79','121','184']); a=ap.parse_args()
    ok=True
    for fn in a.fns: ok = run(fn,range(11)) and ok
    raise SystemExit(0 if ok else 1)
if __name__=='__main__': main()
