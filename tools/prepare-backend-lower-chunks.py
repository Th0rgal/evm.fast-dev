#!/usr/bin/env python3
"""Compose checked local lower-pass equations without compiler reduction."""
from guest_layout import LAST_LABEL, STOP_LABEL
import argparse, pathlib, subprocess, time, json, os
parser=argparse.ArgumentParser();parser.add_argument("stage",choices=["Alloc","Removed","Named"]);args=parser.parse_args()
root=pathlib.Path(__file__).resolve().parents[1];work=root/"work/lean-perf/backend-stages"
env=dict(os.environ,LAKE_ARTIFACT_CACHE="false")
previous={"Alloc":"Raw","Removed":"Alloc","Named":"Removed"}[args.stage]
for first in range(64,STOP_LABEL,16):
 last=min(first+15,LAST_LABEL);ns=range(first,last+1);name=f"{args.stage}Chunk{first}_{last}"
 if (work/f"{name}.check.json").exists() and json.loads((work/f"{name}.check.json").read_text())["returncode"] == 0 and (root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{name}.olean").exists(): continue
 for n in ns:
  while not (work/f"{args.stage}{n}.check.json").exists():time.sleep(1)
  if json.loads((work/f"{args.stage}{n}.check.json").read_text())["returncode"]:raise RuntimeError(f"{args.stage}{n} failed")
 prevchunk=f"{previous}Chunk{first}_{last}"
 while not (root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{prevchunk}.olean").exists():time.sleep(1)
 s=f"import InitECandidate.Proofs.BackendStages.{prevchunk}\n"+"".join(f"import InitECandidate.Proofs.BackendStages.{args.stage}{n}\n" for n in ns)
 s+="set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nopen Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target\nnamespace InitECandidate.Proofs.BackendStages."+name+"\n"
 s+="def bodies : List (Nat × StackLang.HolProg 64) := ["+", ".join(f"{args.stage}{n}" for n in ns)+"]\n"
 op={"Alloc":"StackAlloc.progComp","Removed":"StackRemove.progComp false riscvConfig.addrOffset (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))","Named":"StackNames.progCompEntryHOL RiscVConfig.riscvNames"}[args.stage]
 s+=f"theorem compiled_eq : {prevchunk}.bodies.map ({op}) = bodies := by\n  change ["+", ".join(f"{op} ({n}, raw{n})" if args.stage=="Alloc" else f"{op} {previous}{n}" for n in ns)+"] = bodies\n"
 s+="  rw ["+", ".join(f"{args.stage}{n}_eq" for n in ns)+"]\n  rfl\n#print axioms compiled_eq\nend InitECandidate.Proofs.BackendStages."+name+"\n"
 source=root/f"submission/InitECandidate/Proofs/BackendStages/{name}.lean";source.write_text(s);started=time.monotonic()
 result=subprocess.run(["rtk","proxy","python3",str(root/"tools/prepare-backend-lean.py"),"-o",str(root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{name}.olean"),str(source)],cwd=root,env=env,text=True,capture_output=True)
 (work/f"{name}.check.log").write_text(result.stdout+result.stderr)
 (work/f"{name}.check.json").write_text(json.dumps(dict(returncode=result.returncode,seconds=time.monotonic()-started)))
 print(f"{name}: {result.returncode}",flush=True);result.check_returncode()
