#!/usr/bin/env python3
"""Compose exact per-function Lab sections in bounded chunks."""
from guest_layout import LAST_LABEL, STOP_LABEL
import pathlib,subprocess,time,json,os
root=pathlib.Path(__file__).resolve().parents[1];work=root/"work/lean-perf/backend-stages"
for first in range(64,STOP_LABEL,16):
 last=min(first+15,LAST_LABEL);ns=range(first,last+1);name=f"SectionChunk{first}_{last}"
 if (work/f"{name}.check.json").exists() and json.loads((work/f"{name}.check.json").read_text())["returncode"] == 0 and (root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{name}.olean").exists(): continue
 for n in ns:
  while not (work/f"Section{n}.check.json").exists():time.sleep(1)
  if json.loads((work/f"Section{n}.check.json").read_text())["returncode"]:raise RuntimeError(f"Section{n}")
 while not (root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/NamedChunk{first}_{last}.olean").exists():time.sleep(1)
 s=f"import InitECandidate.Proofs.BackendStages.NamedChunk{first}_{last}\n"+"".join(f"import InitECandidate.Proofs.BackendStages.Section{n}\n" for n in ns)
 s+="set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nopen Flapjack Flapjack.Compiler.Backend\nnamespace InitECandidate.Proofs.BackendStages."+name+"\n"
 s+="def sections : LabSem.LabProgHOL 64 := ["+", ".join(f"section{n}" for n in ns)+"]\n"
 s+=f"theorem compiled_eq : NamedChunk{first}_{last}.bodies.map StackToLab.progToSectionHOL = sections := by\n  change ["+", ".join(f"StackToLab.progToSectionHOL Named{n}" for n in ns)+"] = sections\n"
 s+="  rw ["+", ".join(f"section{n}_eq" for n in ns)+"]\n  rfl\n#print axioms compiled_eq\nend InitECandidate.Proofs.BackendStages."+name+"\n"
 source=root/f"submission/InitECandidate/Proofs/BackendStages/{name}.lean";source.write_text(s);started=time.monotonic()
 r=subprocess.run(["rtk","proxy","python3",str(root/"tools/prepare-backend-lean.py"),"-o",str(root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{name}.olean"),str(source)],cwd=root,env=dict(os.environ,LAKE_ARTIFACT_CACHE="false"),text=True,capture_output=True)
 (work/f"{name}.check.log").write_text(r.stdout+r.stderr);(work/f"{name}.check.json").write_text(json.dumps(dict(returncode=r.returncode,seconds=time.monotonic()-started)));print(f"{name}: {r.returncode}",flush=True);r.check_returncode()
