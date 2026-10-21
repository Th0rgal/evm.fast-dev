#!/usr/bin/env python3
"""Compose checked section-local filtering/encoding without whole literal reduction."""
from guest_layout import LAST_LABEL, STOP_LABEL
import pathlib,time,subprocess,json,sys
root=pathlib.Path(__file__).resolve().parents[1];work=root/"work/lean-perf/backend-stages"
stage=sys.argv[1];assert stage in ["Filtered","Encoded"]
chunks=[([0,1,2,4,5,6],"Stubs")]+[(list(range(a,min(a+16,STOP_LABEL))),f"Chunk{a}_{min(a+15,LAST_LABEL)}") for a in range(64,STOP_LABEL,16)]
for ids,suffix in chunks:
 name=stage+suffix;cert=work/f"{name}.check.json"
 if cert.exists() and json.loads(cert.read_text()).get("returncode")==0:continue
 for n in ids:
  dep=work/f"{stage}{n}.check.json"
  while not dep.exists():time.sleep(2)
  if json.loads(dep.read_text())["returncode"]:raise RuntimeError(str(dep))
 prev="Section"+suffix if stage=="Filtered" else "Filtered"+suffix
 prior=root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{prev}.olean"
 while not prior.exists():time.sleep(2)
 inp="SectionStubs" if suffix=="Stubs" and stage=="Filtered" else prev+".sections"
 vals=[("section"+str(n)) if stage=="Filtered" else "Filtered"+str(n) for n in ids]
 fun="(fun sec => { sec with lines := sec.lines.filter LabFilter.notSkip })" if stage=="Filtered" else "(LabToTarget.encSec riscvConfig.encode (riscvConfig.encode (.inst .skip)).length)"
 exprs=[("{ "+v+" with lines := "+v+".lines.filter LabFilter.notSkip }") if stage=="Filtered" else "LabToTarget.encSec riscvConfig.encode (riscvConfig.encode (.inst .skip)).length "+v for v in vals]
 s=f"import InitECandidate.Proofs.BackendStages.{prev}\n"+"".join(f"import InitECandidate.Proofs.BackendStages.{stage}{n}\n" for n in ids)
 s+="set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nopen Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target\n"
 s+=f"namespace InitECandidate.Proofs.BackendStages.{name}\ndef sections : LabSem.LabProgHOL 64 := ["+", ".join(stage+str(n) for n in ids)+"]\n"
 s+=f"theorem compiled_eq : {inp}.map {fun} = sections := by\n  change ["+", ".join(exprs)+"] = sections\n  rw ["+", ".join(stage+str(n)+"_eq" for n in ids)+"]\n  rfl\n#print axioms compiled_eq\nend InitECandidate.Proofs.BackendStages."+name+"\n"
 source=root/f"submission/InitECandidate/Proofs/BackendStages/{name}.lean";source.write_text(s);start=time.monotonic()
 r=subprocess.run(["rtk","proxy","python3",str(root/"tools/prepare-backend-lean.py"),"-o",str(root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{name}.olean"),str(source)],cwd=root,text=True,capture_output=True)
 (work/f"{name}.check.log").write_text(r.stdout+r.stderr);cert.write_text(json.dumps(dict(returncode=r.returncode,seconds=time.monotonic()-start)));print(name,r.returncode,flush=True);r.check_returncode()
