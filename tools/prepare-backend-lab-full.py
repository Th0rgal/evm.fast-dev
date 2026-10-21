#!/usr/bin/env python3
"""Compose all independent section filtering or initial encodings."""
from guest_layout import LAST_LABEL, STOP_LABEL
import pathlib,time,json,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[1];work=root/"work/lean-perf/backend-stages"
stage=sys.argv[1];assert stage in ["Filtered","Encoded"]
chunks=[(a,min(a+15,LAST_LABEL)) for a in range(64,STOP_LABEL,16)]
for suffix in ["Stubs"]+[f"Chunk{a}_{b}" for a,b in chunks]:
 p=work/f"{stage}{suffix}.check.json"
 while not p.exists():time.sleep(3)
 if json.loads(p.read_text())["returncode"]:raise RuntimeError(str(p))
prev="Sections" if stage=="Filtered" else "Filtered"
while not (root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{prev}.olean").exists():time.sleep(3)
fun="(fun sec => { sec with lines := sec.lines.filter LabFilter.notSkip })" if stage=="Filtered" else "(LabToTarget.encSec riscvConfig.encode (riscvConfig.encode (.inst .skip)).length)"
priorName=lambda i: f"Sections.sections{i}" if stage=="Filtered" else f"Filtered.sections{i}"
s=f"import InitECandidate.Proofs.BackendStages.{prev}\nimport InitECandidate.Proofs.BackendComputation\nimport InitECandidate.Proofs.BackendStages.{stage}Stubs\n"+"".join(f"import InitECandidate.Proofs.BackendStages.{stage}Chunk{a}_{b}\n" for a,b in chunks)
s+="set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nopen Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target\nnamespace InitECandidate.Proofs.BackendStages."+stage+"\n"
s+="def sections52 : LabSem.LabProgHOL 64 := []\n"+f"theorem sections52_eq : {priorName(52)}.map {fun} = sections52 := by rfl\n"
for i,(a,b) in reversed(list(enumerate(chunks))):
 s+=f"def sections{i} := {stage}Chunk{a}_{b}.sections ++ sections{i+1}\n"
 s+=f"theorem sections{i}_eq : {priorName(i)}.map {fun} = sections{i} := by\n  unfold {priorName(i)} sections{i}\n  rw [List.map_append, {stage}Chunk{a}_{b}.compiled_eq, sections{i+1}_eq]\n"
s+=f"def program := {stage}Stubs.sections ++ sections0\n"
s+=f"theorem map_eq : {prev}.program.map {fun} = program := by\n  unfold {prev}.program program\n  rw [List.map_append, {stage}Stubs.compiled_eq, sections0_eq]\n"
statement="LabFilter.filterSkip Sections.program = program" if stage=="Filtered" else "LabToTarget.encSecList riscvConfig.encode Filtered.program = program"
lemma="InitECandidate.Proofs.BackendComputation.filterSkip_eq_map" if stage=="Filtered" else "InitECandidate.Proofs.BackendComputation.encSecList_eq_map"
s+=f"theorem compile_eq : {statement} := by\n  rw [{lemma}, map_eq]\n#print axioms compile_eq\nend InitECandidate.Proofs.BackendStages.{stage}\n"
source=root/f"submission/InitECandidate/Proofs/BackendStages/{stage}.lean";source.write_text(s);start=time.monotonic()
r=subprocess.run(["rtk","proxy","python3",str(root/"tools/prepare-backend-lean.py"),"-o",str(root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/{stage}.olean"),str(source)],cwd=root,text=True,capture_output=True)
(work/f"{stage}.check.log").write_text(r.stdout+r.stderr);(work/f"{stage}.check.json").write_text(json.dumps(dict(returncode=r.returncode,seconds=time.monotonic()-start)));print(r.stdout+r.stderr);r.check_returncode()
