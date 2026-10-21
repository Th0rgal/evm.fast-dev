#!/usr/bin/env python3
"""Extract independently checked section bytes into thin candidate-match literals."""
from guest_layout import LAST_LABEL, STOP_LABEL
import pathlib,time,json,subprocess,concurrent.futures
root=pathlib.Path(__file__).resolve().parents[1];work=root/"work/lean-perf/backend-stages"
def run(name,source,out=None):
 args=["rtk","proxy","/usr/bin/time","-v","-o",str(work/f"{name}.timing.log"),"python3",str(root/"tools/prepare-backend-lean.py")]
 if out:args += ["-o",str(out)]
 start=time.monotonic();r=subprocess.run(args+[str(source)],cwd=root,text=True,capture_output=True)
 (work/f"{name}.check.log").write_text(r.stdout+r.stderr);(work/f"{name}.check.json").write_text(json.dumps(dict(returncode=r.returncode,seconds=time.monotonic()-start)));print(name,r.returncode,flush=True);r.check_returncode()
def process(n):
 cert=work/f"Bytes{n}.check.json"
 if cert.exists() and json.loads(cert.read_text()).get("returncode")==0:return
 prior=root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/Padded{n}.olean"
 while not prior.exists():time.sleep(5)
 data=root/f"submission/InitECandidate/Proofs/BackendStages/BytesData{n}.lean"
 if not data.exists():
  runner=work/f"GenerateBytes{n}.lean"
  runner.write_text(f"import Tools.GenBackendStages\nimport InitECandidate.Proofs.BackendStages.Padded{n}\nopen Lean Flapjack Flapjack.Compiler.Backend\nrun_meta do\n  let env ← Lean.getEnv\n  let bytes := (InitECandidate.Proofs.BackendStages.Padded{n}.lines.map LabToTarget.lineBytes).flatten\n  let text ← liftM (renderWordStage env (toExpr bytes))\n  liftM (IO.FS.writeFile \"submission/InitECandidate/Proofs/BackendStages/BytesData{n}.lean\" (\"import Init.Data.BitVec\\nset_option autoImplicit false\\nset_option maxRecDepth 1000000\\nset_option maxHeartbeats 0\\nnamespace InitECandidate.Proofs.BackendStages.ByteData\\ndef bytes{n} : List (BitVec 8) :=\\n\" ++ text ++ \"\\nend InitECandidate.Proofs.BackendStages.ByteData\\n\"))\n")
  run(f"GenerateBytes{n}",runner)
 dataout=root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/BytesData{n}.olean"
 if not dataout.exists():run(f"BytesData{n}",data,dataout)
 source=root/f"submission/InitECandidate/Proofs/BackendStages/Bytes{n}.lean"
 source.write_text(f"import InitECandidate.Proofs.BackendStages.Padded{n}\nimport InitECandidate.Proofs.BackendStages.BytesData{n}\nset_option autoImplicit false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nopen Flapjack Flapjack.Compiler.Backend\nnamespace InitECandidate.Proofs.BackendStages\ntheorem sectionBytes{n}_eq : (Padded{n}.lines.map LabToTarget.lineBytes).flatten = ByteData.bytes{n} := by\n  with_unfolding_all rfl\n#print axioms sectionBytes{n}_eq\nend InitECandidate.Proofs.BackendStages\n")
 run(f"Bytes{n}",source,root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/Bytes{n}.olean")

with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 list(pool.map(process,[0,1,2,4,5,6]+list(range(64,STOP_LABEL))))
