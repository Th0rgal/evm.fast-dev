#!/usr/bin/env python3
"""Certify zero-label target collection as thin section-local key lists."""
from guest_layout import LAST_LABEL, STOP_LABEL
import pathlib,time,json,subprocess,concurrent.futures
root=pathlib.Path(__file__).resolve().parents[1];work=root/"work/lean-perf/backend-stages"
def run(name,source,out=None):
 args=["rtk","proxy","python3",str(root/"tools/prepare-backend-lean.py")]
 if out:args += ["-o",str(out)]
 start=time.monotonic();r=subprocess.run(args+[str(source)],cwd=root,text=True,capture_output=True)
 (work/f"{name}.check.log").write_text(r.stdout+r.stderr);(work/f"{name}.check.json").write_text(json.dumps(dict(returncode=r.returncode,seconds=time.monotonic()-start)));print(name,r.returncode,flush=True);r.check_returncode()
def process(n):
 cert=work/f"ZeroTargets{n}.check.json"
 if cert.exists() and json.loads(cert.read_text()).get("returncode")==0:return
 prior=root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/Padded{n}.olean"
 while not prior.exists():time.sleep(5)
 data=root/f"submission/InitECandidate/Proofs/BackendStages/ZeroData{n}.lean"
 if not data.exists():
  runner=work/f"GenerateZeroData{n}.lean"
  runner.write_text(f"import Tools.GenBackendStages\nimport InitECandidate.Proofs.BackendStages.Padded{n}\nopen Lean Flapjack Flapjack.Compiler.Backend\nrun_meta do\n  let env ← Lean.getEnv\n  let keys := InitECandidate.Proofs.BackendStages.Padded{n}.lines.filterMap fun line =>\n    match line with\n    | .labAsm (.locValue _ (.lab key 0)) _ _ _ => some key\n    | .labAsm (.jump (.lab key 0)) _ _ _ => some key\n    | .labAsm (.jumpCmp _ _ _ (.lab key 0)) _ _ _ => some key\n    | _ => none\n  let text ← liftM (renderWordStage env (toExpr keys))\n  liftM (IO.FS.writeFile \"submission/InitECandidate/Proofs/BackendStages/ZeroData{n}.lean\" (\"import Flapjack.Misc.Sptree\\nnamespace InitECandidate.Proofs.BackendStages.ZeroData\\ndef keys{n} : List Nat := \" ++ text ++ \"\\nend InitECandidate.Proofs.BackendStages.ZeroData\\n\"))\n")
  run(f"GenerateZeroData{n}",runner)
 dataout=root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/ZeroData{n}.olean"
 if not dataout.exists():run(f"ZeroData{n}",data,dataout)
 source=root/f"submission/InitECandidate/Proofs/BackendStages/ZeroTargets{n}.lean"
 source.write_text(f"import InitECandidate.Proofs.BackendStages.ZeroCollection\nimport InitECandidate.Proofs.BackendStages.Padded{n}\nimport InitECandidate.Proofs.BackendStages.ZeroData{n}\nset_option autoImplicit false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nopen Flapjack Flapjack.Compiler.Backend\nnamespace InitECandidate.Proofs.BackendStages\ntheorem targets{n}_eq : Padded{n}.lines.filterMap ZeroCollection.lineTarget = ZeroData.keys{n} := by\n  with_unfolding_all rfl\ntheorem zeroTargets{n}_eq (acc : NumSet) : LabToTarget.secGetZeroLabsAcc Padded{n} acc = ZeroData.keys{n}.foldr (fun key acc => sptInsert key () acc) acc := by\n  unfold LabToTarget.secGetZeroLabsAcc\n  rw [ZeroCollection.linesTarget_eq, targets{n}_eq]\n#print axioms zeroTargets{n}_eq\nend InitECandidate.Proofs.BackendStages\n")
 run(f"ZeroTargets{n}",source,root/f".lake/build/lib/lean/InitECandidate/Proofs/BackendStages/ZeroTargets{n}.olean")

with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 list(pool.map(process,[0,1,2,4,5,6]+list(range(64,STOP_LABEL))))
