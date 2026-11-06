import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Batch02

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Parts
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition Stack151Frame

noncomputable def transform (p : WordLangProgHOL (BitVec 64)) :=
  WordRemove.removeMustTerminate
    (WordAlloc.applyColour (WordAlloc.totalColour (oracle151.getD .ln)) p)

theorem transform_seq (p q : WordLangProgHOL (BitVec 64)) :
    transform (.seq p q) = .seq (transform p) (transform q) := rfl

open Lean Elab Command in
elab "wave8_stack151_assemble" : command => do
  let emit (source : String) : CommandElabM Unit := do
    match Parser.runParserCategory (← getEnv) `command source with
    | .error message => throwError "{message}"
    | .ok command => elabCommand command
  emit "noncomputable def suffix5944 := result5944"
  emit "theorem suffix5944_eq : WordToStack.Native.compNative riscvConfig false (transform Word151ClashTree.part5944Suffix) result5943.2 (registers, frame, stackVariables) = suffix5944 := by rw [show transform Word151ClashTree.part5944Suffix = program5944 from program5944_eq]; exact result5944_eq"
  for i in List.range 5944 do
    let n := 5943 - i
    let initial := if n = 0 then "Function150.stackResult.2.2" else s!"result{n-1}.2"
    emit s!"noncomputable def suffix{n} : Flapjack.Compiler.Backend.StackLang.HolProg 64 × (AppList (BitVec 64) × Nat) := (.seq result{n}.1 suffix{n+1}.1, suffix{n+1}.2)"
    emit s!"theorem suffix{n}_eq : WordToStack.Native.compNative riscvConfig false (transform Word151ClashTree.part{n}Suffix) {initial} (registers, frame, stackVariables) = suffix{n} := by rw [Word151ClashTree.part{n}Suffix, transform_seq, show transform Word151ClashTree.part{n} = program{n} from program{n}_eq]; exact StackCompileComposition.compile_seq _ _ _ _ _ _ _ _ _ _ result{n}_eq suffix{n+1}_eq"

wave8_stack151_assemble

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Parts
