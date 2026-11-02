import InitECandidate.Solver.Wave8Stage.CompilerOutput
import InitECandidate.Solver.Wave8Stage.NativeLength
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.OriginalCompilerPremise
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Encoders.RiscV.Target

/-- Even after removing the nonexistent `asmConf` field, the frozen `hltc`
premise is impossible: updating only labels preserves `pos`, but the native
image has 979140 bytes and successful compilation must advance `pos`. This
is a specification diagnostic, not the nonvacuous Stage 5 transfer. -/
theorem native_image_cannot_update_labels_only
    (config : Config) (labs : Spt (Spt Nat)) (source : LabProgHOL 64) :
    compile riscvConfig config source ≠
      some (InitECandidate.nativeCode, {config with labels := labs}) := by
  intro run
  have empty := CompilerOutput.same_position_empty riscvConfig config _ source
    InitECandidate.nativeCode run rfl
  have zero := congrArg List.length empty
  rw [InitECandidate.Proofs.LiteralFacts.nativeCode_length] at zero
  change 979140 = 0 at zero
  omega

#print axioms native_image_cannot_update_labels_only
end InitECandidate.Solver.Wave8Stage.OriginalCompilerPremise
