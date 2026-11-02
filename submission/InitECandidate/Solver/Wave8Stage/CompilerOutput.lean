import Flapjack.Compiler.Backend.LabToTarget.Compile

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CompilerOutput
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem

/-- Successful compilation retains the actual canonical label-removal witness,
its bytes, and the updated output position. -/
theorem witness {width : Nat} [NeZero width]
    (asm : Compiler.Encoders.Asm.AsmConfigExact width) (config output : Config)
    (source : LabProgHOL width) (bytes : List (BitVec 8))
    (run : compile asm config source = some (bytes, output)) :
    ∃ code labs ffis,
      removeLabels config.initClock asm config.pos config.labels ffis
        (LabFilter.filterSkip source) = some (code, labs) ∧
      bytes = progToBytes code ∧ output.labels = labs ∧ output.pos = bytes.length + config.pos := by
  unfold compile compileLab at run
  cases names : config.ffiNames with
  | none =>
    simp only [names, ↓reduceIte] at run
    split at run
    · rename_i code labs removed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj run).symm
      exact ⟨code, labs, findFfiNames (LabFilter.filterSkip source), removed, rfl, rfl, rfl⟩
    · cases run
  | some ffis =>
    simp only [names] at run
    split at run
    · split at run
      · rename_i code labs removed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj run).symm
        exact ⟨code, labs, ffis, removed, rfl, rfl, rfl⟩
      · cases run
    · cases run

/-- The output position advances by precisely the emitted byte count. -/
theorem position {width : Nat} [NeZero width]
    (asm : Compiler.Encoders.Asm.AsmConfigExact width) (config output : Config)
    (source : LabProgHOL width) (bytes : List (BitVec 8))
    (run : compile asm config source = some (bytes, output)) :
    output.pos = bytes.length + config.pos := by
  obtain ⟨_, _, _, _, _, _, h⟩ := witness asm config output source bytes run
  exact h

/-- Keeping the input position in a compiler output requires an empty image. -/
theorem same_position_empty {width : Nat} [NeZero width]
    (asm : Compiler.Encoders.Asm.AsmConfigExact width) (config output : Config)
    (source : LabProgHOL width) (bytes : List (BitVec 8))
    (run : compile asm config source = some (bytes, output))
    (same : output.pos = config.pos) : bytes = [] := by
  have advanced := position asm config output source bytes run
  have zero : bytes.length = 0 := by omega
  exact List.length_eq_zero_iff.mp zero

end InitECandidate.Solver.Wave8Stage.CompilerOutput
