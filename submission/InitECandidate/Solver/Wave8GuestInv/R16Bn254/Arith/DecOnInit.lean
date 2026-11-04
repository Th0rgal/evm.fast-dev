import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.SeqOnNone

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded

/-- A successful declaration may establish a stronger continuation invariant. -/
theorem TerminatingProgBoundedOn.dec_on_init
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn Q body B)
    (hinit : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      state.code = originalRuntimeCode → P state →
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) init = some v →
      shapeEqHOL shape (shapeOfHOLExact v) = true → Q (setVarHOLFinite name v state)) :
    TerminatingProgBoundedOn P (.dec name shape init body) B := by
  intro F state hc hp
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i value heval hshape
      have hb := hbody (setVarHOLFinite name value state) hc
        (hinit state value hc hp heval hshape) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
