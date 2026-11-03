import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsModHalf
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsBaseLeaves

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def blsHalfStep (counter coefficient : MlS) : ProgHOL 64 :=
  .seq (blsUnaryCall (ofString "bls_fp_shr1") counter)
    (blsUnaryCall (ofString "bls_fp_half_can") coefficient)

def blsHalfTyped (counter coefficient : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ a x : Limbs384, s.locals.lookup counter = some a.toValue ∧
    s.locals.lookup coefficient = some x.toValue

def blsHalfStepCost : Nat := (K.bls_fp_shr1 + 1) + (K.bls_fp_half_can + 1)

theorem blsHalfStep_bound (counter coefficient : MlS) :
    TerminatingProgBounded (blsHalfStep counter coefficient) blsHalfStepCost :=
  TerminatingProgBounded.seq (TerminatingProgBounded.call ub_bls_fp_shr1 _ _)
    (TerminatingProgBounded.call ub_bls_fp_half_can _ _)

theorem blsHalfStep_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter coefficient : MlS) (a x : Limbs384) (hcx : counter ≠ coefficient)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup counter = some a.toValue)
    (hx : s.locals.lookup coefficient = some x.toValue) :
    (evaluateHOLFiniteState s (blsHalfStep counter coefficient)).1 = some .timeOut ∨
      ∃ r : Limbs384,
        (evaluateHOLFiniteState s (blsHalfStep counter coefficient)).1 = none ∧
        (evaluateHOLFiniteState s (blsHalfStep counter coefficient)).2.locals =
          (s.locals.update (counter, (half384 a).toValue)).update (coefficient, r.toValue) := by
  unfold blsHalfStep
  rw [evaluateHOLFiniteState_seq_line780]
  have hf := blsHalf_call s counter a hc ha
  rcases hrun : evaluateHOLFiniteState s (blsUnaryCall (ofString "bls_fp_shr1") counter) with ⟨res, mid⟩
  rw [hrun] at hf
  rcases hf with ht | ⟨hn, hl⟩
  · dsimp only at ht; subst res; exact Or.inl rfl
  · dsimp only at hn hl
    subst res
    dsimp only
    have hmc : mid.code = originalRuntimeCode := by
      have h := evalP_code s (blsUnaryCall (ofString "bls_fp_shr1") counter)
      rw [hrun] at h
      exact h.trans hc
    have hmx : mid.locals.lookup coefficient = some x.toValue := by
      rw [hl]
      simpa [HolFiniteMapExact.lookup_update, FUPDATE, hcx] using hx
    rcases blsModHalf_call_typed mid coefficient x hmc hmx with ht | ⟨r, hr, hlocals⟩
    · exact Or.inl ht
    · exact Or.inr ⟨r, hr, hlocals.trans (congrArg (fun ls => ls.update (coefficient, r.toValue)) hl)⟩
end InitECandidate.Solver.Wave8GuestInv.Arith
