import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsInverseBodyStep
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.SeqOnNone

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def blsInverseTyped {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ q : BlsInverseLocals, q.Matches s

def blsInverseHalfCost : Nat := (384 + 1) * (blsHalfStepCost + 1)
def blsInverseTailCost : Nat := (K.bls_fp_lt_raw + 1) + (K.bls_fp_sub_raw + 1) + (K.bls_fp_sub + 1)
def blsInverseBodyCost : Nat := blsInverseHalfCost + blsInverseHalfCost + blsInverseTailCost

theorem blsInverseUHalf_bound : TerminatingProgBoundedOn blsInverseTyped blsInverseUHalfLoop blsInverseHalfCost := by
  intro F state hc hp
  obtain ⟨q, hu, hv, hx1, hx2⟩ := hp
  exact while_bls_half_typed (ofString "u") (ofString "x1")
    (by decide) state hc ⟨q.u, q.x1, hu, hx1⟩

theorem blsInverseUHalf_preserves_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (hc : state.code = originalRuntimeCode) (hp : blsInverseTyped state)
    (hr : evaluateHOLFiniteState state blsInverseUHalfLoop = (none, post)) : blsInverseTyped post := by
  obtain ⟨q, hu, hv, hx1, hx2⟩ := hp
  have hn := bls_half_normalizes (ofString "u") (ofString "x1")
    (by decide) state q.u q.x1 hc hu hx1
  change (evaluateHOLFiniteState state blsInverseUHalfLoop).1 = some .timeOut ∨
    ((evaluateHOLFiniteState state blsInverseUHalfLoop).1 = none ∧
      BlsHalfNormalPost (ofString "u") (ofString "x1") state q.u (evaluateHOLFiniteState state blsInverseUHalfLoop).2) at hn
  rw [hr] at hn
  rcases hn with ht | ⟨_, r, y, k, hcounter, hcoeff, _, _, hrest⟩
  · cases ht
  · refine ⟨BlsInverseLocals.mk r q.v y q.x2, ?_⟩
    exact ⟨hcounter, (hrest _ (by decide) (by decide)).trans hv, hcoeff, (hrest _ (by decide) (by decide)).trans hx2⟩

theorem blsInverseVHalf_bound : TerminatingProgBoundedOn blsInverseTyped blsInverseVHalfLoop blsInverseHalfCost := by
  intro F state hc hp
  obtain ⟨q, hu, hv, hx1, hx2⟩ := hp
  exact while_bls_half_typed (ofString "v") (ofString "x2")
    (by decide) state hc ⟨q.v, q.x2, hv, hx2⟩

theorem blsInverseVHalf_preserves_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (hc : state.code = originalRuntimeCode) (hp : blsInverseTyped state)
    (hr : evaluateHOLFiniteState state blsInverseVHalfLoop = (none, post)) : blsInverseTyped post := by
  obtain ⟨q, hu, hv, hx1, hx2⟩ := hp
  have hn := bls_half_normalizes (ofString "v") (ofString "x2")
    (by decide) state q.v q.x2 hc hv hx2
  change (evaluateHOLFiniteState state blsInverseVHalfLoop).1 = some .timeOut ∨
    ((evaluateHOLFiniteState state blsInverseVHalfLoop).1 = none ∧
      BlsHalfNormalPost (ofString "v") (ofString "x2") state q.v (evaluateHOLFiniteState state blsInverseVHalfLoop).2) at hn
  rw [hr] at hn
  rcases hn with ht | ⟨_, r, y, k, hcounter, hcoeff, _, _, hrest⟩
  · cases ht
  · refine ⟨BlsInverseLocals.mk q.u r q.x1 y, ?_⟩
    exact ⟨(hrest _ (by decide) (by decide)).trans hu, hcounter, (hrest _ (by decide) (by decide)).trans hx1, hcoeff⟩

theorem blsInverseSubtractTail_bound : TerminatingProgBounded blsInverseSubtractTail blsInverseTailCost := by
  unfold blsInverseSubtractTail blsSubUpdate blsInverseTailCost
  exact TerminatingProgBounded.decCall ub_bls_fp_lt_raw _ _ _
    (TerminatingProgBounded.ite
      (TerminatingProgBounded.decCall ub_bls_fp_sub_raw _ _ _
        (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
          (TerminatingProgBounded.call ub_bls_fp_sub _ _)))
      (TerminatingProgBounded.decCall ub_bls_fp_sub_raw _ _ _
        (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
          (TerminatingProgBounded.call ub_bls_fp_sub _ _))))

theorem blsInverseOuterBody_bound : TerminatingProgBoundedOn blsInverseTyped blsInverseOuterBody blsInverseBodyCost := by
  rw [blsInverseOuterBody_eq]
  have htail : TerminatingProgBoundedOn blsInverseTyped blsInverseSubtractTail blsInverseTailCost :=
    fun state hc _ => blsInverseSubtractTail_bound state hc
  have hv : TerminatingProgBoundedOn blsInverseTyped (.seq blsInverseVHalfLoop blsInverseSubtractTail) (blsInverseHalfCost + blsInverseTailCost) := TerminatingProgBoundedOn.seq_on_none blsInverseVHalf_bound blsInverseVHalf_preserves_none htail
  have hu : TerminatingProgBoundedOn blsInverseTyped (.seq blsInverseUHalfLoop (.seq blsInverseVHalfLoop blsInverseSubtractTail)) (blsInverseHalfCost + (blsInverseHalfCost + blsInverseTailCost)) := TerminatingProgBoundedOn.seq_on_none blsInverseUHalf_bound blsInverseUHalf_preserves_none hv
  have hcheck (c x : MlS) : TerminatingProgBoundedOn blsInverseTyped (blsInverseExitCheck c x) 0 :=
    fun state hc _ => TerminatingProgBounded.straight _ rfl state hc
  have hpres (c x : MlS) {F : Type} (state post : PanSemStateFiniteExact 64 F)
      (_ : state.code = originalRuntimeCode) (hp : blsInverseTyped state)
      (hr : evaluateHOLFiniteState state (blsInverseExitCheck c x) = (none, post)) : blsInverseTyped post := by
    rw [blsInverseExitCheck_passive c x state post hr]
    exact hp
  have h : TerminatingProgBoundedOn blsInverseTyped
      (.seq (blsInverseExitCheck (ofString "u") (ofString "x1"))
        (.seq (blsInverseExitCheck (ofString "v") (ofString "x2"))
          (.seq blsInverseUHalfLoop (.seq blsInverseVHalfLoop blsInverseSubtractTail))))
      (0 + (0 + (blsInverseHalfCost + (blsInverseHalfCost + blsInverseTailCost)))) := TerminatingProgBoundedOn.seq_on_none (hcheck (ofString "u") (ofString "x1"))
    (hpres _ _) (TerminatingProgBoundedOn.seq_on_none (hcheck (ofString "v") (ofString "x2")) (hpres _ _) hu)
  intro F state hc hp
  simpa only [Nat.zero_add, blsInverseBodyCost, Nat.add_assoc] using h state hc hp
end InitECandidate.Solver.Wave8GuestInv.Arith
