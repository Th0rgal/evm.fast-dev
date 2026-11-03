import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.InverseBodyStep
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

def inverseTyped {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ q : InverseLocals, q.Matches s

def inverseHalfCost : Nat := (2 ^ 8 + 1) * ((K.mod_half + 1) + 1)
def inverseTailCost : Nat := (K.u256_lt + 1) + (K.u256_sub + 1) + (K.mod_sub + 1)
def inverseBodyCost : Nat := inverseHalfCost + inverseHalfCost + inverseTailCost

theorem inverseUHalf_bound : TerminatingProgBoundedOn inverseTyped inverseUHalfLoop inverseHalfCost := by
  intro F state hc hp
  obtain ⟨q, hu, hv, hx1, hx2, hm⟩ := hp
  exact while_inverse_half_typed (ofString "u") (ofString "x1")
    (by decide) (by decide) (by decide) state hc ⟨q.u, q.x1, q.m, hu, hx1, hm⟩

theorem inverseUHalf_preserves_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (hc : state.code = originalRuntimeCode) (hp : inverseTyped state)
    (hr : evaluateHOLFiniteState state inverseUHalfLoop = (none, post)) : inverseTyped post := by
  obtain ⟨q, hu, hv, hx1, hx2, hm⟩ := hp
  have hn := inverse_half_normalizes (ofString "u") (ofString "x1")
    (by decide) (by decide) (by decide) state q.u q.x1 q.m hc hu hx1 hm
  change (evaluateHOLFiniteState state inverseUHalfLoop).1 = some .timeOut ∨
    ((evaluateHOLFiniteState state inverseUHalfLoop).1 = none ∧
      HalfNormalPost (ofString "u") (ofString "x1") state q.u (evaluateHOLFiniteState state inverseUHalfLoop).2) at hn
  rw [hr] at hn
  rcases hn with ht | ⟨_, r, y, k, hcounter, hcoeff, _, _, hrest⟩
  · cases ht
  · refine ⟨InverseLocals.mk r q.v y q.x2 q.m, ?_⟩
    exact ⟨hcounter, (hrest _ (by decide) (by decide)).trans hv, hcoeff, (hrest _ (by decide) (by decide)).trans hx2, (hrest _ (by decide) (by decide)).trans hm⟩

theorem inverseVHalf_bound : TerminatingProgBoundedOn inverseTyped inverseVHalfLoop inverseHalfCost := by
  intro F state hc hp
  obtain ⟨q, hu, hv, hx1, hx2, hm⟩ := hp
  exact while_inverse_half_typed (ofString "v") (ofString "x2")
    (by decide) (by decide) (by decide) state hc ⟨q.v, q.x2, q.m, hv, hx2, hm⟩

theorem inverseVHalf_preserves_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (hc : state.code = originalRuntimeCode) (hp : inverseTyped state)
    (hr : evaluateHOLFiniteState state inverseVHalfLoop = (none, post)) : inverseTyped post := by
  obtain ⟨q, hu, hv, hx1, hx2, hm⟩ := hp
  have hn := inverse_half_normalizes (ofString "v") (ofString "x2")
    (by decide) (by decide) (by decide) state q.v q.x2 q.m hc hv hx2 hm
  change (evaluateHOLFiniteState state inverseVHalfLoop).1 = some .timeOut ∨
    ((evaluateHOLFiniteState state inverseVHalfLoop).1 = none ∧
      HalfNormalPost (ofString "v") (ofString "x2") state q.v (evaluateHOLFiniteState state inverseVHalfLoop).2) at hn
  rw [hr] at hn
  rcases hn with ht | ⟨_, r, y, k, hcounter, hcoeff, _, _, hrest⟩
  · cases ht
  · refine ⟨InverseLocals.mk q.u r q.x1 y q.m, ?_⟩
    exact ⟨(hrest _ (by decide) (by decide)).trans hu, hcounter, (hrest _ (by decide) (by decide)).trans hx1, hcoeff, (hrest _ (by decide) (by decide)).trans hm⟩

theorem inverseSubtractTail_bound : TerminatingProgBounded inverseSubtractTail inverseTailCost := by
  have h : TerminatingProgBounded inverseSubtractTail
      ((K.u256_lt + 1) + max ((K.u256_sub + 1) + (K.mod_sub + 1))
        ((K.u256_sub + 1) + (K.mod_sub + 1))) := by
    unfold inverseSubtractTail
    exact TerminatingProgBounded.decCall ub_u256_lt _ _ _
      (TerminatingProgBounded.ite
        (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_u256_sub _ _)
          (TerminatingProgBounded.call ub_mod_sub _ _))
        (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_u256_sub _ _)
          (TerminatingProgBounded.call ub_mod_sub _ _)))
  intro F state hc
  simpa only [inverseTailCost, Nat.max_self, Nat.add_assoc] using h state hc

theorem inverseOuterBody_bound : TerminatingProgBoundedOn inverseTyped inverseOuterBody inverseBodyCost := by
  rw [inverseOuterBody_eq]
  have htail : TerminatingProgBoundedOn inverseTyped inverseSubtractTail inverseTailCost :=
    fun state hc _ => inverseSubtractTail_bound state hc
  have hv : TerminatingProgBoundedOn inverseTyped (.seq inverseVHalfLoop inverseSubtractTail) (inverseHalfCost + inverseTailCost) := TerminatingProgBoundedOn.seq_on_none inverseVHalf_bound inverseVHalf_preserves_none htail
  have hu : TerminatingProgBoundedOn inverseTyped (.seq inverseUHalfLoop (.seq inverseVHalfLoop inverseSubtractTail)) (inverseHalfCost + (inverseHalfCost + inverseTailCost)) := TerminatingProgBoundedOn.seq_on_none inverseUHalf_bound inverseUHalf_preserves_none hv
  have hcheck (c x : MlS) : TerminatingProgBoundedOn inverseTyped (inverseExitCheck c x) 0 :=
    fun state hc _ => TerminatingProgBounded.straight _ rfl state hc
  have hpres (c x : MlS) {F : Type} (state post : PanSemStateFiniteExact 64 F)
      (_ : state.code = originalRuntimeCode) (hp : inverseTyped state)
      (hr : evaluateHOLFiniteState state (inverseExitCheck c x) = (none, post)) : inverseTyped post := by
    rw [inverseExitCheck_passive c x state post hr]
    exact hp
  have h : TerminatingProgBoundedOn inverseTyped
      (.seq (inverseExitCheck (ofString "u") (ofString "x1"))
        (.seq (inverseExitCheck (ofString "v") (ofString "x2"))
          (.seq inverseUHalfLoop (.seq inverseVHalfLoop inverseSubtractTail))))
      (0 + (0 + (inverseHalfCost + (inverseHalfCost + inverseTailCost)))) := TerminatingProgBoundedOn.seq_on_none (hcheck (ofString "u") (ofString "x1"))
    (hpres _ _) (TerminatingProgBoundedOn.seq_on_none (hcheck (ofString "v") (ofString "x2")) (hpres _ _) hu)
  intro F state hc hp
  simpa only [Nat.zero_add, inverseBodyCost, Nat.add_assoc] using h state hc hp
end InitECandidate.Solver.Wave8GuestInv.Arith
