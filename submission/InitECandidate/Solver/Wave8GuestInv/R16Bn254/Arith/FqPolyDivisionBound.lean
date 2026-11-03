import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionInvariant
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyLeaves

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def polyDivisionBodyCost : Nat :=
  K.fq_mul + (0 + ((K.fq_poly_submul+1) + (K.fq_poly_deg+1))) + 1

theorem polyDivBody_bounded : TerminatingProgBoundedOn GuestInv polyDivBody polyDivisionBodyCost := by
  exact TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
    (TerminatingProgBoundedOn.decCall_guestInv (TerminatingFunBoundedOn.of_unconditional ub_fq_mul) _ _ _
      (TerminatingProgBoundedOn.seq_guestInv
        (fun s hc _ => TerminatingProgBounded.straight _ rfl s hc)
        (TerminatingProgBoundedOn.seq_guestInv
          (TerminatingProgBoundedOn.call_guestInv fb_fq_poly_submul _ _)
          (TerminatingProgBoundedOn.call_guestInv fb_fq_poly_deg _ _))))

theorem polyDivInvariant_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (inverse : Limbs256)
    (h : PolyDivInvariant a b quotient d1 B inverse s) :
    PolyDivInvariant a b quotient d1 B inverse (decClockHOLFinite s) := by
  rcases h with ⟨hr0,hr1,hq,hd1,hi,hdA,hdB,hdQ,hmB,hd⟩
  exact ⟨hr0,hr1,hq,hd1,hi,hdA,hdB,hdQ,hmB,hd⟩

/-- Conditional clock bound for the actual source inner division loop, using
only the permitted rank combinator and already certified callee bounds. -/
theorem polyDivLoop_bounded (a b quotient : BitVec 64) (d1 : Nat)
    (B : Nat → Limbs256) (inverse : Limbs256) (ctx : PolyDivContext a b quotient d1 B inverse) :
    TerminatingProgBoundedOn
      (fun s => GuestInv s ∧ PolyDivInvariant a b quotient d1 B inverse s)
      polyDivLoop (14 * (polyDivisionBodyCost + 1)) := by
  let P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧ PolyDivInvariant a b quotient d1 B inverse s
  have hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s) := by
    intro F s hp
    exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hp.1,
      polyDivInvariant_decClock s a b quotient d1 B inverse hp.2⟩
  have hs : LoopStep polyDivisionRank polyDivGuard polyDivBody polyDivisionBodyCost P := by
    apply while_step_of_progBoundedOn P polyDivisionRank polyDivGuard
      (fun s hc hp => polyDivBody_bounded s hc hp.1) hentry
    intro F s word hc hp hcond hnz hclock
    dsimp only
    intro hflow
    have hn : (evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody).1 = none :=
      hflow.resolve_right (evaluate_noTopContinue polyDivBody (by decide) (decClockHOLFinite s))
    have hr : evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody =
        (none,(evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody).2) := Prod.ext hn rfl
    have hprogress := polyDivBody_invariant (decClockHOLFinite s)
      (evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody).2 a b quotient d1 B inverse ctx hc
      (hentry s hp).2 word hcond hnz hr
    exact ⟨hprogress.1,
      guestInv_evaluate (decClockHOLFinite s) polyDivBody (hentry s hp).1,hprogress.2.1⟩
  intro F s hc hp
  exact TerminatingProgBoundedOn.while_measure (n := 13) polyDivisionRank polyDivGuard polyDivBody hs
    s hc ⟨hp,polyDivInvariant_rank_bound s a b quotient d1 B inverse hp.2⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
