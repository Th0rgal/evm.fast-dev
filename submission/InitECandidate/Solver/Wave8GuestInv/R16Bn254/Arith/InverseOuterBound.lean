import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseBodyBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def inverseLocalNat (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]) =>
    (Limbs256.mk a b c d).toNat
  | _ => 0

def inverseStateRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  inverseRank (inverseLocalNat (ofString "u") s) (inverseLocalNat (ofString "v") s)

theorem inverseStateRank_matches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (q : InverseLocals) (hq : q.Matches s) :
    inverseStateRank s = inverseRank q.u.toNat q.v.toNat := by
  simp [inverseStateRank, inverseLocalNat, hq.1, hq.2.1, Limbs256.toValue]

/-- The actual binary-inverse outer loop has the proposed cap for typed locals. -/
theorem inverseOuterLoop_bound : TerminatingProgBoundedOn inverseTyped inverseOuterLoop
    ((513 + 1) * (inverseBodyCost + 1)) := by
  have hs : LoopStep inverseStateRank (.const 1) inverseOuterBody inverseBodyCost inverseTyped := by
    apply while_step_of_progBoundedOn inverseTyped inverseStateRank _ inverseOuterBody_bound
      (fun _ hp => hp)
    intro F state word hc hp _ _ _
    dsimp only
    intro hflow
    rcases hflow with hn | hcontinue
    · obtain ⟨q, hq⟩ := hp
      have hr : evaluateHOLFiniteState (decClockHOLFinite state) inverseOuterBody =
          (none, (evaluateHOLFiniteState (decClockHOLFinite state) inverseOuterBody).2) :=
        Prod.ext hn rfl
      obtain ⟨r, hmatch, hdrop⟩ := inverseOuterBody_none (s := decClockHOLFinite state) q hc hq hr
      refine ⟨?_, r, hmatch⟩
      rw [inverseStateRank_matches _ r hmatch, inverseStateRank_matches state q hq]
      exact hdrop
    · exact False.elim (inverseOuterBody_not_continue _ hcontinue)
  rw [inverseOuterLoop_eq]
  intro F state hc hp
  apply TerminatingProgBoundedOn.while_measure inverseStateRank _ _ hs state hc
  refine ⟨hp, ?_⟩
  obtain ⟨q, hq⟩ := hp
  rw [inverseStateRank_matches state q hq]
  exact inverseRank_256_le q.u q.v

end InitECandidate.Solver.Wave8GuestInv.Arith
