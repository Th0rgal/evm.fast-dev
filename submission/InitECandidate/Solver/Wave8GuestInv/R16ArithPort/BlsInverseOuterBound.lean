import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsInverseBodyBound

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def blsInverseLocalNat (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d), .val (.word e), .val (.word f)]) =>
    (Limbs384.mk a b c d e f).toNat
  | _ => 0

def blsInverseStateRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  tightInverseRank (blsInverseLocalNat (ofString "u") s) (blsInverseLocalNat (ofString "v") s)

theorem blsInverseStateRank_matches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (q : BlsInverseLocals) (hq : q.Matches s) :
    blsInverseStateRank s = tightInverseRank q.u.toNat q.v.toNat := by
  simp [blsInverseStateRank, blsInverseLocalNat, hq.1, hq.2.1, Limbs384.toValue]

/-- The actual binary-inverse outer loop has the proposed cap for typed locals. -/
theorem blsInverseOuterLoop_bound : TerminatingProgBoundedOn blsInverseTyped blsInverseOuterLoop
    ((769 + 1) * (blsInverseBodyCost + 1)) := by
  have hs : LoopStep blsInverseStateRank (.const 1) blsInverseOuterBody blsInverseBodyCost blsInverseTyped := by
    apply while_step_of_progBoundedOn blsInverseTyped blsInverseStateRank _ blsInverseOuterBody_bound
      (fun _ hp => hp)
    intro F state word hc hp _ _ _
    dsimp only
    intro hflow
    rcases hflow with hn | hcontinue
    · obtain ⟨q, hq⟩ := hp
      have hr : evaluateHOLFiniteState (decClockHOLFinite state) blsInverseOuterBody =
          (none, (evaluateHOLFiniteState (decClockHOLFinite state) blsInverseOuterBody).2) :=
        Prod.ext hn rfl
      obtain ⟨r, hmatch, hdrop⟩ := blsInverseOuterBody_none (s := decClockHOLFinite state) q hc hq hr
      refine ⟨?_, r, hmatch⟩
      rw [blsInverseStateRank_matches _ r hmatch, blsInverseStateRank_matches state q hq]
      exact hdrop
    · exact False.elim (blsInverseOuterBody_not_continue _ hcontinue)
  rw [blsInverseOuterLoop_eq]
  intro F state hc hp
  apply TerminatingProgBoundedOn.while_measure blsInverseStateRank _ _ hs state hc
  refine ⟨hp, ?_⟩
  obtain ⟨q, hq⟩ := hp
  rw [blsInverseStateRank_matches state q hq]
  exact tightInverseRank_limbs384_le q.u q.v
end InitECandidate.Solver.Wave8GuestInv.Arith
