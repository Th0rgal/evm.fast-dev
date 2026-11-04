import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModSubExact
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseSubtractTail

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem arith_ite_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {guard : ExpHOL 64} {yes no : ProgHOL 64} {ret : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.ite guard yes no) = (some (.returned ret), post)) :
    evaluateHOLFiniteState s yes = (some (.returned ret), post) ∨
      evaluateHOLFiniteState s no = (some (.returned ret), post) := by
  rw [evaluateHOLFiniteState_ite] at hr
  split at hr
  · split at hr
    · exact Or.inr hr
    · exact Or.inl hr
  · cases hr

theorem arith_seq_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (ret : ValueHOL 64)
    (hf : (evaluateHOLFiniteState s first).1 ≠ some (.returned ret))
    (hs : ∀ mid : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState mid second).1 ≠ some (.returned ret)) :
    (evaluateHOLFiniteState s (.seq first second)).1 ≠ some (.returned ret) := by
  intro hr
  have he : evaluateHOLFiniteState s (.seq first second) =
      (some (.returned ret), (evaluateHOLFiniteState s (.seq first second)).2) := Prod.ext hr rfl
  rcases arith_seq_returned he with hf' | ⟨mid, _, hs'⟩
  · exact hf (congrArg Prod.fst hf')
  · exact hs mid (congrArg Prod.fst hs')

theorem inverseSubtractTail_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ret : ValueHOL 64) :
    (evaluateHOLFiniteState s inverseSubtractTail).1 ≠ some (.returned ret) := by
  intro hr
  have he : evaluateHOLFiniteState s inverseSubtractTail =
      (some (.returned ret), (evaluateHOLFiniteState s inverseSubtractTail).2) := Prod.ext hr rfl
  unfold inverseSubtractTail at he
  obtain ⟨_, _, _, _, _, _, resumed, inner, _, _, _, _, _, _, _, hcont, _⟩ := arith_decCall_returned he
  rcases arith_ite_returned hcont with hy | hn
  · exact arith_seq_not_returned resumed _ _ ret
      (arith_call_local_not_returned resumed _ _ _ ret)
      (fun mid => arith_call_local_not_returned mid _ _ _ ret) (congrArg Prod.fst hy)
  · exact arith_seq_not_returned resumed _ _ ret
      (arith_call_local_not_returned resumed _ _ _ ret)
      (fun mid => arith_call_local_not_returned mid _ _ _ ret) (congrArg Prod.fst hn)

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
