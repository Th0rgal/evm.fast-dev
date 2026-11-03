import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.TailReturnedFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem arith_tailCall_not_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call none fn args)).1 ≠
      none := by
  rw [evaluateHOLFiniteState_call]
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => simp
  | some vals =>
    dsimp only
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => simp
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      dsimp only
      split
      · simp
      · cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals simp only
          all_goals first | (solve | simp_all) | (split <;> first | (solve | simp_all) | (split <;> simp_all))

end InitECandidate.Solver.Wave8GuestInv.Arith
