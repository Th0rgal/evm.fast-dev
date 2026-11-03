import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ReturnedFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem arith_dec_returned_state {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64} {ret : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.dec name shape init body) = (some (.returned ret),post)) :
    ∃ (value : ValueHOL 64) (inner : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) init = some value ∧
      shapeEqHOL shape (shapeOfHOLExact value) = true ∧
      evaluateHOLFiniteState (setVarHOLFinite name value s) body = (some (.returned ret),inner) ∧
      post = {inner with locals := HolFiniteMapExact.resVarEq inner.locals (name,s.locals.lookup name)} := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · simp at hr
  · rename_i value he
    split at hr
    · rename_i hs
      exact ⟨value,_,he,hs,Prod.ext (Prod.mk.inj hr).1 rfl,(Prod.mk.inj hr).2.symm⟩
    · simp at hr

end InitECandidate.Solver.Wave8GuestInv.Arith
