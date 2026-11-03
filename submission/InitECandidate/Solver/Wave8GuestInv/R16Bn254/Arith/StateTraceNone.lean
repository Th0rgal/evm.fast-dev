import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256CallFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem arith_decCall_none_state {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name fn : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.decCall name sh fn args cont) = (none, post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) sh = true ∧
      resumed.locals = s.locals.update (name, w) ∧
      resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) ∧
      resumed = setVarHOLFinite name w { bpost with locals := s.locals } ∧
      post = { inner with locals := HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_decCall_total] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vals =>
    rw [hargs] at h; dsimp only at h
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => rw [hlk] at h; simp at h
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      rw [hlk] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i hclk
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h hrem hmeta
          dsimp only at hmeta hrem
          have hfix : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, bpost) = (r1, bpost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
          rw [hfix] at h; dsimp only at h
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp at h; done) | skip
          simp only [] at h
          split at h
          · rename_i hboth
            obtain ⟨he, hp⟩ := Prod.mk.inj h
            have hsh : shapeEqHOL (shapeOfHOLExact w) sh = true := by
              simp [Bool.and_eq_true] at hboth; exact hboth.1
            let resumed : PanSemStateFiniteExact 64 F := setVarHOLFinite name w { bpost with locals := s.locals }
            let inner : PanSemStateFiniteExact 64 F := (evaluateHOLFiniteState resumed cont).2
            refine ⟨vals, body, callee, rs, w, bpost, resumed, inner, rfl, hlk, hclk, hrun, hsh, rfl, hmeta,
              Prod.ext he rfl, (by rw [← hp]), rfl, hp.symm⟩
          · simp at h

/-- A successful scoped declaration exposes the exact restored post-state. -/
theorem arith_dec_none_state {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.dec name shape init body) = (none, post)) :
    ∃ (value : ValueHOL 64) (inner : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) init = some value ∧
      shapeEqHOL shape (shapeOfHOLExact value) = true ∧
      evaluateHOLFiniteState (setVarHOLFinite name value s) body = (none, inner) ∧
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
