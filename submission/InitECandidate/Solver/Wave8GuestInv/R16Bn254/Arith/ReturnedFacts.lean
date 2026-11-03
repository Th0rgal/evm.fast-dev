import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256CallFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem arith_decCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {ret : ValueHOL 64} {name fn : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.decCall name sh fn args cont) = (some (.returned ret), post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) sh = true ∧
      resumed.locals = s.locals.update (name, w) ∧
      resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (some (.returned ret), inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) := by
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
              Prod.ext he rfl, by rw [← hp]⟩
          · simp at h

theorem arith_seq_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {first second : ProgHOL 64} {ret : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.seq first second) = (some (.returned ret), post)) :
    evaluateHOLFiniteState s first = (some (.returned ret), post) ∨
      ∃ mid : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState s first = (none, mid) ∧
        evaluateHOLFiniteState mid second = (some (.returned ret), post) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hf : evaluateHOLFiniteState s first with ⟨res, mid⟩
  rw [hf] at hr
  cases res with
  | none => exact Or.inr ⟨mid, rfl, hr⟩
  | some res =>
    dsimp only at hr
    exact Or.inl hr

theorem arith_dec_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64} {ret : ValueHOL 64}
    (hr : evaluateHOLFiniteState s (.dec name shape init body) = (some (.returned ret), post)) :
    ∃ value : ValueHOL 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) init = some value ∧
      shapeEqHOL shape (shapeOfHOLExact value) = true ∧
      ∃ inner : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState (setVarHOLFinite name value s) body = (some (.returned ret), inner) := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · simp at hr
  · rename_i value he
    split at hr
    · rename_i hs
      exact ⟨value, he, hs, _, Prod.ext (Prod.mk.inj hr).1 rfl⟩
    · simp at hr

end InitECandidate.Solver.Wave8GuestInv.Arith
