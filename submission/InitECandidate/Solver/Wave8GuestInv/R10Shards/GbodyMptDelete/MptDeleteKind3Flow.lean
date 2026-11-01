import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Value

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptSeq_none {F : Type} {s t : PanSemStateFiniteExact 64 F} {p q : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.seq p q) = (none, t)) :
    ∃ mid, evaluateHOLFiniteState s p = (none, mid) ∧ evaluateHOLFiniteState mid q = (none, t) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases hp : evaluateHOLFiniteState s p with ⟨r, mid⟩
  rw [hp] at hr
  cases r with
  | none => exact ⟨mid, rfl, hr⟩
  | some r => cases hr

theorem mptDec_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.dec name shape init body) = (none, t)) :
    ∃ v inner, evalAt s init = some v ∧
      evaluateHOLFiniteState (setVarHOLFinite name v s) body = (none, inner) ∧
      t = { inner with locals := HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i v hv
    split at hr
    · rcases hb : evaluateHOLFiniteState (setVarHOLFinite name v s) body with ⟨r, inner⟩
      simp only [hb] at hr
      obtain ⟨rfl, heq⟩ := Prod.mk.inj hr
      exact ⟨v, inner, hv, hb, heq.symm⟩
    · cases hr

theorem mptDecCall_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name fname : MlS} {shape : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.decCall name shape fname args cont) = (none, t)) :
    ∃ values body callee ret v post inner,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) ∧
      evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) cont = (none, inner) ∧
      t = { inner with locals := HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp only [ha] at hr
    cases hr
  · simp only [ha] at hr
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hr
      cases hr
    · simp only [hl] at hr
      split at hr
      · cases hr
      · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        simp only [hb] at hr
        cases r with
        | none => cases hr
        | some r =>
          cases r with
          | returned v =>
            simp only at hr
            split at hr
            · rcases hcont : evaluateHOLFiniteState
                (setVarHOLFinite name v { post with locals := s.locals }) cont with ⟨r, inner⟩
              simp only [hcont] at hr
              obtain ⟨rfl, heq⟩ := Prod.mk.inj hr
              exact ⟨values, body, callee, ret, v, post, inner, rfl, hl, hb, hcont, heq.symm⟩
            · cases hr
          | _ => cases hr

theorem mptValid_word_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : MlS} {w : BitVec 64}
    (h : isValidValueHOLExact s.toExact .local name (.val (.word w)) = true) :
    ∃ old : BitVec 64, s.locals.lookup name = some (.val (.word old)) := by
  simp only [isValidValueHOLExact, lookupKvarHOLExact] at h
  rcases hl : s.locals.lookup name with _ | v
  · rw [hl] at h
    cases h
  · rw [hl] at h
    cases v with
    | val v => cases v with | word old => exact ⟨old, rfl⟩
    | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
    | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

theorem mptAssign_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : MlS} {source : ExpHOL 64}
    (hr : evaluateHOLFiniteState s (.assign .local name source) = (none, t)) :
    ∃ v, evalAt s source = some v ∧
      isValidValueHOLExact s.toExact .local name v = true ∧
      t = setVarHOLFinite name v s := by
  rw [evaluateHOLFiniteState_assign] at hr
  split at hr
  · cases hr
  · rename_i v hv
    split at hr
    · rename_i hvalid
      exact ⟨v, hv, hvalid, (Prod.mk.inj hr).2.symm⟩
    · cases hr

 theorem mptStore_locals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {dst src : ExpHOL 64}
    (hr : evaluateHOLFiniteState s (.store dst src) = (none, t)) : t.locals = s.locals := by
  have h := (evaluate_store_control_frame s dst src).2.1
  simpa only [hr] using h

theorem mptIte_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.ite cond yes no) = (none, t)) :
    (CondTrue cond s ∧ evaluateHOLFiniteState s yes = (none, t)) ∨
      (CondFalse cond s ∧ evaluateHOLFiniteState s no = (none, t)) := by
  rw [evaluateHOLFiniteState_ite] at hr
  split at hr
  · rename_i w hw
    split at hr
    · rename_i hz
      subst w
      exact Or.inr ⟨hw, hr⟩
    · rename_i hz
      exact Or.inl ⟨⟨w, hw, hz⟩, hr⟩
  · cases hr

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
