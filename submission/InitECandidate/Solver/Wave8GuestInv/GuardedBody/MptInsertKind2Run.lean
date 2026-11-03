import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2Support

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open RunFramesRace (evalAt)

theorem seq_none {F : Type} {s t : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.seq a b) = (none, t)) :
    ∃ m, evaluateHOLFiniteState s a = (none, m) ∧
      evaluateHOLFiniteState m b = (none, t) := by
  rw [evaluateHOLFiniteState_seq_line780] at hr
  rcases he : evaluateHOLFiniteState s a with ⟨r, m⟩
  cases r with
  | none => exact ⟨m, rfl, by simpa only [he] using hr⟩
  | some r => simp only [he] at hr; cases hr

theorem dec_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.dec name shape init body) = (none, t)) :
    ∃ v u, evalAt s init = some v ∧
      evaluateHOLFiniteState (setVarHOLFinite name v s) body = (none, u) ∧
      t = { u with locals := HolFiniteMapExact.resVarEq u.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i v hv
    split at hr
    · have he := congrArg Prod.fst hr
      have ht := congrArg Prod.snd hr
      refine ⟨v, (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2, hv, ?_, ht.symm⟩
      exact Prod.ext he rfl
    · cases hr

theorem assign_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {kind : VarKind} {name : MlS} {e : ExpHOL 64}
    (hr : evaluateHOLFiniteState s (.assign kind name e) = (none, t)) :
    ∃ v, evalAt s e = some v ∧ t = setKvarHOLFinite kind name v s := by
  rw [evaluateHOLFiniteState_assign] at hr
  split at hr
  · cases hr
  · rename_i v hv
    split at hr
    · exact ⟨v, hv, (congrArg Prod.snd hr).symm⟩
    · cases hr

theorem ite_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.ite cond yes no) = (none, t)) :
    (CondTrue cond s ∧ evaluateHOLFiniteState s yes = (none, t)) ∨
    (CondFalse cond s ∧ evaluateHOLFiniteState s no = (none, t)) := by
  rw [evaluateHOLFiniteState_ite] at hr
  split at hr
  · rename_i w hw
    split at hr
    · rename_i hz
      exact Or.inr ⟨by simpa only [CondFalse, hz] using hw, hr⟩
    · rename_i hz
      exact Or.inl ⟨⟨w, hw, hz⟩, hr⟩
  · cases hr

/-- A normal handler-free call necessarily obtained a normal callee return. -/
theorem call_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {dest : Option (VarKind × MlS)} {fname : MlS} {args : List (ExpHOL 64)}
    (hr : evaluateHOLFiniteState s (.call (some (dest, none)) fname args) = (none, t)) :
    ∃ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) ∧
      t = (match dest with
        | none => { post with locals := s.locals }
        | some (kind, name) => setKvarHOLFinite kind name v { post with locals := s.locals }) := by
  rw [evaluateHOLFiniteState_call] at hr
  split at hr
  · cases hr
  · rename_i values hv
    split at hr
    · cases hr
    · rename_i body callee ret hl
      split at hr
      · cases hr
      · rcases he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        simp only [he] at hr
        cases r with
        | none => cases hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr
            split at hr
            · cases dest with
              | none => exact ⟨values, body, callee, ret, v, post, hv, hl, he, (congrArg Prod.snd hr).symm⟩
              | some d =>
                rcases d with ⟨kind, name⟩
                dsimp only at hr
                split at hr
                · exact ⟨values, body, callee, ret, v, post, hv, hl, he, (congrArg Prod.snd hr).symm⟩
                · cases hr
            · cases hr
          | exception e v => cases hr
          | _ => cases hr

theorem decCall_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.decCall name shape fname args cont) = (none, t)) :
    ∃ values body callee ret v post u,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) ∧
      evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) cont = (none, u) ∧
      t = { u with locals := HolFiniteMapExact.resVarEq u.locals (name, s.locals.lookup name) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
  split at hr
  · cases hr
  · rename_i values hv
    split at hr
    · cases hr
    · rename_i body callee ret hl
      split at hr
      · cases hr
      · rcases he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        simp only [he] at hr
        cases r with
        | none => cases hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr
            split at hr
            · refine ⟨values, body, callee, ret, v, post,
                (evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) cont).2,
                hv, hl, he, ?_, (congrArg Prod.snd hr).symm⟩
              have hfirst := congrArg Prod.fst hr
              exact Prod.ext hfirst rfl
            · cases hr
          | _ => cases hr

def NoContinue (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    (evaluateHOLFiniteState s p).1 ≠ some .continue

theorem NoContinue.seq {a b : ProgHOL 64} (ha : NoContinue a) (hb : NoContinue b) :
    NoContinue (.seq a b) := by
  intro F s
  rw [evaluateHOLFiniteState_seq_line780]
  rcases he : evaluateHOLFiniteState s a with ⟨r, m⟩
  cases r with
  | none => exact hb m
  | some r => simpa only [he] using ha s

theorem NoContinue.dec {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hb : NoContinue body) : NoContinue (.dec name shape init body) := by
  intro F s
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · exact hb _
    · simp

theorem NoContinue.ite {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hy : NoContinue yes) (hn : NoContinue no) : NoContinue (.ite cond yes no) := by
  intro F s
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s
    · exact hy s
  · simp

theorem NoContinue.assign (kind : VarKind) (name : MlS) (e : ExpHOL 64) :
    NoContinue (.assign kind name e) := by
  intro F s
  rw [evaluateHOLFiniteState_assign]
  split
  · simp
  · split <;> simp

theorem NoContinue.store (a v : ExpHOL 64) : NoContinue (.store a v) := by
  intro F s
  rcases (InitECandidate.Solver.PanRunBounded.evaluate_store_control_frame s a v).1 with h | h <;>
    (intro he; rw [h] at he; cases he)

theorem NoContinue.skip : NoContinue .skip := by
  intro F s
  simp [evaluateHOLFiniteState_skip]

theorem NoContinue.call (dest : Option (VarKind × MlS)) (fname : MlS) (args : List (ExpHOL 64)) :
    NoContinue (.call (some (dest, none)) fname args) := by
  intro F s
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · rename_i body callee ret hl
      split
      · simp
      · rcases he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        simp only [he]
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · cases dest with
              | none => simp
              | some d => rcases d with ⟨kind, name⟩; dsimp only; split <;> simp
            · simp
          | _ => simp

theorem NoContinue.decCall {name : MlS} {shape : ShapeHOL} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64} (hc : NoContinue cont) :
    NoContinue (.decCall name shape fname args cont) := by
  intro F s
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · simp
  · split
    · simp
    · rename_i body callee ret hl
      split
      · simp
      · rcases he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        simp only [he]
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · exact hc _
            · simp
          | _ => simp

theorem insert_noContinue : NoContinue mptInsertBody := by
  simp only [mptInsertBody, mptInsertTail, mptInsertCode, mptDecBody, mptLeft,
    mptWhileBody, sourceFunctionEntry, Guest.Software.guestFn__mpt_insert_node,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  repeat' first
    | apply NoContinue.seq
    | apply NoContinue.ite
    | apply NoContinue.dec
    | apply NoContinue.decCall
    | exact NoContinue.call _ _ _
    | exact NoContinue.assign _ _ _
    | exact NoContinue.store _ _
    | exact NoContinue.skip

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
