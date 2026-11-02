import InitECandidate.Solver.Wave8GuestInv.Defs
import Guest.SoftwareAst

/-! Shared definitions and read-only evaluation engine for contract micro-shard `m17`
(`wave8/contracts-m17`, frozen spec rev9 `8a79d9f28`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.Defs` and
`Guest.SoftwareAst` (never the monolithic `GuestInv` or heavy `Contracts` during iteration).
Restates `FunSpec`, `Resumes`, and `ReadOnlyFn` verbatim from `GuestInv.lean` @ `8a79d9f28`,
and proves a syntactic + compositional read-only engine covering straight-line, loop, `call`,
and `decCall` read-only functions.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 1200000

namespace InitECandidate.Solver.Wave8GuestInv.M17

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim rev9 contract interface (`GuestInv.lean` @ `8a79d9f28`) -/

def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

/-! ## 2. Unconditional frame predicate `SameFrame` -/

/-- `post` agrees with `s` on every field except possibly `locals` and `clock`. -/
def SameFrame {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  post = { s with locals := post.locals, clock := post.clock }

theorem SameFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : SameFrame s s := by
  cases s; rfl

theorem SameFrame.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    (hab : SameFrame a b) (hbc : SameFrame b c) : SameFrame a c := by
  unfold SameFrame at hab hbc ⊢
  rw [hbc, hab]

theorem SameFrame.with_locals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameFrame s post) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    SameFrame s { post with locals := locals } := by
  unfold SameFrame at h ⊢
  rw [h]

theorem SameFrame.emptyLocals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameFrame s post) : SameFrame s (emptyLocalsHOLFinite post) := by
  unfold SameFrame at h ⊢
  unfold emptyLocalsHOLFinite
  rw [h]

theorem SameFrame.setVar {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameFrame s post) (name : MlS) (v : ValueHOL 64) :
    SameFrame s (setVarHOLFinite name v post) := by
  unfold SameFrame at h ⊢
  unfold setVarHOLFinite
  rw [h]

theorem SameFrame.decClock {F : Type} {s : PanSemStateFiniteExact 64 F} :
    SameFrame s (decClockHOLFinite s) := by
  cases s; rfl

theorem SameFrame.callEntry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) :
    SameFrame s (callEntryStateHOLFinite s callee) := by
  cases s; rfl

theorem SameFrame.fixClock {F : Type} {s entry post : PanSemStateFiniteExact 64 F}
    (r : Option (PanSemResultExact 64)) (h : SameFrame s post) :
    SameFrame s (fixClockHOLFinite entry (r, post)).2 := by
  unfold fixClockHOLFinite
  dsimp only
  split
  · unfold SameFrame at h ⊢
    rw [h]
  · exact h

theorem SameFrame.code_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameFrame s post) : post.code = s.code := by
  unfold SameFrame at h
  rw [h]

/-! ## 3. Syntactic + callee-parameterized read-only checker `roProg` -/

/-- `roProg good p` checks that `p` contains no memory stores, global assignments, shared-memory
ops, or FFI calls, and only calls functions satisfying `good` (with local/none destinations). -/
def roProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => roProg good body
  | .seq first second => roProg good first && roProg good second
  | .ite _ yes no => roProg good yes && roProg good no
  | .while _ body => roProg good body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .primitive _ _ _ => true
  | .decCall _ _ fname _ cont => good fname && roProg good cont
  | .call none fname _ => good fname
  | .call (some (none, none)) fname _ => good fname
  | .call (some (some (.local, _), none)) fname _ => good fname
  | .call (some (none, some (_, _, handler))) fname _ => good fname && roProg good handler
  | .call (some (some (.local, _), some (_, _, handler))) fname _ => good fname && roProg good handler
  | _ => false

/-- Every evaluation (regardless of result/timeout/error) of a `roProg` program preserves `SameFrame`,
provided every `good` callee in `originalRuntimeCode` has a `roProg` body. -/
theorem evaluate_roProg {F : Type} (good : MlS → Bool)
    (hgood : ∀ fname, good fname = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) →
      roProg good body = true)
    (p : ProgHOL 64) (hp : roProg good p = true)
    (state : PanSemStateFiniteExact 64 F) (hcode : state.code = originalRuntimeCode) :
    SameFrame state (evaluateHOLFiniteState state p).2 := by
  cases shape : p with
  | skip =>
    rw [evaluateHOLFiniteState_skip]
    exact SameFrame.refl state
  | «break» =>
    rw [evaluateHOLFiniteState_break]
    exact SameFrame.refl state
  | «continue» =>
    rw [evaluateHOLFiniteState_continue]
    exact SameFrame.refl state
  | annot _ _ =>
    rw [evaluateHOLFiniteState_annot]
    exact SameFrame.refl state
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · exact (SameFrame.refl state).emptyLocals
      · exact SameFrame.refl state
    · exact SameFrame.refl state
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact SameFrame.refl state
    · split
      · exact (SameFrame.refl state).emptyLocals
      · exact SameFrame.refl state
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · exact SameFrame.refl state
    · split
      · exact SameFrame.refl state
      · split
        · exact (SameFrame.refl state).setVar _ _
        · exact SameFrame.refl state
  | assign kind name expr =>
    cases kind with
    | global => simp [shape, roProg] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact SameFrame.refl state
      · split
        · exact (SameFrame.refl state).setVar _ _
        · exact SameFrame.refl state
  | dec name sh init body =>
    have hb : roProg good body = true := by simpa [shape, roProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact SameFrame.refl state
    · rename_i val _
      split
      · have ih := evaluate_roProg good hgood body hb (setVarHOLFinite name val state) hcode
        exact ((SameFrame.refl state).setVar name val).trans (ih.with_locals _)
      · exact SameFrame.refl state
  | seq first second =>
    have h12 : roProg good first = true ∧ roProg good second = true := by
      simpa [shape, roProg, Bool.and_eq_true] using hp
    have ih1 := evaluate_roProg good hgood first h12.1 state hcode
    have hrem := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases hr1 : evaluateHOLFiniteState state first with
    | mk r1 mid =>
      rw [hr1] at ih1 hrem
      dsimp only at ih1 hrem ⊢
      cases r1 with
      | none =>
        have mclock : mid.clock ≤ state.clock := hrem
        have ih2 := evaluate_roProg good hgood second h12.2 mid (ih1.code_eq.trans hcode)
        exact ih1.trans ih2
      | some _ => exact ih1
  | ite cond yes no =>
    have h12 : roProg good yes = true ∧ roProg good no = true := by
      simpa [shape, roProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_roProg good hgood no h12.2 state hcode
      · exact evaluate_roProg good hgood yes h12.1 state hcode
    · exact SameFrame.refl state
  | «while» cond body =>
    have hb : roProg good body = true := by simpa [shape, roProg] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact (SameFrame.refl state).emptyLocals
        · rename_i nonzero
          have dec_lt : (decClockHOLFinite state).clock < state.clock := by
            simp only [decClockHOLFinite]
            omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_roProg good hgood body hb (decClockHOLFinite state) hcode
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases hbr : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk r1 mid =>
            rw [hbr] at ih1 hrem
            dsimp only at ih1 hrem
            have smaller : mid.clock < state.clock := by
              change mid.clock ≤ state.clock - 1 at hrem
              omega
            have hsf1 : SameFrame state mid := SameFrame.decClock.trans ih1
            have mcode : mid.code = originalRuntimeCode := hsf1.code_eq.trans hcode
            cases r1 with
            | none =>
              have ih2 := evaluate_roProg good hgood (.while cond body) (by simpa [roProg] using hb) mid mcode
              exact hsf1.trans ih2
            | some res =>
              cases res with
              | «continue» =>
                have ih2 := evaluate_roProg good hgood (.while cond body) (by simpa [roProg] using hb) mid mcode
                exact hsf1.trans ih2
              | _ => exact hsf1
      · exact SameFrame.refl state
    · exact SameFrame.refl state
  | decCall name sh fname args cont =>
    have h12 : good fname = true ∧ roProg good cont = true := by
      simpa [shape, roProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · exact SameFrame.refl state
    · rename_i values _
      split
      · exact SameFrame.refl state
      · rename_i body callee rs found
        have found' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) := by
          simpa [hcode] using found
        have hb : roProg good body = true := hgood fname h12.1 values body callee rs found'
        split
        · exact (SameFrame.refl state).emptyLocals
        · rename_i nonzero
          have entry_lt : (callEntryStateHOLFinite state callee).clock < state.clock := by
            simp only [callEntryStateHOLFinite]
            omega
          dsimp only
          have ih1 := evaluate_roProg good hgood body hb (callEntryStateHOLFinite state callee) hcode
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih1 cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih1 cl ⊢
          have hsf_st : SameFrame state st := (SameFrame.callEntry state callee).trans ih1
          have hsf_fix : SameFrame state (fixClockHOLFinite (callEntryStateHOLFinite state callee) (r, st)).2 :=
            hsf_st.fixClock r
          rcases r with _ | res
          · exact hsf_fix
          · cases res with
            | error => exact hsf_fix.emptyLocals
            | timeOut => exact hsf_fix.emptyLocals
            | «break» => exact hsf_fix
            | «continue» => exact hsf_fix
            | finalFfi _ => exact hsf_fix.emptyLocals
            | exception _ _ => exact hsf_fix.emptyLocals
            | returned v =>
              dsimp only
              split
              · have small :
                    (setVarHOLFinite name v
                      { (fixClockHOLFinite (callEntryStateHOLFinite state callee)
                          (some (PanSemResultExact.returned v), st)).2 with
                        locals := state.locals }).clock < state.clock := by
                  change st.clock ≤ state.clock - 1 at cl
                  simp only [setVarHOLFinite, fixClockHOLFinite, callEntryStateHOLFinite]
                  by_cases hlt : state.clock - 1 < st.clock <;> simp [hlt] <;> omega
                have hcont_sf : SameFrame state
                    (setVarHOLFinite name v
                      { (fixClockHOLFinite (callEntryStateHOLFinite state callee)
                          (some (PanSemResultExact.returned v), st)).2 with
                        locals := state.locals }) :=
                  (hsf_fix.with_locals state.locals).setVar name v
                have ih2 := evaluate_roProg good hgood cont h12.2 _ (hcont_sf.code_eq.trans hcode)
                exact (hcont_sf.trans ih2).with_locals _
              · exact hsf_fix
  | call info fname args =>
    have hk : good fname = true ∧
        (info = none ∨
          (∃ handler, info = some (none, handler)) ∨
          (∃ nm handler, info = some (some (.local, nm), handler))) ∧
        (∀ dest hid hv hp, info = some (dest, some (hid, hv, hp)) → roProg good hp = true) := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | ⟨hid, hv, hp'⟩⟩
      · simpa [shape, roProg] using hp
      · simp [shape, roProg] at hp
        exact ⟨hp, Or.inr (Or.inl ⟨none, rfl⟩), fun _ _ _ _ h => by cases h⟩
      · simp [shape, roProg] at hp
        exact ⟨hp.1, Or.inr (Or.inl ⟨_, rfl⟩), fun _ _ _ _ h => by cases h; exact hp.2⟩
      · cases kind with
        | «local» =>
          simp [shape, roProg] at hp
          exact ⟨hp, Or.inr (Or.inr ⟨nm, none, rfl⟩), fun _ _ _ _ h => by cases h⟩
        | global =>
          simp [shape, roProg] at hp
      · cases kind with
        | «local» =>
          simp [shape, roProg] at hp
          exact ⟨hp.1, Or.inr (Or.inr ⟨nm, _, rfl⟩), fun _ _ _ _ h => by cases h; exact hp.2⟩
        | global =>
          simp [shape, roProg] at hp
    rw [evaluateHOLFiniteState_call]
    split
    · exact SameFrame.refl state
    · rename_i values _
      split
      · exact SameFrame.refl state
      · rename_i body callee rs found
        have found' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) := by
          simpa [hcode] using found
        have hb : roProg good body = true := hgood fname hk.1 values body callee rs found'
        split
        · exact (SameFrame.refl state).emptyLocals
        · rename_i nonzero
          have entry_lt : (callEntryStateHOLFinite state callee).clock < state.clock := by
            simp only [callEntryStateHOLFinite]
            omega
          have ih1 := evaluate_roProg good hgood body hb (callEntryStateHOLFinite state callee) hcode
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih1 cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih1 cl ⊢
          have hsf_st : SameFrame state st := (SameFrame.callEntry state callee).trans ih1
          have stc : st.clock < state.clock := by
            change st.clock ≤ state.clock - 1 at cl
            omega
          rcases hk.2.1 with rfl | ⟨handler, rfl⟩ | ⟨nm, handler, rfl⟩
          · rcases r with _ | (_ | _ | _ | _ | v | ⟨eid, v⟩ | _)
            · exact hsf_st
            · exact hsf_st.emptyLocals
            · exact hsf_st.emptyLocals
            · exact hsf_st
            · exact hsf_st
            · dsimp only
              split
              · exact hsf_st.emptyLocals
              · exact hsf_st
            · exact hsf_st.emptyLocals
            · exact hsf_st.emptyLocals
          · rcases handler with _ | ⟨hid, hv, hp'⟩
            · rcases r with _ | (_ | _ | _ | _ | v | ⟨eid, v⟩ | _)
              · exact hsf_st
              · exact hsf_st.emptyLocals
              · exact hsf_st.emptyLocals
              · exact hsf_st
              · exact hsf_st
              · dsimp only
                split
                · exact hsf_st.with_locals state.locals
                · exact hsf_st
              · exact hsf_st.emptyLocals
              · exact hsf_st.emptyLocals
            · rcases r with _ | (_ | _ | _ | _ | v | ⟨eid, v⟩ | _)
              · exact hsf_st
              · exact hsf_st.emptyLocals
              · exact hsf_st.emptyLocals
              · exact hsf_st
              · exact hsf_st
              · dsimp only
                split
                · exact hsf_st.with_locals state.locals
                · exact hsf_st
              · dsimp only
                split
                · split
                  · split
                    · have hhp := hk.2.2 none hid hv hp' rfl
                      have h_lt : (setVarHOLFinite hv v { st with locals := state.locals }).clock < state.clock := stc
                      have hsf_h : SameFrame state (setVarHOLFinite hv v { st with locals := state.locals }) :=
                        (hsf_st.with_locals state.locals).setVar hv v
                      have ihh := evaluate_roProg good hgood hp' hhp
                        (setVarHOLFinite hv v { st with locals := state.locals }) (hsf_h.code_eq.trans hcode)
                      exact hsf_h.trans ihh
                    · exact hsf_st
                  · exact hsf_st
                · exact hsf_st.emptyLocals
              · exact hsf_st.emptyLocals
          · rcases handler with _ | ⟨hid, hv, hp'⟩
            · rcases r with _ | (_ | _ | _ | _ | v | ⟨eid, v⟩ | _)
              · exact hsf_st
              · exact hsf_st.emptyLocals
              · exact hsf_st.emptyLocals
              · exact hsf_st
              · exact hsf_st
              · dsimp only
                split
                · split
                  · exact (hsf_st.with_locals state.locals).setVar nm v
                  · exact hsf_st
                · exact hsf_st
              · exact hsf_st.emptyLocals
              · exact hsf_st.emptyLocals
            · rcases r with _ | (_ | _ | _ | _ | v | ⟨eid, v⟩ | _)
              · exact hsf_st
              · exact hsf_st.emptyLocals
              · exact hsf_st.emptyLocals
              · exact hsf_st
              · exact hsf_st
              · dsimp only
                split
                · split
                  · exact (hsf_st.with_locals state.locals).setVar nm v
                  · exact hsf_st
                · exact hsf_st
              · dsimp only
                split
                · split
                  · split
                    · have hhp := hk.2.2 (some (.local, nm)) hid hv hp' rfl
                      have h_lt : (setVarHOLFinite hv v { st with locals := state.locals }).clock < state.clock := stc
                      have hsf_h : SameFrame state (setVarHOLFinite hv v { st with locals := state.locals }) :=
                        (hsf_st.with_locals state.locals).setVar hv v
                      have ihh := evaluate_roProg good hgood hp' hhp
                        (setVarHOLFinite hv v { st with locals := state.locals }) (hsf_h.code_eq.trans hcode)
                      exact hsf_h.trans ihh
                    · exact hsf_st
                  · exact hsf_st
                · exact hsf_st.emptyLocals
              · exact hsf_st.emptyLocals
  | _ => simp [shape, roProg] at hp
termination_by (state.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ entry_lt
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ small
      | exact Prod.Lex.left _ _ h_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

/-! ## 4. Turning AST lookup + `roProg` into `ReadOnlyFn` -/

/-- No-callee pure read-only body. -/
theorem evaluate_roProg_none {F : Type} (p : ProgHOL 64)
    (hp : roProg (fun _ => false) p = true)
    (state : PanSemStateFiniteExact 64 F) (hcode : state.code = originalRuntimeCode) :
    SameFrame state (evaluateHOLFiniteState state p).2 :=
  evaluate_roProg (fun _ => false) (fun _ h => by simp at h) p hp state hcode

/-- Lookup + `roProg` directly proves `ReadOnlyFn` for any `guestAst[idx]` function. -/
theorem readOnlyFn_of_guestAst_roProg (idx : Nat) (d : Decl (BitVec 64))
    (good : MlS → Bool)
    (hgood : ∀ fname, good fname = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs) →
      roProg good body = true)
    (hidx : idx < Guest.Software.guestAst.length)
    (hd : Guest.Software.guestAst[idx] = .function (extractFn d))
    (hro : roProg good
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) = true) :
    ReadOnlyFn (ofString (extractFn d).name) := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem idx hidx (extractFn d) hd, ?_⟩
  intro F s hcode _ _ _ _
  exact evaluate_roProg good hgood _ hro s hcode

/-- Specialization for call-free functions (`good := fun _ => false`). -/
theorem readOnlyFn_of_guestAst_pure (idx : Nat) (d : Decl (BitVec 64))
    (hidx : idx < Guest.Software.guestAst.length)
    (hd : Guest.Software.guestAst[idx] = .function (extractFn d))
    (hro : roProg (fun _ => false)
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) = true) :
    ReadOnlyFn (ofString (extractFn d).name) :=
  readOnlyFn_of_guestAst_roProg idx d (fun _ => false) (fun _ h => by simp at h) hidx hd hro

/-- Helper to discharge `lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs)`
into `body = progToHOLStructural (extractFn d).body`. -/
theorem body_eq_of_lookupCode {fname : MlS} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    {params : List (MlS × ShapeHOL)} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname = some (params, body0, rs0))
    (hfound : lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, rs)) :
    body = body0 := by
  obtain ⟨p', r', hc⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  rw [hlook] at hc
  injection hc with h
  injection h with _ h2
  injection h2 with hb _
  exact hb.symm

end InitECandidate.Solver.Wave8GuestInv.M17
