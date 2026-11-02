import InitECandidate.Solver.Wave8GuestInv.Defs

/-! Shared read-only contract infrastructure for micro-shard `m18` (`wave8/contracts-m18`),
frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.Defs`.
Restates `FunSpec`, `Resumes`, and `ReadOnlyFn` verbatim from `campaign/specs-proposed/GuestInv.lean`
@ `8a79d9f28` so they delta-reduce definitionally (`rfl`) to the spec statements in `Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M18

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- Outcome specification of a function body from its callee-entry state
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
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

/-- The outcomes after which the caller resumes (return, or a catchable exception)
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

/-- `fname` changes nothing but locals and clock
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

/-- `t` agrees with `s` on every field except `locals` and `clock`. -/
def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *
  rw [h2]; rw [h1]

theorem LocFrame.with_locals_clock {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    LocFrame s { t with locals := locals, clock := k } := by
  unfold LocFrame at h ⊢
  rw [h]

/-- A run of `prog` from `s` either changes nothing except `locals` and `clock`,
or terminates with an uncatchable/fatal outcome (neither falls through `none`, nor `continue`,
nor `break`, nor returns, nor raises a catchable exception). -/
def SafeOrTrapped {F : Type} (s : PanSemStateFiniteExact 64 F)
    (out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  LocFrame s out.2 ∨
    (out.1 ≠ none ∧ out.1 ≠ some .continue ∧ out.1 ≠ some .break ∧ ¬ Resumes out.1)

theorem SafeOrTrapped.of_locFrame {F : Type} {s : PanSemStateFiniteExact 64 F}
    {out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F}
    (h : LocFrame s out.2) : SafeOrTrapped s out :=
  Or.inl h

theorem SafeOrTrapped.to_resumes {F : Type} {s : PanSemStateFiniteExact 64 F}
    {out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F}
    (h : SafeOrTrapped s out) (hr : Resumes out.1) : LocFrame s out.2 := by
  rcases h with hl | ⟨_, _, _, hnr⟩
  · exact hl
  · exact absurd hr hnr

theorem call_trap_with_trapped {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (hcode : state.code = originalRuntimeCode) :
    SafeOrTrapped state
      (evaluateHOLFiniteState state (.call (some (none, none)) (ofString "trap_with") arguments)) := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact Or.inl (LocFrame.refl state)
  · dsimp only
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "trap_with") values with
      _ | ⟨body, callee, rs⟩
    · exact Or.inl (LocFrame.refl state)
    · dsimp only
      have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "trap_with") values =
          some (body, callee, rs) := by rwa [← hcode]
      obtain ⟨params, rs', hinst⟩ := lookupCode_installed hl'
      rw [lookup_trap_with] at hinst
      have hbody : body = sourceFnBody Guest.Software.guestFn_trap_with :=
        (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1.symm
      subst hbody
      split
      · exact Or.inl rfl
      · have hout := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite state callee)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee)
            (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
        rw [hrun] at hout
        dsimp only at hout ⊢
        cases res with
        | none => exact absurd rfl hout.1
        | some r =>
          cases r with
          | returned v => exact absurd rfl (hout.2.1 v)
          | «break» | «continue» | error | timeOut | finalFfi _ =>
            exact Or.inr ⟨by simp, by simp, by simp,
              by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
          | exception eid v =>
            refine Or.inr ⟨by simp, by simp, by simp, ?_⟩
            rintro (⟨_, h⟩ | ⟨e, w, h, hne⟩)
            · simp at h
            · injection h with h'
              injection h' with he hw
              subst he hw
              exact hout.2.2 eid v hne rfl

/-- Syntactic predicate for programs that perform no memory store, shared-memory write/global load,
global assignment, or FFI call (except `call trap_with`), calling only `decCall` callees approved
by `good`. -/
def readOnlyProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => readOnlyProg good body
  | .seq first second => readOnlyProg good first && readOnlyProg good second
  | .ite _ yes no => readOnlyProg good yes && readOnlyProg good no
  | .while _ body => readOnlyProg good body
  | .decCall _ _ fname _ cont => good fname && readOnlyProg good cont
  | .call (some (none, none)) fname _ => fname == ofString "trap_with"
  | .assign .local _ _ => true
  | .primitive _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem evaluate_readOnlyProg {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (program : ProgHOL 64) (supported : readOnlyProg good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    SafeOrTrapped state (evaluateHOLFiniteState state program) := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact Or.inl (LocFrame.refl state)
  | «break» => rw [evaluateHOLFiniteState_break]; exact Or.inl (LocFrame.refl state)
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact Or.inl (LocFrame.refl state)
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact Or.inl (LocFrame.refl state)
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · exact Or.inl rfl
      · exact Or.inl (LocFrame.refl state)
    · exact Or.inl (LocFrame.refl state)
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact Or.inl (LocFrame.refl state)
    · split
      · exact Or.inl rfl
      · exact Or.inl (LocFrame.refl state)
  | assign kind name value =>
    cases kind with
    | global => simp [shape, readOnlyProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact Or.inl (LocFrame.refl state)
      · split
        · exact Or.inl rfl
        · exact Or.inl (LocFrame.refl state)
  | primitive name op args =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · exact Or.inl (LocFrame.refl state)
    · split
      · exact Or.inl (LocFrame.refl state)
      · split
        · exact Or.inl rfl
        · exact Or.inl (LocFrame.refl state)
  | dec name kind initializer body =>
    have child : readOnlyProg good body = true := by simpa only [shape, readOnlyProg] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact Or.inl (LocFrame.refl state)
    · rename_i val _
      split
      · have ih := evaluate_readOnlyProg good hgood body child (setVarHOLFinite name val state) code
        rcases hrun : evaluateHOLFiniteState (setVarHOLFinite name val state) body with ⟨res, st⟩
        rw [hrun] at ih
        rcases ih with hloc | ⟨hnn, hnc, hnb, hnr⟩
        · refine Or.inl ?_
          unfold LocFrame at hloc ⊢
          dsimp only at hloc ⊢
          rw [hloc]; rfl
        · exact Or.inr ⟨hnn, hnc, hnb, hnr⟩
      · exact Or.inl (LocFrame.refl state)
  | seq first second =>
    have children : readOnlyProg good first = true ∧ readOnlyProg good second = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    have ih1 := evaluate_readOnlyProg good hgood first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at ih1 remaining meta'
      dsimp only at ih1 remaining meta' ⊢
      cases result with
      | none =>
        rcases ih1 with hloc1 | ⟨hnn, _⟩
        · have mclock : middle.clock ≤ state.clock := remaining
          have ih2 := evaluate_readOnlyProg good hgood second children.2 middle (meta'.1.trans code)
          rcases ih2 with hloc2 | htrap2
          · exact Or.inl (hloc1.trans hloc2)
          · exact Or.inr htrap2
        · exact absurd rfl hnn
      | some r =>
        rcases ih1 with hloc1 | ⟨_, hnc, hnb, hnr⟩
        · exact Or.inl hloc1
        · exact Or.inr ⟨by simp, hnc, hnb, hnr⟩
  | ite condition yes no =>
    have children : readOnlyProg good yes = true ∧ readOnlyProg good no = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_readOnlyProg good hgood no children.2 state code
      · exact evaluate_readOnlyProg good hgood yes children.1 state code
    · exact Or.inl (LocFrame.refl state)
  | «while» condition body =>
    have child : readOnlyProg good body = true := by simpa only [shape, readOnlyProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact Or.inl rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_readOnlyProg good hgood body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at ih1 remaining meta'
            dsimp only at ih1 remaining meta' ⊢
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none =>
              rcases ih1 with hloc1 | ⟨hnn, _⟩
              · dsimp only at hloc1
                have ih1' : LocFrame state middle := by
                  unfold LocFrame at hloc1 ⊢
                  rw [hloc1]; rfl
                have ih2 := evaluate_readOnlyProg good hgood (.while condition body)
                  (by simpa [readOnlyProg] using child) middle mCode
                rcases ih2 with hloc2 | htrap2
                · exact Or.inl (ih1'.trans hloc2)
                · exact Or.inr htrap2
              · exact absurd rfl hnn
            | some r =>
              cases r with
              | «continue» =>
                rcases ih1 with hloc1 | ⟨_, hnc, _⟩
                · dsimp only at hloc1
                  have ih1' : LocFrame state middle := by
                    unfold LocFrame at hloc1 ⊢
                    rw [hloc1]; rfl
                  have ih2 := evaluate_readOnlyProg good hgood (.while condition body)
                    (by simpa [readOnlyProg] using child) middle mCode
                  rcases ih2 with hloc2 | htrap2
                  · exact Or.inl (ih1'.trans hloc2)
                  · exact Or.inr htrap2
                · exact absurd rfl hnc
              | «break» =>
                rcases ih1 with hloc1 | ⟨_, _, hnb, _⟩
                · dsimp only at hloc1
                  refine Or.inl ?_
                  unfold LocFrame at hloc1 ⊢
                  rw [hloc1]; rfl
                · exact absurd rfl hnb
              | returned _ | exception _ _ | finalFfi _ | error | timeOut =>
                rcases ih1 with hloc1 | ⟨_, _, _, hnr⟩
                · dsimp only at hloc1
                  refine Or.inl ?_
                  unfold LocFrame at hloc1 ⊢
                  rw [hloc1]; rfl
                · exact Or.inr ⟨by simp, by simp, by simp, hnr⟩
      · exact Or.inl (LocFrame.refl state)
    · exact Or.inl (LocFrame.refl state)
  | call ret fname arguments =>
    rcases ret with _ | ⟨dest, hdl⟩
    · simp [shape, readOnlyProg] at supported
    · rcases dest with _ | _
      · rcases hdl with _ | _
        · have hfn : fname = ofString "trap_with" := by
            simpa only [shape, readOnlyProg, beq_iff_eq] using supported
          subst hfn
          exact call_trap_with_trapped state arguments code
        · simp [shape, readOnlyProg] at supported
      · simp [shape, readOnlyProg] at supported
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ readOnlyProg good continuation = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
    · exact Or.inl (LocFrame.refl state)
    · dsimp only
      rcases found : lookupCodeHOLFinite state.code.lookup function values with _ | ⟨body, callee, rs⟩
      · exact Or.inl (LocFrame.refl state)
      · dsimp only
        have found' : lookupCodeHOLFinite originalRuntimeCode.lookup function values =
            some (body, callee, rs) := by rwa [← code]
        have bodyOk := hgood function children.1 values body callee rs found'
        split
        · exact Or.inl rfl
        · rename_i nonzero
          have ih := evaluate_readOnlyProg good hgood body bodyOk
            (callEntryStateHOLFinite state callee) code
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
          | mk res st =>
            rw [hrun] at ih meta' cl
            dsimp only at ih meta' cl ⊢
            change st.clock ≤ state.clock - 1 at cl
            have small : st.clock < state.clock := by omega
            have stCode : st.code = originalRuntimeCode := meta'.1.trans code
            cases res with
            | none =>
              rcases ih with hloc | ⟨hnn, _⟩
              · dsimp only at hloc
                refine Or.inl ?_
                unfold LocFrame at hloc ⊢
                rw [hloc]; rfl
              · exact absurd rfl hnn
            | some r =>
              cases r with
              | returned v =>
                have hloc : LocFrame (callEntryStateHOLFinite state callee) st :=
                  ih.to_resumes (Or.inl ⟨v, rfl⟩)
                have ih' : LocFrame state st := by
                  unfold LocFrame at hloc ⊢
                  rw [hloc]; rfl
                dsimp only
                split
                · set resumed := setVarHOLFinite name v { st with locals := state.locals }
                  have smallR : resumed.clock < state.clock := small
                  have rCode : resumed.code = originalRuntimeCode := stCode
                  have ihR : LocFrame state resumed := ih'.with_locals_clock _ _
                  have ih2 := evaluate_readOnlyProg good hgood continuation children.2 resumed rCode
                  rcases hcont : evaluateHOLFiniteState resumed continuation with ⟨res2, st2⟩
                  rw [hcont] at ih2
                  rcases ih2 with hloc2 | ⟨hnn2, hnc2, hnb2, hnr2⟩
                  · dsimp only at hloc2
                    exact Or.inl ((ihR.trans hloc2).with_locals_clock _ _)
                  · exact Or.inr ⟨hnn2, hnc2, hnb2, hnr2⟩
                · exact Or.inl ih'
              | timeOut | error | exception _ _ | finalFfi _ =>
                rcases ih with hloc | ⟨_, _, _, hnr⟩
                · dsimp only at hloc
                  have ih' : LocFrame state st := by
                    unfold LocFrame at hloc ⊢
                    rw [hloc]; rfl
                  exact Or.inl (ih'.with_locals_clock _ _)
                · exact Or.inr ⟨by simp, by simp, by simp, hnr⟩
              | «break» | «continue» =>
                rcases ih with hloc | ⟨_, hnc, hnb, _⟩
                · dsimp only at hloc
                  refine Or.inl ?_
                  unfold LocFrame at hloc ⊢
                  rw [hloc]; rfl
                · exact Or.inr ⟨by simp, by simp, by simp,
                    by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
  | _ => simp [shape, readOnlyProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

theorem readOnlyFn_of_guestAst (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (hbody : readOnlyProg good
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) =
        true) :
    ReadOnlyFn (ofString (extractFn d).name) :=
  ⟨_, _, _, lookup_of_guestAst_getElem i hi (extractFn d) hd,
    fun s hcode _ _ _ hr => (evaluate_readOnlyProg good hgood _ hbody s hcode).to_resumes hr⟩

/-- Helper to prove `readOnlyProg good body = true` for a single installed function at `guestAst[i]`. -/
theorem installed_body_readOnly (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (good : MlS → Bool)
    (hbody : readOnlyProg good
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) =
        true)
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString (extractFn d).name) values = some (body, callee, rs)) :
    readOnlyProg good body = true := by
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  have hl := lookup_of_guestAst_getElem i hi (extractFn d) hd
  rw [hl] at hinst
  have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
  rw [← heq]
  exact hbody

/-- All `decCall` callees needed across micro-shard `m18`. -/
def m18Callees (f : MlS) : Bool :=
  f == ofString "memeq" ||
  f == ofString "udivmod" ||
  f == ofString "udiv" ||
  f == ofString "u256_fits_word" ||
  f == ofString "u256_is_zero" ||
  f == ofString "mul64x64" ||
  f == ofString "htab_find_leaf" ||
  f == ofString "htab_has" ||
  f == ofString "htab_item" ||
  f == ofString "count_tokens_in_data" ||
  f == ofString "calculate_intrinsic_cost"

theorem m18Callees_good :
    ∀ function, m18Callees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg m18Callees body = true := by
  intro function hfn values body callee rs hfound
  simp only [m18Callees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · exact installed_body_readOnly 18 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_memeq rfl m18Callees rfl hfound
  · exact installed_body_readOnly 33 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_udivmod rfl m18Callees rfl hfound
  · exact installed_body_readOnly 34 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_udiv rfl m18Callees rfl hfound
  · exact installed_body_readOnly 41 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_u256_fits_word rfl m18Callees rfl hfound
  · exact installed_body_readOnly 42 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_u256_is_zero rfl m18Callees rfl hfound
  · exact installed_body_readOnly 59 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_mul64x64 rfl m18Callees rfl hfound
  · exact installed_body_readOnly 131 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_htab_find_leaf rfl m18Callees rfl hfound
  · exact installed_body_readOnly 133 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_htab_has rfl m18Callees rfl hfound
  · exact installed_body_readOnly 143 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_htab_item rfl m18Callees rfl hfound
  · exact installed_body_readOnly 344 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_count_tokens_in_data rfl m18Callees rfl hfound
  · exact installed_body_readOnly 345 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_calculate_intrinsic_cost rfl m18Callees rfl hfound

end InitECandidate.Solver.Wave8Contracts.M18
