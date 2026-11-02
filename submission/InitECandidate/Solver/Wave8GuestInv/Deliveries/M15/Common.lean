import InitECandidate.Solver.Wave8GuestInv.Defs

/-! Shared read-only contract infrastructure for micro-shard `m15` (`wave8/contracts-m15`),
frozen revision 9 (`8a79d9f28`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.Defs`.
Restates `FunSpec`, `Resumes`, and `ReadOnlyFn` verbatim from `campaign/specs-proposed/GuestInv.lean`
@ `8a79d9f28` so they delta-reduce definitionally (`rfl`) to the spec statements in `Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M15

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

/-- Syntactic predicate for programs that perform no memory store, shared-memory write/global load,
global assignment, or FFI call, calling only `decCall` callees approved by `good`. -/
def readOnlyProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => readOnlyProg good body
  | .seq first second => readOnlyProg good first && readOnlyProg good second
  | .ite _ yes no => readOnlyProg good yes && readOnlyProg good no
  | .while _ body => readOnlyProg good body
  | .decCall _ _ fname _ cont => good fname && readOnlyProg good cont
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem evaluate_readOnlyProg {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (program : ProgHOL 64) (supported : readOnlyProg good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    LocFrame state (evaluateHOLFiniteState state program).2 := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl state
  | «break» => rw [evaluateHOLFiniteState_break]; exact LocFrame.refl state
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl state
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl state
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · rfl
      · exact LocFrame.refl state
    · exact LocFrame.refl state
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl state
    · split
      · rfl
      · exact LocFrame.refl state
  | assign kind name value =>
    cases kind with
    | global => simp [shape, readOnlyProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl state
      · split
        · rfl
        · exact LocFrame.refl state
  | dec name kind initializer body =>
    have child : readOnlyProg good body = true := by simpa only [shape, readOnlyProg] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl state
    · rename_i val _
      split
      · have ih := evaluate_readOnlyProg good hgood body child (setVarHOLFinite name val state) code
        unfold LocFrame at ih ⊢
        dsimp only
        rw [ih]; rfl
      · exact LocFrame.refl state
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
        have mclock : middle.clock ≤ state.clock := remaining
        exact ih1.trans (evaluate_readOnlyProg good hgood second children.2 middle (meta'.1.trans code))
      | some _ => exact ih1
  | ite condition yes no =>
    have children : readOnlyProg good yes = true ∧ readOnlyProg good no = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_readOnlyProg good hgood no children.2 state code
      · exact evaluate_readOnlyProg good hgood yes children.1 state code
    · exact LocFrame.refl state
  | «while» condition body =>
    have child : readOnlyProg good body = true := by simpa only [shape, readOnlyProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
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
            have ih1' : LocFrame state middle := by
              unfold LocFrame at ih1 ⊢
              rw [ih1]; rfl
            cases result with
            | none =>
              exact ih1'.trans (evaluate_readOnlyProg good hgood (.while condition body)
                (by simpa [readOnlyProg] using child) middle mCode)
            | some result =>
              cases result with
              | «continue» =>
                exact ih1'.trans (evaluate_readOnlyProg good hgood (.while condition body)
                  (by simpa [readOnlyProg] using child) middle mCode)
              | «break» => exact ih1'
              | returned _ => exact ih1'
              | exception _ _ => exact ih1'
              | finalFfi _ => exact ih1'
              | error => exact ih1'
              | timeOut => exact ih1'
      · exact LocFrame.refl state
    · exact LocFrame.refl state
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ readOnlyProg good continuation = true := by
      simpa only [shape, readOnlyProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
    · exact LocFrame.refl state
    · dsimp only
      rcases found : lookupCodeHOLFinite state.code.lookup function values with _ | ⟨body, callee, rs⟩
      · exact LocFrame.refl state
      · dsimp only
        have found' : lookupCodeHOLFinite originalRuntimeCode.lookup function values =
            some (body, callee, rs) := by rwa [← code]
        have bodyOk := hgood function children.1 values body callee rs found'
        split
        · rfl
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
            have ih' : LocFrame state st := by
              unfold LocFrame at ih ⊢
              rw [ih]; rfl
            cases res with
            | none => exact ih'
            | some r =>
              cases r with
              | returned v =>
                dsimp only
                split
                · set resumed := setVarHOLFinite name v { st with locals := state.locals }
                  have smallR : resumed.clock < state.clock := small
                  have rCode : resumed.code = originalRuntimeCode := stCode
                  have ihR : LocFrame state resumed := ih'.with_locals_clock _ _
                  have ih2 := evaluate_readOnlyProg good hgood continuation children.2 resumed rCode
                  exact (ihR.trans ih2).with_locals_clock _ _
                · exact ih'
              | timeOut => exact ih'.with_locals_clock _ _
              | «break» => exact ih'
              | «continue» => exact ih'
              | error => exact ih'.with_locals_clock _ _
              | exception _ _ => exact ih'.with_locals_clock _ _
              | finalFfi _ => exact ih'.with_locals_clock _ _
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
    fun s hcode _ _ _ _ => evaluate_readOnlyProg good hgood _ hbody s hcode⟩

/-- Callees invoked via `decCall` by `htab_get` and `htab_has`. -/
def htabGetCallees (f : MlS) : Bool :=
  f == ofString "htab_find_leaf" || f == ofString "memeq"

theorem htabGetCallees_good :
    ∀ function, htabGetCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg htabGetCallees body = true := by
  intro function hfn values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [htabGetCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with rfl | rfl
  · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]
    rfl
  · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_memeq) rfl
    change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]
    rfl

end InitECandidate.Solver.Wave8Contracts.M15
