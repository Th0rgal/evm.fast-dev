import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min
import InitECandidate.Solver.GuestGlobalKeep

/-! # Read-only helper specs (`EvmPreservingSpec`) and gas-cost bounds (`u256_byte_length`, `words_of`, `add_sat`, `access_gas_cost`) -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Extended `readOnlyProg` engine supporting `.decCall`, tail `.call none`,
    void `.call (some (none, none))` (`trap_with` or `good`), and
    local-assign `.call (some (some (.local, _), none))` -/

def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *; rw [h2]; rw [h1]

theorem LocFrame.with_locals_clock {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    LocFrame s { t with locals := locals, clock := k } := by
  unfold LocFrame at h ⊢; rw [h]

def SafeOrTrapped {F : Type} (s : PanSemStateFiniteExact 64 F)
    (out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  LocFrame s out.2 ∨
    (out.1 ≠ none ∧ out.1 ≠ some .continue ∧ out.1 ≠ some .break ∧ ¬ Resumes out.1)

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

def readOnlyProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => readOnlyProg good body
  | .seq first second => readOnlyProg good first && readOnlyProg good second
  | .ite _ yes no => readOnlyProg good yes && readOnlyProg good no
  | .while _ body => readOnlyProg good body
  | .decCall _ _ fname _ cont => good fname && readOnlyProg good cont
  | .call none fname _ => good fname
  | .call (some (none, none)) fname _ => (fname == ofString "trap_with") || good fname
  | .call (some (some (.local, _), none)) fname _ => good fname
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
    · -- tail call `.call none fname arguments`
      have hfn : good fname = true := by simpa only [shape, readOnlyProg] using supported
      rw [evaluateHOLFiniteState_call]
      rcases hargs : evalListHOLFinite state
          (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
      · exact Or.inl (LocFrame.refl state)
      · dsimp only
        rcases found : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body, callee, rs⟩
        · exact Or.inl (LocFrame.refl state)
        · dsimp only
          have found' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
              some (body, callee, rs) := by rwa [← code]
          have bodyOk := hgood fname hfn values body callee rs found'
          split
          · exact Or.inl rfl
          · have ih := evaluate_readOnlyProg good hgood body bodyOk
              (callEntryStateHOLFinite state callee) code
            have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
            cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
            | mk res st =>
              rw [hrun] at ih cl
              dsimp only at ih cl
              change st.clock ≤ state.clock - 1 at cl
              have small : st.clock < state.clock := by omega
              cases res with
              | none =>
                rcases ih with hloc | ⟨hnn, _⟩
                · dsimp only at hloc
                  refine Or.inl ?_
                  unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                · exact absurd rfl hnn
              | some r =>
                cases r with
                | returned v =>
                  have hloc : LocFrame (callEntryStateHOLFinite state callee) st :=
                    ih.to_resumes (Or.inl ⟨v, rfl⟩)
                  have ih' : LocFrame state st := by
                    unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                  dsimp only
                  split
                  · exact Or.inl (ih'.with_locals_clock _ _)
                  · exact Or.inl ih'
                | timeOut | error | exception _ _ | finalFfi _ =>
                  rcases ih with hloc | ⟨_, _, _, hnr⟩
                  · dsimp only at hloc
                    have ih' : LocFrame state st := by
                      unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                    exact Or.inl (ih'.with_locals_clock _ _)
                  · exact Or.inr ⟨by simp, by simp, by simp, hnr⟩
                | «break» | «continue» =>
                  rcases ih with hloc | _
                  · dsimp only at hloc
                    refine Or.inl ?_
                    unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                  · exact Or.inr ⟨by simp, by simp, by simp,
                      by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
    · rcases hdl with _ | _
      · rcases dest with _ | ⟨vk, vnm⟩
        · -- `.call (some (none, none)) fname arguments`
          have hor : fname = ofString "trap_with" ∨ good fname = true := by
            simpa only [shape, readOnlyProg, Bool.or_eq_true, beq_iff_eq] using supported
          by_cases htr : fname = ofString "trap_with"
          · subst htr
            exact call_trap_with_trapped state arguments code
          · have hfn : good fname = true := hor.resolve_left htr
            rw [evaluateHOLFiniteState_call]
            rcases hargs : evalListHOLFinite state
                (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
            · exact Or.inl (LocFrame.refl state)
            · dsimp only
              rcases found : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body, callee, rs⟩
              · exact Or.inl (LocFrame.refl state)
              · dsimp only
                have found' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
                    some (body, callee, rs) := by rwa [← code]
                have bodyOk := hgood fname hfn values body callee rs found'
                split
                · exact Or.inl rfl
                · have ih := evaluate_readOnlyProg good hgood body bodyOk
                    (callEntryStateHOLFinite state callee) code
                  have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
                  cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
                  | mk res st =>
                    rw [hrun] at ih cl
                    dsimp only at ih cl
                    change st.clock ≤ state.clock - 1 at cl
                    have small : st.clock < state.clock := by omega
                    cases res with
                    | none =>
                      rcases ih with hloc | ⟨hnn, _⟩
                      · dsimp only at hloc
                        refine Or.inl ?_
                        unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                      · exact absurd rfl hnn
                    | some r =>
                      cases r with
                      | returned v =>
                        have hloc : LocFrame (callEntryStateHOLFinite state callee) st :=
                          ih.to_resumes (Or.inl ⟨v, rfl⟩)
                        have ih' : LocFrame state st := by
                          unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                        dsimp only
                        split
                        · exact Or.inl (ih'.with_locals_clock _ _)
                        · exact Or.inl ih'
                      | timeOut | error | exception _ _ | finalFfi _ =>
                        rcases ih with hloc | ⟨_, _, _, hnr⟩
                        · dsimp only at hloc
                          have ih' : LocFrame state st := by
                            unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                          exact Or.inl (ih'.with_locals_clock _ _)
                        · exact Or.inr ⟨by simp, by simp, by simp, hnr⟩
                      | «break» | «continue» =>
                        rcases ih with hloc | _
                        · dsimp only at hloc
                          refine Or.inl ?_
                          unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                        · exact Or.inr ⟨by simp, by simp, by simp,
                            by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
        · cases vk with
          | global => simp [shape, readOnlyProg] at supported
          | «local» =>
            have hfn : good fname = true := by simpa only [shape, readOnlyProg] using supported
            rw [evaluateHOLFiniteState_call]
            rcases hargs : evalListHOLFinite state
                (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
            · exact Or.inl (LocFrame.refl state)
            · dsimp only
              rcases found : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body, callee, rs⟩
              · exact Or.inl (LocFrame.refl state)
              · dsimp only
                have found' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
                    some (body, callee, rs) := by rwa [← code]
                have bodyOk := hgood fname hfn values body callee rs found'
                split
                · exact Or.inl rfl
                · have ih := evaluate_readOnlyProg good hgood body bodyOk
                    (callEntryStateHOLFinite state callee) code
                  have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
                  cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
                  | mk res st =>
                    rw [hrun] at ih cl
                    dsimp only at ih cl
                    change st.clock ≤ state.clock - 1 at cl
                    have small : st.clock < state.clock := by omega
                    cases res with
                    | none =>
                      rcases ih with hloc | ⟨hnn, _⟩
                      · dsimp only at hloc
                        refine Or.inl ?_
                        unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                      · exact absurd rfl hnn
                    | some r =>
                      cases r with
                      | returned v =>
                        have hloc : LocFrame (callEntryStateHOLFinite state callee) st :=
                          ih.to_resumes (Or.inl ⟨v, rfl⟩)
                        have ih' : LocFrame state st := by
                          unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                        dsimp only
                        split
                        · split
                          · exact Or.inl (ih'.with_locals_clock _ _)
                          · exact Or.inl ih'
                        · exact Or.inl ih'
                      | timeOut | error | exception _ _ | finalFfi _ =>
                        rcases ih with hloc | ⟨_, _, _, hnr⟩
                        · dsimp only at hloc
                          have ih' : LocFrame state st := by
                            unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                          exact Or.inl (ih'.with_locals_clock _ _)
                        · exact Or.inr ⟨by simp, by simp, by simp, hnr⟩
                      | «break» | «continue» =>
                        rcases ih with hloc | _
                        · dsimp only at hloc
                          refine Or.inl ?_
                          unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                        · exact Or.inr ⟨by simp, by simp, by simp,
                            by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
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
                rcases ih with hloc | _
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
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, ProgHOL.call.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | exact Or.inl small
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

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

theorem eps_of_readOnly (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (hbody : readOnlyProg good
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) =
        true) :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString (extractFn d).name) := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem i hi (extractFn d) hd, ?_⟩
  intro F s hcode hInv _ _ _
  have hsafe := evaluate_readOnlyProg good hgood _ hbody s hcode
  have hres (hr : Resumes (evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).1) :
      let post := (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2
      EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧ LocFrame s post := by
    have hlf := hsafe.to_resumes hr
    dsimp only
    let post := (evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2
    have hInv_p : EvmInv post := by
      have h := localsFree_evmInv s post.locals post.clock hInv
      rwa [← hlf] at h
    have hm : post.memory = s.memory := by
      change (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2.memory = s.memory
      conv_lhs => rw [hlf]
    have hg : post.globals = s.globals := by
      change (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2.globals = s.globals
      conv_lhs => rw [hlf]
    have hc := evm_congr hm hg
    exact ⟨hInv_p, evmChain_congr hm hg, le_of_eq hc.2.1, hlf⟩
  refine ⟨fun v hv => hres (Or.inl ⟨v, hv⟩), fun ⟨v, hv⟩ => ?_⟩
  obtain ⟨h1, h2, h3, _⟩ := hres (Or.inr ⟨_, v, hv, by decide⟩)
  exact ⟨h1, h2, h3⟩

/-! ## 2. Closed read-only callee table for Groups 01–05 -/

def opRoCallees (f : MlS) : Bool :=
  f == ofString "heap_mark" ||
  f == ofString "memeq" ||
  f == ofString "bswap64" ||
  f == ofString "udivmod" ||
  f == ofString "udiv" ||
  f == ofString "u256_from_word" ||
  f == ofString "u256_low" ||
  f == ofString "u256_fits_word" ||
  f == ofString "u256_is_zero" ||
  f == ofString "u256_limb" ||
  f == ofString "u256_bit" ||
  f == ofString "u256_eq" ||
  f == ofString "u256_lt" ||
  f == ofString "u256_gt" ||
  f == ofString "u256_slt" ||
  f == ofString "u256_sgt" ||
  f == ofString "u256_cmp" ||
  f == ofString "u256_not" ||
  f == ofString "u256_and" ||
  f == ofString "u256_or" ||
  f == ofString "u256_xor" ||
  f == ofString "u256_add_carry" ||
  f == ofString "u256_add" ||
  f == ofString "u256_sub" ||
  f == ofString "u256_neg" ||
  f == ofString "mul64x64" ||
  f == ofString "u256_mul" ||
  f == ofString "u256_mul_full" ||
  f == ofString "nlz32" ||
  f == ofString "div64by32" ||
  f == ofString "digits_to_u256" ||
  f == ofString "digits_len" ||
  f == ofString "u256_abs" ||
  f == ofString "bit_length64" ||
  f == ofString "u256_bit_length" ||
  f == ofString "u256_byte_length" ||
  f == ofString "u256_exp" ||
  f == ofString "u256_shl" ||
  f == ofString "u256_shr" ||
  f == ofString "u256_sar" ||
  f == ofString "u256_signextend" ||
  f == ofString "u256_byte" ||
  f == ofString "u256_from_be" ||
  f == ofString "htab_find_leaf" ||
  f == ofString "htab_has" ||
  f == ofString "acct_is_empty" ||
  f == ofString "sat_word" ||
  f == ofString "add_sat" ||
  f == ofString "ceil32" ||
  f == ofString "words_of" ||
  f == ofString "address_to_u256" ||
  f == ofString "memory_gas_cost" ||
  f == ofString "extend_memory_cost1" ||
  f == ofString "is_warm_address" ||
  f == ofString "access_gas_cost"

theorem opRoCallees_good :
    ∀ function, opRoCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg opRoCallees body = true := by
  intro function hfn values body callee rs hfound
  simp only [opRoCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with ((((((((((((((((((((((((((((((((((((((((((((((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · exact installed_body_readOnly 8 (by rw [guestAst_len]; decide) Guest.Software.guestFn_heap_mark rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 18 (by rw [guestAst_len]; decide) Guest.Software.guestFn_memeq rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 23 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bswap64 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 33 (by rw [guestAst_len]; decide) Guest.Software.guestFn_udivmod rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 34 (by rw [guestAst_len]; decide) Guest.Software.guestFn_udiv rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 39 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_word rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 40 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_low rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 41 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_fits_word rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 42 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_is_zero rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 43 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_limb rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 44 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_bit rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 45 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_eq rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 46 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_lt rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 47 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_gt rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 48 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_slt rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 49 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sgt rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 50 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_cmp rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 51 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_not rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 52 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_and rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 53 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_or rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 54 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_xor rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 55 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_add_carry rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 56 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_add rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 57 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sub rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 58 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_neg rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 59 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mul64x64 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 60 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mul rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 61 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mul_full rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 62 (by rw [guestAst_len]; decide) Guest.Software.guestFn_nlz32 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 63 (by rw [guestAst_len]; decide) Guest.Software.guestFn_div64by32 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 65 (by rw [guestAst_len]; decide) Guest.Software.guestFn_digits_to_u256 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 66 (by rw [guestAst_len]; decide) Guest.Software.guestFn_digits_len rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 72 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_abs rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 77 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bit_length64 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 78 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_bit_length rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 79 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_byte_length rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 80 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_exp rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 81 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_shl rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 82 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_shr rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 83 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sar rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 84 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_signextend rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 85 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_byte rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 86 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_be rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 131 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_find_leaf rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 133 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_has rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 384 (by rw [guestAst_len]; decide) Guest.Software.guestFn_acct_is_empty rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 440 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sat_word rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 441 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_sat rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 442 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ceil32 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 443 (by rw [guestAst_len]; decide) Guest.Software.guestFn_words_of rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 445 (by rw [guestAst_len]; decide) Guest.Software.guestFn_address_to_u256 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 457 (by rw [guestAst_len]; decide) Guest.Software.guestFn_memory_gas_cost rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 458 (by rw [guestAst_len]; decide) Guest.Software.guestFn_extend_memory_cost1 rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 471 (by rw [guestAst_len]; decide) Guest.Software.guestFn_is_warm_address rfl opRoCallees rfl hfound
  · exact installed_body_readOnly 473 (by rw [guestAst_len]; decide) Guest.Software.guestFn_access_gas_cost rfl opRoCallees rfl hfound

/-! ## 3. Individual `EvmPreservingSpec` theorems for read-only helpers -/

theorem eps_heap_mark : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "heap_mark") :=
  eps_of_readOnly 8 (by rw [guestAst_len]; decide) Guest.Software.guestFn_heap_mark rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_is_zero : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_is_zero") :=
  eps_of_readOnly 42 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_is_zero rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_eq : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_eq") :=
  eps_of_readOnly 45 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_eq rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_lt : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_lt") :=
  eps_of_readOnly 46 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_lt rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_gt : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_gt") :=
  eps_of_readOnly 47 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_gt rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_slt : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_slt") :=
  eps_of_readOnly 48 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_slt rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_sgt : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_sgt") :=
  eps_of_readOnly 49 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sgt rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_add_carry : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_add_carry") :=
  eps_of_readOnly 55 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_add_carry rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_add : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_add") :=
  eps_of_readOnly 56 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_add rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_sub : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_sub") :=
  eps_of_readOnly 57 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sub rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_neg : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_neg") :=
  eps_of_readOnly 58 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_neg rfl opRoCallees opRoCallees_good rfl

theorem eps_mul64x64 : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "mul64x64") :=
  eps_of_readOnly 59 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mul64x64 rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_mul : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_mul") :=
  eps_of_readOnly 60 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mul rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_mul_full : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_mul_full") :=
  eps_of_readOnly 61 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mul_full rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_abs : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_abs") :=
  eps_of_readOnly 72 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_abs rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_bit_length : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_bit_length") :=
  eps_of_readOnly 78 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_bit_length rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_exp : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_exp") :=
  eps_of_readOnly 80 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_exp rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_shl : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_shl") :=
  eps_of_readOnly 81 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_shl rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_shr : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_shr") :=
  eps_of_readOnly 82 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_shr rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_sar : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_sar") :=
  eps_of_readOnly 83 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sar rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_signextend : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_signextend") :=
  eps_of_readOnly 84 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_signextend rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_byte : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_byte") :=
  eps_of_readOnly 85 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_byte rfl opRoCallees opRoCallees_good rfl

theorem eps_u256_from_be : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "u256_from_be") :=
  eps_of_readOnly 86 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_be rfl opRoCallees opRoCallees_good rfl

theorem eps_acct_is_empty : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "acct_is_empty") :=
  eps_of_readOnly 384 (by rw [guestAst_len]; decide) Guest.Software.guestFn_acct_is_empty rfl opRoCallees opRoCallees_good rfl

theorem eps_sat_word : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "sat_word") :=
  eps_of_readOnly 440 (by rw [guestAst_len]; decide) Guest.Software.guestFn_sat_word rfl opRoCallees opRoCallees_good rfl

theorem eps_address_to_u256 : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "address_to_u256") :=
  eps_of_readOnly 445 (by rw [guestAst_len]; decide) Guest.Software.guestFn_address_to_u256 rfl opRoCallees opRoCallees_good rfl

theorem eps_extend_memory_cost1 : EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "extend_memory_cost1") :=
  eps_of_readOnly 458 (by rw [guestAst_len]; decide) Guest.Software.guestFn_extend_memory_cost1 rfl opRoCallees opRoCallees_good rfl

/-! ## 4. Return-value bounds for gas-cost helpers (`u256_byte_length`, `words_of`, `add_sat`, `access_gas_cost`) -/

/-- `u256_byte_length` is read-only and returns a word `≤ 32` (so `10 + 50 * nb` in `op_exp` never wraps and is `≥ 10 > 0`). -/
theorem eps_u256_byte_length_le32 :
    EvmPreservingSpec (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 32)
      (ofString "u256_byte_length") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ :=
    eps_of_readOnly 79 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_byte_length rfl
      opRoCallees opRoCallees_good rfl
  have hlk_eq := M13.lookup_u256_byte_length.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, M13.lookup_u256_byte_length, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hro s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, M13.u256_byte_length_body_le_32 s hcode v hv⟩

/-- `words_of(n)` returns `(ceil32(n)) >>> 5`, which is strictly `< 2 ^ 59`. -/
theorem words_of_body_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 59 := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_words_of,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  split at hret
  · simp at hret
  · split at hret
    · simp at hret
    · rename_i body' callee ret' hl
      split at hret
      · simp at hret
      · dsimp only at hret
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨rb, pb⟩
        rw [hrun] at hret
        rcases rb with _ | rb
        · simp at hret
        · cases rb with
          | returned vb =>
            dsimp only at hret
            split at hret
            · dsimp only at hret
              rw [evaluateHOLFiniteState_return] at hret
              set cs := setVarHOLFinite (ofString "c") vb { pb with locals := s.locals }
              have hcs_c : cs.locals.lookup (ofString "c") = some vb := by
                simp [cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rcases vb with ⟨⟨cw⟩⟩ | _ | _
              · have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
                have hev : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
                    (.shift .lsr (.var .local (ofString "c")) (.const 5#64)) =
                    some (.val (.word (cw >>> (5 : Nat)))) := by
                  simp [evalHOLExact, hcs_c, wordShiftHOL, h5]
                rw [hev] at hret; dsimp only at hret
                split at hret
                · injection hret with h1; injection h1 with hv
                  refine ⟨cw >>> (5 : Nat), hv.symm, ?_⟩
                  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                  have hcw := cw.isLt
                  have : (2 ^ 64 : Nat) = 2 ^ 59 * 2 ^ 5 := by decide
                  omega
                · simp at hret
              · simp [evalHOLExact, hcs_c, wordShiftHOL] at hret
              · simp [evalHOLExact, hcs_c, wordShiftHOL] at hret
            · simp at hret
          | _ => simp at hret

theorem lookup_words_of :
    originalRuntimeCode.lookup (ofString "words_of") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_words_of, .one) :=
  lookup_of_guestAst_getElem 443 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_words_of) rfl

theorem eps_words_of_lt :
    EvmPreservingSpec (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 59)
      (ofString "words_of") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ :=
    eps_of_readOnly 443 (by rw [guestAst_len]; decide) Guest.Software.guestFn_words_of rfl
      opRoCallees opRoCallees_good rfl
  have hlk_eq := lookup_words_of.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_words_of, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hro s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, words_of_body_lt s v hv⟩

/-- `add_sat(a, b)` returns `max_sat(a + b)` which is always `≥ a.toNat`! -/
theorem add_sat_body_ge {F : Type} (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧ aw.toNat ≤ rw.toNat := by
  have hbody : sourceFnBody Guest.Software.guestFn_add_sat =
      .dec (ofString "s") .one (.op .add [.var .local (ofString "a"), .var .local (ofString "b")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a")))
            (.return (.const 18446744073709551615#64))
            .skip)
          (.return (.var .local (ofString "s")))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hsum : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [.var .local (ofString "a"), .var .local (ofString "b")]) =
      some (.val (.word (aw + bw))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hsum] at hret; dsimp only at hret
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (aw + bw)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh] at hret; dsimp only at hret
  set s1 := setVarHOLFinite (ofString "s") (.val (.word (aw + bw))) s
  have hs1_s : s1.locals.lookup (ofString "s") = some (.val (.word (aw + bw))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "s" ≠ ofString "a" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a"))) =
      some (.val (.word (if (aw + bw) < aw then 1 else 0))) := by
    simp [evalHOLExact, hs1_s, hs1_a, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  by_cases hlt : (aw + bw) < aw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨18446744073709551615#64, hv.symm, ?_⟩
    have haw := aw.isLt
    have : (18446744073709551615#64 : BitVec 64).toNat = 18446744073709551615 := rfl
    omega
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_s : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "s")) = some (.val (.word (aw + bw))) := hs1_s
    rw [hev_s] at hret; dsimp only at hret
    split at hret
    · injection hret with h1; injection h1 with hv
      refine ⟨aw + bw, hv.symm, ?_⟩
      rw [BitVec.lt_def] at hlt; omega
    · simp at hret

theorem lookup_add_sat :
    originalRuntimeCode.lookup (ofString "add_sat") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_add_sat, .one) :=
  lookup_of_guestAst_getElem 441 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_sat) rfl

theorem two_word_arg_lookup {fname p1 p2 : MlS} {body : ProgHOL 64}
    {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body', callee, ret')) :
    body' = body ∧ ret' = .one ∧ ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      callee.lookup p1 = some (.val (.word w1)) ∧
      callee.lookup p2 = some (.val (.word w2)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases hx with ⟨_, hbody_eq, hloc, hret_eq⟩
    refine ⟨hbody_eq.symm, hret_eq.symm, w1, w2, rfl, ?_, ?_⟩
    · have hfn := congrFun hloc.symm p1
      simpa [FUPDATE_LIST, FUPDATE, hne, Ne.symm hne] using hfn
    · have hfn := congrFun hloc.symm p2
      simpa [FUPDATE_LIST, FUPDATE, hne, Ne.symm hne] using hfn
  · simp at hx

theorem eps_add_sat_pos :
    EvmPreservingSpec
      (fun s => ∃ aw : BitVec 64, s.locals.lookup (ofString "a") = some (.val (.word aw)) ∧ 0 < aw.toNat)
      (fun s v post => LocFrame s post ∧ ∃ rw : BitVec 64, v = .val (.word rw) ∧ 0 < rw.toNat)
      (ofString "add_sat") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ :=
    eps_of_readOnly 441 (by rw [guestAst_len]; decide) Guest.Software.guestFn_add_sat rfl
      opRoCallees opRoCallees_good rfl
  have hlk_eq : some ([(ofString "a", ShapeHOL.one), (ofString "b", ShapeHOL.one)],
      sourceFnBody Guest.Software.guestFn_add_sat, ShapeHOL.one) =
      some (params, body, retShape) := lookup_add_sat.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_add_sat, ?_⟩
  intro F s hcode hInv ⟨aw, haw, hpos⟩ ⟨vals, hl⟩ hnt
  have hs := hro s hcode hInv trivial ⟨vals, hl⟩ hnt
  dsimp only at hs ⊢
  obtain ⟨_, _, w1, w2, rfl, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl
  rw [haw] at hw1; injection hw1 with hw1'; injection hw1' with hw1''; injection hw1'' with hw_eq; subst hw_eq
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  obtain ⟨rw, rfl, hrw_ge⟩ := add_sat_body_ge s haw hw2 v hv
  exact ⟨h1, h2, h3, hlf, rw, rfl, by omega⟩

/-- `access_gas_cost(addr)` returns either `100` (`G_WARM_ACCESS`) or `3000` (`G_COLD_ACCOUNT_ACCESS`). -/
theorem access_gas_cost_body_bounds {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_access_gas_cost)).1 =
      some (.returned v)) :
    ∃ cw : BitVec 64, v = .val (.word cw) ∧ (cw.toNat = 100 ∨ cw.toNat = 3000) := by
  have hbody : sourceFnBody Guest.Software.guestFn_access_gas_cost =
      .decCall (ofString "w") .one (ofString "is_warm_address") [.var .local (ofString "addr")]
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "w")) (.const 0#64))
            (.return (.const 100#64))
            .skip)
          (.return (.const 3000#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  split at hret
  · simp at hret
  · split at hret
    · simp at hret
    · rename_i body' callee ret' _
      split at hret
      · simp at hret
      · dsimp only at hret
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨rb, pb⟩
        rw [hrun] at hret
        rcases rb with _ | rb
        · simp at hret
        · cases rb with
          | returned vb =>
            dsimp only at hret
            split at hret
            · dsimp only at hret
              set cs := setVarHOLFinite (ofString "w") vb { pb with locals := s.locals }
              change (evaluateHOLFiniteState cs
                (.seq
                  (.ite (.cmp .notEqual (.var .local (ofString "w")) (.const 0#64))
                    (.return (.const 100#64))
                    .skip)
                  (.return (.const 3000#64)))).1 = some (.returned v) at hret
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
              split at hret
              · split at hret
                · rw [evaluateHOLFiniteState_skip] at hret; dsimp only at hret
                  rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
                  have hsz3000 : sizeOfShapeWithContextHOL cs.structs
                      (shapeOfHOLExact (.val (.word 3000#64))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz3000] at hret; dsimp only at hret
                  injection hret with h1; injection h1 with hv
                  exact ⟨3000#64, hv.symm, Or.inr rfl⟩
                · rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
                  have hsz100 : sizeOfShapeWithContextHOL cs.structs
                      (shapeOfHOLExact (.val (.word 100#64))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz100] at hret; dsimp only at hret
                  injection hret with h1; injection h1 with hv
                  exact ⟨100#64, hv.symm, Or.inl rfl⟩
              · simp at hret
            · simp at hret
          | _ => simp at hret

theorem lookup_access_gas_cost :
    originalRuntimeCode.lookup (ofString "access_gas_cost") =
      some ([(ofString "addr", .one)], sourceFnBody Guest.Software.guestFn_access_gas_cost, .one) :=
  lookup_of_guestAst_getElem 473 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_access_gas_cost) rfl

theorem eps_access_gas_cost_bounds :
    EvmPreservingSpec (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ cw : BitVec 64, v = .val (.word cw) ∧ (cw.toNat = 100 ∨ cw.toNat = 3000))
      (ofString "access_gas_cost") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ :=
    eps_of_readOnly 473 (by rw [guestAst_len]; decide) Guest.Software.guestFn_access_gas_cost rfl
      opRoCallees opRoCallees_good rfl
  have hlk_eq := lookup_access_gas_cost.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_access_gas_cost, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hro s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, access_gas_cost_body_bounds s v hv⟩

end InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
