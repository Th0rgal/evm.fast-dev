import InitECandidate.Solver.Wave8GuestInv.Deliveries.M22.EvmLemmas

/-! `ek_is_warm_storage_key`: `is_warm_storage_key` keeps `EvmInv`, `heap_ptr`, all globals
(`gw = []`), and `evmChain`.
Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

AST index 525 (`Guest/SoftwareAst.lean:16559`):
```
decCall "k" .one "sk_make" [addr, key]
  (decCall "h" .one "htab_has" [load .one (ev + 176), k]
    (return h))
```
1. `sk_make(addr, key)` calls `memcpy(sk_buf, addr, 20)` and `memcpy(sk_buf + 20, key, 32)` and
   returns `sk_buf`. If `globN s "sk_buf" = 0`, the first `memcpy` fails to store at address `0`
   (outside `ordinaryDomain`), so `sk_make` cannot resume. When `globN s "sk_buf" ≠ 0`,
   `(globN s "sk_buf", 64) ∈ fixedObjects s`, and `sk_make` satisfies
   `ByteRegionEffect s post_sk [(globN s "sk_buf", 64)]`.
2. `htab_has` is purely read-only (`htab_find_leaf`, `memeq`), changing only `locals` and `clock`,
   so its `ByteRegionEffect` is `refl` (modulo `locals` and `clock`).
3. Under `EvmInv s`, `(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64)` is an untyped
   global buffer in `fixedObjects s`, disjoint from every interval in `worldTypedIvls s S Nd_at`
   and disjoint from every frame object in `evmChain s`, so `ByteRegionEffect.to_evmStep_nil_with`
   (extended to zero-length or disjoint intervals) yields `EvmStep [] s post`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M22

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

private theorem lookup_memeq :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memeq, .one) :=
  lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

private theorem lookup_htab_find_leaf :
    originalRuntimeCode.lookup (ofString "htab_find_leaf") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_find_leaf, .one) :=
  lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_find_leaf) rfl

private theorem lookup_htab_has :
    originalRuntimeCode.lookup (ofString "htab_has") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_has, .one) :=
  lookup_of_guestAst_getElem 133 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_has) rfl

private theorem lookup_sk_make :
    originalRuntimeCode.lookup (ofString "sk_make") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_sk_make, .one) :=
  lookup_of_guestAst_getElem 360 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_sk_make) rfl

private theorem lookup_is_warm_storage_key :
    originalRuntimeCode.lookup (ofString "is_warm_storage_key") =
      some ([(ofString "addr", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_is_warm_storage_key, .one) :=
  lookup_of_guestAst_getElem 525 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_warm_storage_key) rfl

private theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem not_resumes_timeOut : ¬ Resumes (some (.timeOut : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

/-! ## 1. Read-only evaluation of `htab_has` -/

private def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

private theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

private theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *; rw [h2, h1]

private theorem LocFrame.with_locals_clock {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    LocFrame s { t with locals := locals, clock := k } := by
  unfold LocFrame at h ⊢; rw [h]

private def readOnlyProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => readOnlyProg good body
  | .seq first second => readOnlyProg good first && readOnlyProg good second
  | .ite _ yes no => readOnlyProg good yes && readOnlyProg good no
  | .while _ body => readOnlyProg good body
  | .decCall _ _ fname _ cont => good fname && readOnlyProg good cont
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

private theorem lex_of {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

private theorem evaluate_readOnlyProg {F : Type} (good : MlS → Bool)
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
        unfold LocFrame at ih ⊢; dsimp only; rw [ih]; rfl
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
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            have ih1' : LocFrame state middle := by unfold LocFrame at ih1 ⊢; rw [ih1]; rfl
            cases result with
            | none =>
              exact ih1'.trans (evaluate_readOnlyProg good hgood (.while condition body)
                (by simpa [readOnlyProg] using child) middle mCode)
            | some result =>
              cases result with
              | «continue» =>
                exact ih1'.trans (evaluate_readOnlyProg good hgood (.while condition body)
                  (by simpa [readOnlyProg] using child) middle mCode)
              | «break» | returned _ | exception _ _ | finalFfi _ | error | timeOut => exact ih1'
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
            have ih' : LocFrame state st := by unfold LocFrame at ih ⊢; rw [ih]; rfl
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
              | timeOut | error | exception _ _ | finalFfi _ => exact ih'.with_locals_clock _ _
              | «break» | «continue» => exact ih'
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

private def htabHasCallees (f : MlS) : Bool :=
  f == ofString "htab_has" || f == ofString "htab_find_leaf" || f == ofString "memeq"

private theorem htabHasCallees_good :
    ∀ function, htabHasCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg htabHasCallees body = true := by
  intro function hfn values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [htabHasCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with (rfl | rfl) | rfl
  · have hl := lookup_htab_has
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl
  · have hl := lookup_htab_find_leaf
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl
  · have hl := lookup_memeq
    rw [hl] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl

/-! ## 2. `ByteRegionEffect` of `memcpy(dst, src, n)` when `dst.toNat + n.toNat ≤ 2^64` -/

private def noReturnOrRaise : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise a && noReturnOrRaise b
  | .ite _ a b => noReturnOrRaise a && noReturnOrRaise b
  | .while _ a => noReturnOrRaise a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturnOrRaise {F : Type} (p : ProgHOL 64) (hp : noReturnOrRaise p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ¬ Resumes (evaluateHOLFiniteState s p).1 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact not_resumes_error
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | seq a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnOrRaise a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturnOrRaise b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnOrRaise b hab.2 s
      · exact evaluate_noReturnOrRaise a hab.1 s
    · exact not_resumes_error
  | «while» cond body =>
    have hb : noReturnOrRaise body = true := by simpa [shape, noReturnOrRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · rename_i nonzero
          have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnOrRaise body hb (decClockHOLFinite s)
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
            | «break» | timeOut | finalFfi _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | returned _ | exception _ _ => exact ih1
            | error => exact not_resumes_error
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error
  | _ => simp [shape, noReturnOrRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private def noBreak : ProgHOL 64 → Bool
  | .break => false
  | .seq a b => noBreak a && noBreak b
  | .ite _ a b => noBreak a && noBreak b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreak {F : Type} (p : ProgHOL 64) (hp : noBreak p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break := by
  cases shape : p with
  | «break» => simp [shape, noBreak] at hp
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreak] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreak a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreak b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreak b hab.2 s
      · exact evaluate_noBreak a hab.1 s
    · simp
  | _ => simp [shape, noBreak] at hp

private def MemcpyEffInv {F : Type} (dst0 n0 : BitVec 64) (Rl : List Ivl)
    (s0 s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧
  s.memaddrs = ordinaryDomain ∧
  ByteRegionEffect s0 s Rl ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat)

private theorem eval_load_one_isWord {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (val : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some val) :
    ∃ w : BitVec 64, val = .val (.word w) := by
  simp only [evalHOLExact] at he
  split at he
  · split at he
    · rename_i addr _
      simp only [memLoadHOLExact] at he
      split at he
      · cases hw : s.memory addr with
        | word w =>
          have hv : val = .val (s.memory addr) := (Option.some.inj he).symm
          rw [hw] at hv
          exact ⟨w, hv⟩
      · simp at he
    · simp at he
  · simp at he

private theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y a : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i]) = some (.val (.word a))) :
    a = x + y := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp] at he
  exact he.symm

private theorem eval_add3_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y c a : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i, .const c]) = some (.val (.word a))) :
    a = x + y + c := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp] at he
  rw [← he, BitVec.add_assoc]

private theorem eval_notLower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw k w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const k])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    ¬ (n0 < iw + k) := by
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL] at he
  intro hlt
  have hnotle : ¬ (iw + k ≤ n0) := by
    rw [BitVec.lt_def] at hlt; rw [BitVec.le_def]; omega
  simp [hnotle] at he
  exact hw he.symm

private theorem eval_lower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    iw < n0 := by
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_contra hge
  simp [hge] at he
  exact hw he.symm

private theorem eval_lower_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word 0))) :
    n0.toNat ≤ iw.toNat := by
  simp only [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_cases hlt : iw < n0
  · simp [hlt] at he
  · rw [BitVec.lt_def] at hlt; omega

private theorem while_preserve_eff {F : Type} {dst0 n0 : BitVec 64} {Rl : List Ivl}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s0 s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s0 s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemcpyEffInv dst0 n0 Rl s0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemcpyEffInv dst0 n0 Rl s0 post ∧
      @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
        some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nb := evaluate_noBreak body hnb (decClockHOLFinite s)
          have nc := evaluate_noTopContinue body hnc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nb nc
          cases r1 with
          | none =>
            have hmid : MemcpyEffInv dst0 n0 Rl s0 mid := by
              have hb := hbody s0 s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            have hmk : mid.clock ≤ k := by change mid.clock ≤ s.clock - 1 at rem; omega
            exact ih mid hmk hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

/-- Helper for a single word store `store (dst + i [+ off]) (load .one ...)` inside `memcpy` when
`dst0.toNat + n0.toNat ≤ 2^64` and `(dst0.toNat, n0.toNat) ∈ Rl`. -/
private theorem memcpy_store_word_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst0 iw n0 : BitVec 64} {Rl : List Ivl}
    {dstExp srcExp : ExpHOL 64} {off : Nat}
    (hma : s.memaddrs = ordinaryDomain)
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_rl : (dst0.toNat, n0.toNat) ∈ Rl)
    (hiw_end : iw.toNat + off + 8 ≤ n0.toNat)
    (hrun : evaluateHOLFiniteState s (.store dstExp (.load .one srcExp)) = (none, post))
    (hdst_ev : ∀ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dstExp =
        some (.val (.word a)) → a.toNat = dst0.toNat + iw.toNat + off) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals ∧
      sourceBase ≤ dst0.toNat + iw.toNat + off := by
  have hd : sourceBase ≤ dst0.toNat + iw.toNat + off := by
    rw [evaluateHOLFiniteState_store] at hrun
    split at hrun
    · rename_i addr had
      split at hrun
      · rename_i val hv
        obtain ⟨w, rfl⟩ := eval_load_one_isWord s srcExp val hv
        split at hrun
        · rename_i mem hmem
          have hdom : s.memaddrs addr := by
            simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
            by_contra hc; simp [hc] at hmem
          rw [hma, ordinaryDomain_iff] at hdom
          have ha_eq := hdst_ev addr had
          rw [sourceBase_val]; omega
        · simp at hrun
      · simp at hrun
    · simp at hrun
  have he := ByteRegionEffect.of_store_word hma hrun (eval_load_one_isWord s srcExp)
    (fun addr had _ => ⟨(dst0.toNat, n0.toNat), hin_rl, by have := hdst_ev addr had; omega,
      by have := hdst_ev addr had; omega⟩)
  exact ⟨he.1, he.2, hd⟩

private theorem memcpy_storeByte_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {dst0 iw n0 : BitVec 64} {Rl : List Ivl}
    {dstExp valExp : ExpHOL 64} {off : Nat}
    (hma : s.memaddrs = ordinaryDomain)
    (_hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_rl : (dst0.toNat, n0.toNat) ∈ Rl)
    (hiw_end : iw.toNat + off < n0.toNat)
    (hrun : evaluateHOLFiniteState s (.storeByte dstExp valExp) = (none, post))
    (hdst_ev : ∀ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dstExp =
        some (.val (.word a)) → a.toNat = dst0.toNat + iw.toNat + off) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals ∧
      sourceBase ≤ dst0.toNat + iw.toNat + off := by
  have hd : sourceBase ≤ dst0.toNat + iw.toNat + off := by
    rw [evaluateHOLFiniteState_storeByte] at hrun
    split at hrun
    · rename_i addr had
      split at hrun
      · split at hrun
        · rename_i mem hmem
          have hdom : s.memaddrs (panByteAlignHOL addr) := by
            by_contra hc
            revert hmem
            simp only [panMemStoreByteWord8HOL]
            split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
          rw [hma, ordinaryDomain_iff] at hdom
          have hal : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 := panByteAlign_toNat64 addr
          have ha_eq := hdst_ev addr had
          rw [sourceBase_val]; omega
        · simp at hrun
      · simp at hrun
    · simp at hrun
  have he := ByteRegionEffect.of_storeByte hrun
    (fun addr had _ => ⟨(dst0.toNat, n0.toNat), hin_rl, by have := hdst_ev addr had; omega,
      by have := hdst_ev addr had; omega⟩)
  exact ⟨he.1, he.2, hd⟩

private theorem assign_i_add_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {iw k : BitVec 64} {Rl : List Ivl}
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) = (none, post)) :
    ByteRegionEffect s post Rl ∧
      post.locals.lookup (ofString "i") = some (.val (.word (iw + k))) ∧
      (∀ m, m ≠ ofString "i" → post.locals.lookup m = s.locals.lookup m) := by
  rw [evaluateHOLFiniteState_assign] at hrun
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "i"), .const k]) = some (.val (.word (iw + k))) := by
    simp [evalHOLExact, evalListHOLExact, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hval : s.isValidValueHOLFinite .local (ofString "i") (.val (.word (iw + k))) = true := by
    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hi, shapeOfHOLExact, shapeEqHOL]
  rw [hev] at hrun; dsimp only at hrun; rw [if_pos hval] at hrun
  injection hrun with _ hpost
  subst hpost
  refine ⟨(ByteRegionEffect.refl s Rl).with_locals_clock _ _, ?_, ?_⟩
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · intro m hm
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hm]

/-- When `n0.toNat ≤ 64` and `dst0.toNat + n0.toNat ≤ 2^64` (and `0 < n0.toNat`), any resuming
evaluation of `memcpy(dst0, src0, n0)` requires `sourceBase ≤ dst0.toNat` and produces
`ByteRegionEffect s post Rl` whenever `(dst0.toNat, n0.toNat) ∈ Rl`. -/
private theorem eval_memcpy_bounded {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (_hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hn_pos : 0 < n0.toNat)
    (hn_small : n0.toNat ≤ 64)
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_rl : (dst0.toNat, n0.toNat) ∈ Rl)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 =
      some (.returned (.val (.word 0))) ∧
    sourceBase ≤ dst0.toNat ∧
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).2 Rl := by
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  have hiv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hiv]; dsimp only; rw [if_pos hsh0]
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s with hs1
  have hinv1 : MemcpyEffInv dst0 n0 Rl s s1 := by
    refine ⟨hcode, hma, (ByteRegionEffect.refl s Rl).with_locals_clock _ _, ?_, ?_, 0, ?_, Nat.zero_le _,
      fun h => by simp at h⟩
    · have hne : ofString "dst" ≠ ofString "i" := by decide
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, hdst]
    · have hne : ofString "n" ≠ ofString "i" := by decide
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, hn]
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Helper: when `iw.toNat ≤ n0.toNat ≤ 64`, `¬ (n0 < iw + k)` for `k ∈ {8, 32}` implies `iw.toNat + k.toNat ≤ n0.toNat`!
  have hnw_step : ∀ (iw k : BitVec 64), iw.toNat ≤ n0.toNat → k.toNat ≤ 32 → ¬ (n0 < iw + k) →
      (iw + k).toNat = iw.toNat + k.toNat ∧ iw.toNat + k.toNat ≤ n0.toNat := by
    intro iw k hiw hk hnl
    have hsum_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd : (iw + k).toNat = iw.toNat + k.toNat := BitVec.toNat_add_of_lt hsum_lt
    rw [BitVec.lt_def, hadd] at hnl
    exact ⟨hadd, by omega⟩
  have hdom_first : ∀ (iw : BitVec 64), (0 < iw.toNat → sourceBase ≤ dst0.toNat) →
      sourceBase ≤ dst0.toNat + iw.toNat + 0 → sourceBase ≤ dst0.toNat := by
    intro iw hprev h0
    by_cases hiz : iw.toNat = 0
    · omega
    · exact hprev (by omega)
  -- Step proofs for loop1 (32), loop2 (8 word), loop3 (8 byte), loop4 (1 byte):
  have hstep1 : ∀ (s0 t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)) →
      w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                  (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                  (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))).2 := by
    intro s0 t w ⟨hc, hm, heff0, ht_d, ht_n, iw, ht_i, hiw_le, hdprev⟩ hcond hw hnone
    have hnl := eval_notLower_true t n0 iw 32 w ht_n ht_i hcond hw
    obtain ⟨hik_eq, hik_le⟩ := hnw_step iw 32 hiw_le (by decide) hnl
    have h32_nat : (32 : BitVec 64).toNat = 32 := rfl
    rw [h32_nat] at hik_eq hik_le
    let t0 := decClockHOLFinite t
    have hm0 : t0.memaddrs = ordinaryDomain := hm
    rcases hr : evaluateHOLFiniteState t0 _ with ⟨r_all, post_b⟩
    rw [hr] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs0 : evaluateHOLFiniteState t0 _ with ⟨r0, m1⟩
    rw [hs0] at hr; cases r0 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he0, hl0, hsb0⟩ := memcpy_store_word_step (s := t0) (iw := iw) (off := 0) hm0 hfit hin_rl (by omega) hs0
      (fun a ha => by
        rw [eval_add2_locals t0 _ _ dst0 iw a ht_d ht_i ha, BitVec.toNat_add_of_lt (by omega)]; omega)
    have hdst_sb := hdom_first iw hdprev hsb0
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs8 : evaluateHOLFiniteState m1 _ with ⟨r8, m2⟩
    rw [hs8] at hr; cases r8 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he8, hl8, _⟩ := memcpy_store_word_step (s := m1) (iw := iw) (off := 8) (he0.memaddrs.trans hm0) hfit hin_rl (by omega) hs8
      (fun a ha => by
        rw [eval_add3_locals m1 _ _ dst0 iw 8 a (hl0 ▸ ht_d) (hl0 ▸ ht_i) ha]
        rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 8 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs16 : evaluateHOLFiniteState m2 _ with ⟨r16, m3⟩
    rw [hs16] at hr; cases r16 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he16, hl16, _⟩ := memcpy_store_word_step (s := m2) (iw := iw) (off := 16) (he8.memaddrs.trans (he0.memaddrs.trans hm0)) hfit hin_rl (by omega) hs16
      (fun a ha => by
        rw [eval_add3_locals m2 _ _ dst0 iw 16 a (hl8 ▸ hl0 ▸ ht_d) (hl8 ▸ hl0 ▸ ht_i) ha]
        rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 16 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs24 : evaluateHOLFiniteState m3 _ with ⟨r24, m4⟩
    rw [hs24] at hr; cases r24 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he24, hl24, _⟩ := memcpy_store_word_step (s := m3) (iw := iw) (off := 24) (he16.memaddrs.trans (he8.memaddrs.trans (he0.memaddrs.trans hm0))) hfit hin_rl (by omega) hs24
      (fun a ha => by
        rw [eval_add3_locals m3 _ _ dst0 iw 24 a (hl16 ▸ hl8 ▸ hl0 ▸ ht_d) (hl16 ▸ hl8 ▸ hl0 ▸ ht_i) ha]
        rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 24 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    obtain ⟨he_asg, hi_post, hother_post⟩ := assign_i_add_step (Rl := Rl) (hl24 ▸ hl16 ▸ hl8 ▸ hl0 ▸ ht_i) hr
    have heff_all : ByteRegionEffect s0 post_b Rl :=
      ((((heff0.with_locals_clock t.locals (t.clock - 1)).trans he0).trans he8).trans he16).trans (he24.trans he_asg)
    refine ⟨heff_all.code.trans (heff0.code.symm.trans hc),
      heff_all.memaddrs.trans (heff0.memaddrs.symm.trans hm),
      heff_all, ?_, ?_, iw + 32, hi_post, by rw [hik_eq]; omega, fun _ => hdst_sb⟩
    · rw [hother_post _ (by decide), hl24, hl16, hl8, hl0]; exact ht_d
    · rw [hother_post _ (by decide), hl24, hl16, hl8, hl0]; exact ht_n
  have hstep2 : ∀ (s0 t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)) →
      w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))).2 := by
    intro s0 t w ⟨hc, hm, heff0, ht_d, ht_n, iw, ht_i, hiw_le, hdprev⟩ hcond hw hnone
    have hnl := eval_notLower_true t n0 iw 8 w ht_n ht_i hcond hw
    obtain ⟨hik_eq, hik_le⟩ := hnw_step iw 8 hiw_le (by decide) hnl
    have h8_nat : (8 : BitVec 64).toNat = 8 := rfl
    rw [h8_nat] at hik_eq hik_le
    let t0 := decClockHOLFinite t
    have hm0 : t0.memaddrs = ordinaryDomain := hm
    rcases hr : evaluateHOLFiniteState t0 _ with ⟨r_all, post_b⟩
    rw [hr] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs0 : evaluateHOLFiniteState t0 _ with ⟨r0, m1⟩
    rw [hs0] at hr; cases r0 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he0, hl0, hsb0⟩ := memcpy_store_word_step (s := t0) (iw := iw) (off := 0) hm0 hfit hin_rl (by omega) hs0
      (fun a ha => by
        rw [eval_add2_locals t0 _ _ dst0 iw a ht_d ht_i ha, BitVec.toNat_add_of_lt (by omega)]; omega)
    have hdst_sb := hdom_first iw hdprev hsb0
    obtain ⟨he_asg, hi_post, hother_post⟩ := assign_i_add_step (Rl := Rl) (hl0 ▸ ht_i) hr
    have heff_all : ByteRegionEffect s0 post_b Rl :=
      ((heff0.with_locals_clock t.locals (t.clock - 1)).trans he0).trans he_asg
    refine ⟨heff_all.code.trans (heff0.code.symm.trans hc),
      heff_all.memaddrs.trans (heff0.memaddrs.symm.trans hm),
      heff_all, ?_, ?_, iw + 8, hi_post, by rw [hik_eq]; omega, fun _ => hdst_sb⟩
    · rw [hother_post _ (by decide), hl0]; exact ht_d
    · rw [hother_post _ (by decide), hl0]; exact ht_n
  have hstep3 : ∀ (s0 t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)) →
      w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))).2 := by
    intro s0 t w ⟨hc, hm, heff0, ht_d, ht_n, iw, ht_i, hiw_le, hdprev⟩ hcond hw hnone
    have hnl := eval_notLower_true t n0 iw 8 w ht_n ht_i hcond hw
    obtain ⟨hik_eq, hik_le⟩ := hnw_step iw 8 hiw_le (by decide) hnl
    have h8_nat : (8 : BitVec 64).toNat = 8 := rfl
    rw [h8_nat] at hik_eq hik_le
    let t0 := decClockHOLFinite t
    have hm0 : t0.memaddrs = ordinaryDomain := hm
    rcases hr : evaluateHOLFiniteState t0 _ with ⟨r_all, post_b⟩
    rw [hr] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs0 : evaluateHOLFiniteState t0 _ with ⟨r0, m1⟩
    rw [hs0] at hr; cases r0 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he0, hl0, hsb0⟩ := memcpy_storeByte_step (s := t0) (iw := iw) (off := 0) hm0 hfit hin_rl (by omega) hs0
      (fun a ha => by rw [eval_add2_locals t0 _ _ dst0 iw a ht_d ht_i ha, BitVec.toNat_add_of_lt (by omega)]; omega)
    have hdst_sb := hdom_first iw hdprev hsb0
    have hd1 : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl0 ▸ ht_d
    have hi1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := hl0 ▸ ht_i
    have hm1 : m1.memaddrs = ordinaryDomain := he0.memaddrs.trans hm0
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs1 : evaluateHOLFiniteState m1 _ with ⟨r1, m2⟩
    rw [hs1] at hr; cases r1 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he1, hl1, _⟩ := memcpy_storeByte_step (s := m1) (iw := iw) (off := 1) hm1 hfit hin_rl (by omega) hs1
      (fun a ha => by
        rw [eval_add3_locals m1 _ _ dst0 iw 1 a hd1 hi1 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 1 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd2 : m2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl1 ▸ hd1
    have hi2 : m2.locals.lookup (ofString "i") = some (.val (.word iw)) := hl1 ▸ hi1
    have hm2 : m2.memaddrs = ordinaryDomain := he1.memaddrs.trans hm1
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs2 : evaluateHOLFiniteState m2 _ with ⟨r2, m3⟩
    rw [hs2] at hr; cases r2 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he2, hl2, _⟩ := memcpy_storeByte_step (s := m2) (iw := iw) (off := 2) hm2 hfit hin_rl (by omega) hs2
      (fun a ha => by
        rw [eval_add3_locals m2 _ _ dst0 iw 2 a hd2 hi2 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 2 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd3 : m3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl2 ▸ hd2
    have hi3 : m3.locals.lookup (ofString "i") = some (.val (.word iw)) := hl2 ▸ hi2
    have hm3 : m3.memaddrs = ordinaryDomain := he2.memaddrs.trans hm2
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs3 : evaluateHOLFiniteState m3 _ with ⟨r3, m4⟩
    rw [hs3] at hr; cases r3 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he3, hl3, _⟩ := memcpy_storeByte_step (s := m3) (iw := iw) (off := 3) hm3 hfit hin_rl (by omega) hs3
      (fun a ha => by
        rw [eval_add3_locals m3 _ _ dst0 iw 3 a hd3 hi3 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 3 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd4 : m4.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl3 ▸ hd3
    have hi4 : m4.locals.lookup (ofString "i") = some (.val (.word iw)) := hl3 ▸ hi3
    have hm4 : m4.memaddrs = ordinaryDomain := he3.memaddrs.trans hm3
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs4 : evaluateHOLFiniteState m4 _ with ⟨r4, m5⟩
    rw [hs4] at hr; cases r4 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he4, hl4, _⟩ := memcpy_storeByte_step (s := m4) (iw := iw) (off := 4) hm4 hfit hin_rl (by omega) hs4
      (fun a ha => by
        rw [eval_add3_locals m4 _ _ dst0 iw 4 a hd4 hi4 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 4 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd5 : m5.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl4 ▸ hd4
    have hi5 : m5.locals.lookup (ofString "i") = some (.val (.word iw)) := hl4 ▸ hi4
    have hm5 : m5.memaddrs = ordinaryDomain := he4.memaddrs.trans hm4
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs5 : evaluateHOLFiniteState m5 _ with ⟨r5, m6⟩
    rw [hs5] at hr; cases r5 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he5, hl5, _⟩ := memcpy_storeByte_step (s := m5) (iw := iw) (off := 5) hm5 hfit hin_rl (by omega) hs5
      (fun a ha => by
        rw [eval_add3_locals m5 _ _ dst0 iw 5 a hd5 hi5 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 5 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd6 : m6.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl5 ▸ hd5
    have hi6 : m6.locals.lookup (ofString "i") = some (.val (.word iw)) := hl5 ▸ hi5
    have hm6 : m6.memaddrs = ordinaryDomain := he5.memaddrs.trans hm5
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs6 : evaluateHOLFiniteState m6 _ with ⟨r6, m7⟩
    rw [hs6] at hr; cases r6 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he6, hl6, _⟩ := memcpy_storeByte_step (s := m6) (iw := iw) (off := 6) hm6 hfit hin_rl (by omega) hs6
      (fun a ha => by
        rw [eval_add3_locals m6 _ _ dst0 iw 6 a hd6 hi6 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 6 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    have hd7 : m7.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hl6 ▸ hd6
    have hi7 : m7.locals.lookup (ofString "i") = some (.val (.word iw)) := hl6 ▸ hi6
    have hm7 : m7.memaddrs = ordinaryDomain := he6.memaddrs.trans hm6
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs7 : evaluateHOLFiniteState m7 _ with ⟨r7, m8⟩
    rw [hs7] at hr; cases r7 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he7, hl7, _⟩ := memcpy_storeByte_step (s := m7) (iw := iw) (off := 7) hm7 hfit hin_rl (by omega) hs7
      (fun a ha => by
        rw [eval_add3_locals m7 _ _ dst0 iw 7 a hd7 hi7 ha,
            BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; change _ + 7 < _; omega),
            BitVec.toNat_add_of_lt (by omega)]; rfl)
    obtain ⟨he_asg, hi_post, hother_post⟩ := assign_i_add_step (Rl := Rl) (hl7 ▸ hi7) hr
    have heff_all : ByteRegionEffect s0 post_b Rl :=
      ((((((((heff0.with_locals_clock t.locals (t.clock - 1)).trans he0).trans he1).trans he2).trans
        he3).trans he4).trans he5).trans he6).trans (he7.trans he_asg)
    refine ⟨heff_all.code.trans (heff0.code.symm.trans hc),
      heff_all.memaddrs.trans (heff0.memaddrs.symm.trans hm),
      heff_all, ?_, ?_, iw + 8, hi_post, by rw [hik_eq]; omega, fun _ => hdst_sb⟩
    · rw [hother_post _ (by decide), hl7]; exact hd7
    · rw [hother_post _ (by decide), hl7, hl6, hl5, hl4, hl3, hl2, hl1, hl0]; exact ht_n
  have hstep4 : ∀ (s0 t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyEffInv dst0 n0 Rl s0 t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)) →
      w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))).1 = none →
      MemcpyEffInv dst0 n0 Rl s0 (evaluateHOLFiniteState (decClockHOLFinite t)
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))).2 := by
    intro s0 t w ⟨hc, hm, heff0, ht_d, ht_n, iw, ht_i, _, hdprev⟩ hcond hw hnone
    have hlt := eval_lower_true t n0 iw w ht_n ht_i hcond hw
    rw [BitVec.lt_def] at hlt
    let t0 := decClockHOLFinite t
    have hm0 : t0.memaddrs = ordinaryDomain := hm
    rcases hr : evaluateHOLFiniteState t0 _ with ⟨r_all, post_b⟩
    rw [hr] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hs0 : evaluateHOLFiniteState t0 _ with ⟨r0, m1⟩
    rw [hs0] at hr; cases r0 with | some _ => simp at hr | none =>
    dsimp only at hr
    obtain ⟨he0, hl0, hsb0⟩ := memcpy_storeByte_step (s := t0) (iw := iw) (off := 0) hm0 hfit hin_rl (by omega) hs0
      (fun a ha => by rw [eval_add2_locals t0 _ _ dst0 iw a ht_d ht_i ha, BitVec.toNat_add_of_lt (by omega)]; omega)
    have hdst_sb := hdom_first iw hdprev hsb0
    obtain ⟨he_asg, hi_post, hother_post⟩ := assign_i_add_step (Rl := Rl) (hl0 ▸ ht_i) hr
    have heff_all : ByteRegionEffect s0 post_b Rl :=
      ((heff0.with_locals_clock t.locals (t.clock - 1)).trans he0).trans he_asg
    have hi1_eq : (iw + 1).toNat = iw.toNat + 1 := BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
    refine ⟨heff_all.code.trans (heff0.code.symm.trans hc),
      heff_all.memaddrs.trans (heff0.memaddrs.symm.trans hm),
      heff_all, ?_, ?_, iw + 1, hi_post, by rw [hi1_eq]; omega, fun _ => hdst_sb⟩
    · rw [hother_post _ (by decide), hl0]; exact ht_d
    · rw [hother_post _ (by decide), hl0]; exact ht_n
  rw [evaluateHOLFiniteState_seq_line780]
  set iteProg : ProgHOL 64 := .ite _ _ .skip
  have hite_nrr : noReturnOrRaise iteProg = true := rfl
  rcases hite : evaluateHOLFiniteState s1 iteProg with ⟨r_ite, s2⟩
  cases r_ite with
  | some x =>
    intro hres
    have hnr := evaluate_noReturnOrRaise iteProg hite_nrr s1
    rw [hite] at hnr; exact absurd hres hnr
  | none =>
    dsimp only
    have hinv2 : MemcpyEffInv dst0 n0 Rl s s2 := by
      dsimp only [iteProg] at hite
      rw [evaluateHOLFiniteState_ite] at hite
      split at hite
      · split at hite
        · rw [evaluateHOLFiniteState_skip] at hite
          injection hite with _ hs2; rw [← hs2]; exact hinv1
        · rw [evaluateHOLFiniteState_seq_line780] at hite
          rcases hw1 : evaluateHOLFiniteState s1 _ with ⟨rw1, m1⟩
          rw [hw1] at hite
          cases rw1 with
          | some _ => simp at hite
          | none =>
            dsimp only at hite
            have hm1 := (while_preserve_eff _ _ rfl rfl hstep1 s1.clock s s1 m1 le_rfl hinv1 hw1).1
            exact (while_preserve_eff _ _ rfl rfl hstep2 m1.clock s m1 s2 le_rfl hm1 hite).1
      · simp at hite
    rw [evaluateHOLFiniteState_seq_line780]
    set loop3 : ProgHOL 64 := .while _ _
    have hl3_nrr : noReturnOrRaise loop3 = true := rfl
    rcases hw3 : evaluateHOLFiniteState s2 loop3 with ⟨rw3, s3⟩
    cases rw3 with
    | some _ =>
      intro hres
      have hnr := evaluate_noReturnOrRaise loop3 hl3_nrr s2
      rw [hw3] at hnr; exact absurd hres hnr
    | none =>
      dsimp only
      have hinv3 : MemcpyEffInv dst0 n0 Rl s s3 :=
        (while_preserve_eff _ _ rfl rfl hstep3 s2.clock s s2 s3 le_rfl hinv2 hw3).1
      rw [evaluateHOLFiniteState_seq_line780]
      set loop4 : ProgHOL 64 := .while _ _
      have hl4_nrr : noReturnOrRaise loop4 = true := rfl
      rcases hw4 : evaluateHOLFiniteState s3 loop4 with ⟨rw4, s4⟩
      cases rw4 with
      | some _ =>
        intro hres
        have hnr := evaluate_noReturnOrRaise loop4 hl4_nrr s3
        rw [hw4] at hnr; exact absurd hres hnr
      | none =>
        dsimp only
        obtain ⟨⟨_, _, heff4, _, hn4, iw, hi4, _, hdom4⟩, hcond4⟩ :=
          while_preserve_eff _ _ rfl rfl hstep4 s3.clock s s3 s4 le_rfl hinv3 hw4
        have hge4 := eval_lower_false s4 n0 iw hn4 hi4 hcond4
        have hdst_sb : sourceBase ≤ dst0.toNat := hdom4 (by omega)
        rw [evaluateHOLFiniteState_return]
        have hev0 : @evalHOLExact 64 F _ s4.toExact
            (fun a => Classical.propDecidable (s4.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
            some (.val (.word 0)) := rfl
        have hsz0 : sizeOfShapeWithContextHOL s4.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [hev0]; dsimp only; rw [if_pos hsz0]; dsimp only
        intro _
        exact ⟨rfl, hdst_sb, heff4.with_locals_clock _ _⟩

/-! ## 3. `sk_make` and `is_warm_storage_key` -/

private theorem eval_sk_make_body {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hsk_fit : globN s "sk_buf" + 64 ≤ 2 ^ 64)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1) :
    ∃ skw : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 =
        some (.returned (.val (.word skw))) ∧
      globN s "sk_buf" ≠ 0 ∧
      ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).2
        [(globN s "sk_buf", 64)] := by
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_sk_make,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  -- First call: `call (some (none, none)) "memcpy" [G:"sk_buf", L:"addr", #20]`
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call]
  rcases hargs1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .global (ofString "sk_buf"), .var .local (ofString "addr"),
       .const (BitVec.ofNat 64 20)] with _ | vals1
  · intro h; exact absurd h not_resumes_error
  · dsimp only
    rcases hl1 : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vals1 with _ | ⟨body1, callee1, rs1⟩
    · intro h; exact absurd h not_resumes_error
    · dsimp only
      by_cases hclk1 : s.clock = 0
      · simp [hclk1]; intro h; exact absurd h not_resumes_timeOut
      · rw [if_neg hclk1]
        have hsame1 := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "memcpy")
          _ _ _ _ _ vals1 callee1 (by rw [hcode]; exact lookup_memcpy) hl1
        subst hsame1
        -- Extract `skw` and `addrw` from `hargs1` and `hl1`:
        have hvals1_info : ∃ skw addrw : BitVec 64,
            s.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) ∧
            skw.toNat = globN s "sk_buf" ∧
            callee1.lookup (ofString "dst") = some (.val (.word skw)) ∧
            callee1.lookup (ofString "src") = some (.val (.word addrw)) ∧
            callee1.lookup (ofString "n") = some (.val (.word 20)) := by
          rw [evalListHOLFinite_eq_toExact] at hargs1
          simp only [evalListHOLExact, evalHOLExact] at hargs1
          rcases hsk : s.globals.lookup (ofString "sk_buf") with _ | vsk
          · simp [hsk] at hargs1
          · rcases had : s.locals.lookup (ofString "addr") with _ | vad
            · simp [hsk, had] at hargs1
            · simp only [hsk, had, Option.some.injEq] at hargs1
              subst hargs1
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl1
              split at hl1
              · cases hl1
              · rename_i eb el es hraw
                have heq := Option.some.inj hl1
                rcases Prod.mk.inj heq with ⟨_, hrest⟩
                rcases Prod.mk.inj hrest with ⟨rfl, _⟩
                unfold lookupCodeHOLExact at hraw
                rw [hcode, lookup_memcpy] at hraw
                dsimp only at hraw
                split at hraw
                · rename_i hcond
                  have rawEq := Option.some.inj hraw
                  rcases Prod.mk.inj rawEq with ⟨_, hrest2⟩
                  rcases Prod.mk.inj hrest2 with ⟨hloc, _⟩
                  subst hloc
                  rcases vsk with ⟨⟨skw⟩⟩ | _ | _
                  · rcases vad with ⟨⟨addrw⟩⟩ | _ | _
                    · refine ⟨skw, addrw, rfl, by simp [globN, hsk], ?_, ?_, ?_⟩
                      · have hnd1 : ofString "n" ≠ ofString "dst" := by decide
                        have hnd2 : ofString "src" ≠ ofString "dst" := by decide
                        simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE,
                          hnd1, hnd2, Ne.symm hnd1, Ne.symm hnd2]
                      · have hns : ofString "n" ≠ ofString "src" := by decide
                        simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE,
                          hns, Ne.symm hns]
                      · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE]
                    · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                    · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                  · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                  · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                · cases hraw
        obtain ⟨skw, addrw, hsk_g, hsk_nat, hc1_d, hc1_s, hc1_n⟩ := hvals1_info
        let ent1 := callEntryStateHOLFinite s callee1
        rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite s callee1)
            (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res1, st1⟩
        have hrun1_ent : evaluateHOLFiniteState ent1 (sourceFnBody Guest.Software.guestFn_memcpy) = (res1, st1) := hrun1
        cases res1 with
        | none => intro h; exact absurd h not_resumes_error
        | some r1 =>
          cases r1 with
          | timeOut => intro h; exact absurd h not_resumes_timeOut
          | «break» | «continue» | error => intro h; exact absurd h not_resumes_error
          | finalFfi _ => intro h; rcases h with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
          | exception e1 v1 =>
            intro hres
            have h20 : (20 : BitVec 64).toNat = 20 := rfl
            have hm1 := eval_memcpy_bounded ent1 skw addrw 20 [(skw.toNat, 20)]
              hcode hma hc1_d hc1_s hc1_n (by rw [h20]; omega) (by rw [h20]; omega)
              (by rw [h20, hsk_nat]; omega) (by simp [h20])
              (by rw [hrun1_ent]; rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hnt⟩
                  · simp at hc
                  · injection hc with hc; injection hc with he1 _; subst he1; exact Or.inr ⟨_, _, rfl, hnt⟩)
            rw [hrun1_ent] at hm1; simp at hm1
          | returned rv1 =>
            dsimp only
            have h20 : (20 : BitVec 64).toNat = 20 := rfl
            obtain ⟨hrv1_eq, hsk_sb, heff1_sub⟩ := eval_memcpy_bounded ent1 skw addrw 20 [(skw.toNat, 20)]
              hcode hma hc1_d hc1_s hc1_n (by rw [h20]; omega) (by rw [h20]; omega)
              (by rw [h20, hsk_nat]; omega) (by simp [h20])
              (by rw [hrun1_ent]; exact Or.inl ⟨rv1, rfl⟩)
            rw [hrun1_ent] at hrv1_eq heff1_sub
            dsimp only at hrv1_eq heff1_sub
            injection hrv1_eq with hrv1_eq; injection hrv1_eq with hrv1_eq
            subst hrv1_eq
            have hsh_rs1 : rs1 = .one := by
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl1
              split at hl1
              · cases hl1
              · rename_i eb el es hraw
                have heq := Option.some.inj hl1
                rcases Prod.mk.inj heq with ⟨_, hrest⟩
                rcases Prod.mk.inj hrest with ⟨_, rfl⟩
                unfold lookupCodeHOLExact at hraw
                rw [hcode, lookup_memcpy] at hraw
                dsimp only at hraw
                split at hraw
                · injection hraw with hraw; exact (Prod.mk.inj (Prod.mk.inj hraw).2).2.symm
                · cases hraw
            subst hsh_rs1
            have hsh1 : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            rw [if_pos hsh1]
            dsimp only
            have hsk_nz : globN s "sk_buf" ≠ 0 := by rw [sourceBase_val] at hsk_sb; omega
            have heff1 : ByteRegionEffect s { st1 with locals := s.locals } [(globN s "sk_buf", 64)] := by
              have hmono : ByteRegionEffect ent1 st1 [(globN s "sk_buf", 64)] :=
                heff1_sub.mono (fun i hi => by
                  simp at hi; subst hi
                  exact ⟨(globN s "sk_buf", 64), by simp, by dsimp only; omega, by dsimp only; omega⟩)
              exact (((ByteRegionEffect.refl s _).with_locals_clock _ _).trans hmono).with_locals_clock _ _
            set m1 : PanSemStateFiniteExact 64 F := { st1 with locals := s.locals }
            -- Second call: `call (some (none, none)) "memcpy" [sk_buf + 20, L:"key", #32]`
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call]
            rcases hargs2 : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
                [.op .add [.var .global (ofString "sk_buf"), .const (BitVec.ofNat 64 20)],
                 .var .local (ofString "key"), .const (BitVec.ofNat 64 32)] with _ | vals2
            · intro h; exact absurd h not_resumes_error
            · dsimp only
              rcases hl2 : lookupCodeHOLFinite m1.code.lookup (ofString "memcpy") vals2 with _ | ⟨body2, callee2, rs2⟩
              · intro h; exact absurd h not_resumes_error
              · dsimp only
                by_cases hclk2 : m1.clock = 0
                · simp [hclk2]; intro h; exact absurd h not_resumes_timeOut
                · rw [if_neg hclk2]
                  have hm1_code : m1.code = originalRuntimeCode := heff1.code.trans hcode
                  have hm1_ma : m1.memaddrs = ordinaryDomain := heff1.memaddrs.trans hma
                  have hsame2 := lookupCodeHOLFinite_installed_body m1.code.lookup (ofString "memcpy")
                    _ _ _ _ _ vals2 callee2 (by rw [hm1_code]; exact lookup_memcpy) hl2
                  subst hsame2
                  have hm1_sk : m1.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) := by
                    rw [heff1.globals]; exact hsk_g
                  have hvals2_info : ∃ keyw : BitVec 64,
                      callee2.lookup (ofString "dst") = some (.val (.word (skw + 20))) ∧
                      callee2.lookup (ofString "src") = some (.val (.word keyw)) ∧
                      callee2.lookup (ofString "n") = some (.val (.word 32)) ∧
                      rs2 = .one := by
                    rw [evalListHOLFinite_eq_toExact] at hargs2
                    simp only [evalListHOLExact, evalHOLExact, hm1_sk, valueIsWord, valueWord,
                      wordOpHOL, wordOp, List.all, List.map, Bool.and_self, ↓reduceIte,
                      List.foldr, BitVec.add_zero] at hargs2
                    rcases hky : m1.locals.lookup (ofString "key") with _ | vky
                    · simp [hky] at hargs2
                    · simp only [hky, Option.map, BitVec.add_zero, Option.some.injEq] at hargs2
                      subst hargs2
                      unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl2
                      split at hl2
                      · cases hl2
                      · rename_i eb el es hraw
                        have heq := Option.some.inj hl2
                        rcases Prod.mk.inj heq with ⟨_, hrest⟩
                        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
                        unfold lookupCodeHOLExact at hraw
                        rw [hm1_code, lookup_memcpy] at hraw
                        dsimp only at hraw
                        split at hraw
                        · rename_i hcond
                          have rawEq := Option.some.inj hraw
                          rcases Prod.mk.inj rawEq with ⟨_, hrest2⟩
                          rcases Prod.mk.inj hrest2 with ⟨hloc, rfl⟩
                          subst hloc
                          rcases vky with ⟨⟨keyw⟩⟩ | _ | _
                          · refine ⟨keyw, ?_, ?_, ?_, rfl⟩
                            · have hnd1 : ofString "n" ≠ ofString "dst" := by decide
                              have hnd2 : ofString "src" ≠ ofString "dst" := by decide
                              simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE,
                                hnd1, hnd2, Ne.symm hnd1, Ne.symm hnd2]
                            · have hns : ofString "n" ≠ ofString "src" := by decide
                              simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE,
                                hns, Ne.symm hns]
                            · simp [List.zip, List.foldl, HolFiniteMapExact.lookup_update, FUPDATE]
                          · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                          · simp [shapeOfHOLExact, shapeEqHOL] at hcond
                        · cases hraw
                  obtain ⟨keyw, hc2_d, hc2_s, hc2_n, rfl⟩ := hvals2_info
                  let ent2 := callEntryStateHOLFinite m1 callee2
                  rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite m1 callee2)
                      (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res2, st2⟩
                  have hrun2_ent : evaluateHOLFiniteState ent2 (sourceFnBody Guest.Software.guestFn_memcpy) = (res2, st2) := hrun2
                  have h32 : (32 : BitVec 64).toNat = 32 := rfl
                  have hsk20 : (skw + 20).toNat = globN s "sk_buf" + 20 := by
                    rw [BitVec.toNat_add_of_lt (by change skw.toNat + 20 < 2 ^ 64; omega), hsk_nat]
                    rfl
                  cases res2 with
                  | none => intro h; exact absurd h not_resumes_error
                  | some r2 =>
                    cases r2 with
                    | timeOut => intro h; exact absurd h not_resumes_timeOut
                    | «break» | «continue» | error => intro h; exact absurd h not_resumes_error
                    | finalFfi _ => intro h; rcases h with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
                    | exception e2 v2 =>
                      intro hres
                      have hm2 := eval_memcpy_bounded ent2 (skw + 20) keyw 32 [((skw + 20).toNat, 32)]
                        hm1_code hm1_ma hc2_d hc2_s hc2_n (by rw [h32]; omega) (by rw [h32]; omega)
                        (by rw [h32, hsk20]; omega) (by simp [h32])
                        (by rw [hrun2_ent]; rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hnt⟩
                            · simp at hc
                            · injection hc with hc; injection hc with he2 _; subst he2; exact Or.inr ⟨_, _, rfl, hnt⟩)
                      rw [hrun2_ent] at hm2; simp at hm2
                    | returned rv2 =>
                      dsimp only
                      obtain ⟨hrv2_eq, _, heff2_sub⟩ := eval_memcpy_bounded ent2 (skw + 20) keyw 32
                        [((skw + 20).toNat, 32)] hm1_code hm1_ma hc2_d hc2_s hc2_n
                        (by rw [h32]; omega) (by rw [h32]; omega)
                        (by rw [h32, hsk20]; omega) (by simp [h32])
                        (by rw [hrun2_ent]; exact Or.inl ⟨rv2, rfl⟩)
                      rw [hrun2_ent] at hrv2_eq heff2_sub
                      dsimp only at hrv2_eq heff2_sub
                      injection hrv2_eq with hrv2_eq; injection hrv2_eq with hrv2_eq
                      subst hrv2_eq
                      have hsh2 : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
                        simp [shapeOfHOLExact, shapeEqHOL]
                      rw [if_pos hsh2]
                      dsimp only
                      have heff2 : ByteRegionEffect m1 { st2 with locals := m1.locals } [(globN s "sk_buf", 64)] := by
                        have hmono : ByteRegionEffect ent2 st2 [(globN s "sk_buf", 64)] :=
                          heff2_sub.mono (fun i hi => by
                            simp at hi; subst hi
                            exact ⟨(globN s "sk_buf", 64), by simp, by dsimp only; omega, by dsimp only; omega⟩)
                        exact (((ByteRegionEffect.refl m1 _).with_locals_clock _ _).trans hmono).with_locals_clock _ _
                      set m2 : PanSemStateFiniteExact 64 F := { st2 with locals := m1.locals }
                      have hm2_sk : m2.globals.lookup (ofString "sk_buf") = some (.val (.word skw)) := by
                        rw [heff2.globals]; exact hm1_sk
                      rw [evaluateHOLFiniteState_return]
                      have hev_ret : @evalHOLExact 64 F _ m2.toExact
                          (fun a => Classical.propDecidable (m2.memaddrs a)) (.var .global (ofString "sk_buf")) =
                          some (.val (.word skw)) := by simp [evalHOLExact, hm2_sk]
                      have hsz_ret : sizeOfShapeWithContextHOL m2.structs
                          (shapeOfHOLExact (.val (.word skw) : ValueHOL 64)) ≤ 32 := by
                        simp [shapeOfHOLExact]
                      rw [hev_ret]; dsimp only; rw [if_pos hsz_ret]; dsimp only
                      intro _
                      exact ⟨skw, rfl, hsk_nz, (heff1.trans heff2).with_locals_clock _ _⟩

/-- `is_warm_storage_key` (AST index 525, line 16559): EVM step keeping `EvmInv`, globals, and `evmChain`. -/
theorem «ek_is_warm_storage_key» : EvmKeeps EvmInv [] (ofString "is_warm_storage_key") := by
  refine ⟨_, _, _, lookup_is_warm_storage_key, ?_⟩
  intro F s hcode hInv _ hres
  -- Bound `globN s "sk_buf" + 64 ≤ 2^64` from `EvmInv s` (`FixedTyped s`):
  have hsk_fit : globN s "sk_buf" + 64 ≤ 2 ^ 64 := by
    by_cases hz : globN s "sk_buf" = 0
    · rw [hz]; decide
    · obtain ⟨hAs, S, hW, _⟩ := hInv
      have hmem_fix : (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64) ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩
      rw [if_neg hz] at hmem_fix
      rcases fixedObject_le_2pow64 hAs.2 hW.2.2.1 hmem_fix with h0 | hbnd
      · dsimp only at h0; omega
      · exact hbnd
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_is_warm_storage_key,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "addr"), .var .local (ofString "key")] with _ | vals
  · intro h; exact absurd h not_resumes_error
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") vals with _ | ⟨body_sk, callee_sk, rs_sk⟩
    · intro h; exact absurd h not_resumes_error
    · dsimp only
      by_cases hclk_sk : s.clock = 0
      · simp [hclk_sk]; intro h; exact absurd h not_resumes_timeOut
      · rw [if_neg hclk_sk]
        have hsame_sk := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
          _ _ _ _ _ vals callee_sk (by rw [hcode]; exact lookup_sk_make) hl
        subst hsame_sk
        let ent_sk := callEntryStateHOLFinite s callee_sk
        rcases hrun_sk : evaluateHOLFiniteState (callEntryStateHOLFinite s callee_sk)
            (sourceFnBody Guest.Software.guestFn_sk_make) with
          ⟨res_sk, st_sk⟩
        have hrun_sk_ent : evaluateHOLFiniteState ent_sk (sourceFnBody Guest.Software.guestFn_sk_make) =
            (res_sk, st_sk) := hrun_sk
        have hma : s.memaddrs = ordinaryDomain := hInv.1.1.memaddrs
        cases res_sk with
        | none => intro h; exact absurd h not_resumes_error
        | some r_sk =>
          cases r_sk with
          | timeOut => intro h; exact absurd h not_resumes_timeOut
          | «break» | «continue» | error => intro h; exact absurd h not_resumes_error
          | finalFfi _ => intro h; rcases h with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
          | exception e_sk v_sk =>
            intro hres
            obtain ⟨_, hret_eq, _, _⟩ := eval_sk_make_body ent_sk hcode hma hsk_fit
              (by rw [hrun_sk_ent]; rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hnt⟩
                  · simp at hc
                  · injection hc with hc; injection hc with he _; subst he; exact Or.inr ⟨_, _, rfl, hnt⟩)
            rw [hrun_sk_ent] at hret_eq; simp at hret_eq
          | returned rv_sk =>
            dsimp only
            obtain ⟨skw, hret_eq, hsk_nz_ent, heff_sk0⟩ := eval_sk_make_body ent_sk hcode hma hsk_fit
              (by rw [hrun_sk_ent]; exact Or.inl ⟨rv_sk, rfl⟩)
            have hsk_nz : globN s "sk_buf" ≠ 0 := hsk_nz_ent
            rw [hrun_sk_ent] at hret_eq heff_sk0
            dsimp only at hret_eq heff_sk0
            injection hret_eq with hret_eq; injection hret_eq with hret_eq
            subst hret_eq
            split
            · set s_after_sk := setVarHOLFinite (ofString "k") (.val (.word skw))
                { st_sk with locals := s.locals }
              have heff_sk : ByteRegionEffect s s_after_sk [(globN s "sk_buf", 64)] :=
                (((ByteRegionEffect.refl s _).with_locals_clock _ _).trans heff_sk0).with_locals_clock _ _
              have hs_after_code : s_after_sk.code = originalRuntimeCode := heff_sk.code.trans hcode
              -- Now evaluate `decCall "h" .one "htab_has" [...] (return h)` via `evaluate_readOnlyProg`!
              set cont : ProgHOL 64 :=
                .decCall (ofString "h") .one (ofString "htab_has")
                  [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 176)]),
                   .var .local (ofString "k")]
                  (.return (.var .local (ofString "h")))
              have hcont_ro : readOnlyProg htabHasCallees cont = true := rfl
              have hloc_cont := evaluate_readOnlyProg htabHasCallees htabHasCallees_good
                cont hcont_ro s_after_sk hs_after_code
              rcases hrun_c : evaluateHOLFiniteState s_after_sk cont with ⟨res_c, post_c⟩
              rw [hrun_c] at hloc_cont
              dsimp only at hloc_cont ⊢
              intro _
              let newLocals := HolFiniteMapExact.resVarEq post_c.locals
                (ofString "k", s.locals.lookup (ofString "k"))
              have heff_total : ByteRegionEffect s { post_c with locals := newLocals }
                  [(globN s "sk_buf", 64)] := by
                have hpc : ByteRegionEffect s_after_sk post_c [(globN s "sk_buf", 64)] := by
                  unfold LocFrame at hloc_cont
                  rw [hloc_cont]
                  exact (ByteRegionEffect.refl s_after_sk _).with_locals_clock _ _
                exact (heff_sk.trans hpc).with_locals_clock _ _
              -- Apply `ByteRegionEffect.to_evmStep_nil_with`!
              obtain ⟨hAs, S, hW, hrest⟩ := hInv
              have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
              obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hInvAt.2.2.2.2.2.2.2.2.2.1
              have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
              have hsk_fix : (globN s "sk_buf", 64) ∈ fixedObjects s := by
                have hmem : (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64) ∈ fixedObjects s := by
                  unfold fixedObjects
                  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                  exact List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩
                rwa [if_neg hsk_nz] at hmem
              have hdj_all : ∀ x ∈ [(globN s "sk_buf", 64)],
                  ∀ y ∈ worldTypedIvls s S Nd_at ++ ((evmChain s).map (frameObjects s)).flatten,
                  y.2 = 0 ∨ Disj x y := by
                intro x hx y hy
                simp only [List.mem_singleton] at hx
                subst hx
                rcases List.mem_append.1 hy with hy_wti | hy_fo
                · have hu := untypedGlobalBuf_disj_worldTypedIvls hWT (g := "sk_buf") (sz := 64)
                    (by decide) (by decide) y hy_wti
                  rwa [if_neg hsk_nz] at hu
                · rw [List.mem_flatten] at hy_fo
                  obtain ⟨l, hl, hy_in⟩ := hy_fo
                  obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hl
                  exact Or.inr (Disj.symm ((hInvAt.2.2.2.2.2.2.2.2.1 ec hec y hy_in).2 _ hsk_fix))
              exact ByteRegionEffect.to_evmStep_nil_with hAs hInvAt hTr_at hAT_at hdj_all heff_total
            · intro h; exact absurd h not_resumes_error

end InitECandidate.Solver.Wave8Contracts.M22
