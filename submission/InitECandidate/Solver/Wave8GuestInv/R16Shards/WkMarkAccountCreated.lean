import InitECandidate.Solver.Wave8GuestInv.ContractParts.C03
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.Base
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Exec
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M25.nz_htab_set

/-! Proof of `wk_mark_account_created` (`ContractParts/C08.lean:641`) and
reusable non-value-bearing `HtabExit -> WorldStep` bridge (`worldStep_of_htabExit_nonValue`)
under 9-conjunct `ArenaOK`. Imports only prebuilt `C03` and `Deliveries/*`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16WkMarkAccountCreated

open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

section Helpers

abbrev M08IvlUnhit {F : Type} := @InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit F

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem lookup_htab_set :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_set, .one) :=
  lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

theorem lookup_mark_account_created :
    originalRuntimeCode.lookup (ofString "mark_account_created") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_mark_account_created, .one) :=
  lookup_of_guestAst_getElem 393 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mark_account_created) rfl

theorem FunSpec.at_lookup {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (hf : FunSpec Pc Qc fname) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret'))
    (hPc : Pc (callEntryStateHOLFinite state callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1 ≠
      some .timeOut) :
    Qc (callEntryStateHOLFinite state callee)
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').2 := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  have hret := lookupCodeHOLFinite_installed_return state fname params body' body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hret
  exact hspec _ hcode hPc ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩ hnt

theorem evalAt_loadG' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (globN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.globals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [globN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

theorem evalAt_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (globN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.globals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadG' t g k a h⟩

def noCatchableRaise (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ b => noCatchableRaise good b
  | .seq a b => noCatchableRaise good a && noCatchableRaise good b
  | .ite _ a b => noCatchableRaise good a && noCatchableRaise good b
  | .while _ b => noCatchableRaise good b
  | .decCall _ _ f _ cont => good f && noCatchableRaise good cont
  | .call (some (_, none)) f _ => good f
  | .raise eid _ => eid == ofString "TrapErr"
  | .skip | .break | .continue | .annot _ _ | .tick | .return _
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .shMemStore _ _ _ | .shMemLoad _ _ _ _ | .extCall _ _ _ _ _ | .primitive _ _ _ => true
  | _ => false

private theorem lex_ncr {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

theorem evaluate_noCatchableRaise {F : Type} (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise good body = true)
    (p : ProgHOL 64) (hp : noCatchableRaise good p = true)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ∀ eid v, eid ≠ ofString "TrapErr" → (evaluateHOLFiniteState s p).1 ≠ some (.exception eid v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | «break» => rw [evaluateHOLFiniteState_break]; simp
  | «continue» => rw [evaluateHOLFiniteState_continue]; simp
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; simp
  | tick => rw [evaluateHOLFiniteState_tick]; split <;> simp
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | assign _ _ _ =>
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
  | store32 _ _ =>
    rw [evaluateHOLFiniteState_store32]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | shMemStore _ _ _ =>
    rw [evaluateHOLFiniteState_shMemStore_total]
    dsimp only
    split
    · unfold shMemStoreHOLExact
      split <;> split
      all_goals simp [ofExact, toExact]
      all_goals split <;> simp
    · simp
  | shMemLoad _ _ _ _ =>
    classical
    rw [evaluateHOLFiniteState_shMemLoad_source]
    dsimp only
    split
    · split
      · unfold shMemLoadHOLFiniteExact
        repeat' split
        all_goals simp [ofExact, toExact]
      · simp
    · simp
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · simp
    · split
      · simp
      · split <;> simp
  | raise name _ =>
    have htrap : name = ofString "TrapErr" := by
      simpa [shape, noCatchableRaise, beq_iff_eq] using hp
    subst htrap
    intro eid v hne
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · simp [hne.symm]
      · simp
    · simp
  | dec name _ _ body =>
    have hb : noCatchableRaise good body = true := by simpa [shape, noCatchableRaise] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · rename_i val _
      split
      · exact evaluate_noCatchableRaise good hgood body hb (setVarHOLFinite name val s) hcode
      · simp
  | seq a b =>
    have hab : noCatchableRaise good a = true ∧ noCatchableRaise good b = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    have ih1 := evaluate_noCatchableRaise good hgood a hab.1 s hcode
    have rem := evaluateHOLFiniteState_clock_le s a
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s a
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr] at ih1 rem meta'
    dsimp only at ih1 rem meta' ⊢
    cases r1 with
    | none =>
      have mclock : mid.clock ≤ s.clock := rem
      exact evaluate_noCatchableRaise good hgood b hab.2 mid (meta'.1.trans hcode)
    | some _ => exact ih1
  | ite _ yes no =>
    have hy : noCatchableRaise good yes = true ∧ noCatchableRaise good no = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noCatchableRaise good hgood no hy.2 s hcode
      · exact evaluate_noCatchableRaise good hgood yes hy.1 s hcode
    · simp
  | «while» cond body =>
    have hb : noCatchableRaise good body = true := by simpa [shape, noCatchableRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noCatchableRaise good hgood body hb (decClockHOLFinite s) hcode
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem meta'
          dsimp only at ih1 rem meta' ⊢
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have mCode : mid.code = originalRuntimeCode := meta'.1.trans hcode
          cases r1 with
          | none =>
            exact evaluate_noCatchableRaise good hgood (.while cond body) (by simpa [noCatchableRaise] using hb) mid mCode
          | some r =>
            cases r with
            | «continue» =>
              exact evaluate_noCatchableRaise good hgood (.while cond body) (by simpa [noCatchableRaise] using hb) mid mCode
            | «break» => simp
            | _ => exact ih1
      · simp
    · simp
  | decCall name _ fn args cont =>
    have hc : good fn = true ∧ noCatchableRaise good cont = true := by
      simpa [shape, noCatchableRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · simp
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
        have bodyOk := hgood fn hc.1 values body callee rs hl'
        split
        · simp
        · have ih1 := evaluate_noCatchableRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 meta' cl
          dsimp only at ih1 meta' cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have stCode : st.code = originalRuntimeCode := meta'.1.trans hcode
          cases res with
          | none => simp
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := s.locals }
                have smallR : resumed.clock < s.clock := small
                have rCode : resumed.code = originalRuntimeCode := stCode
                exact evaluate_noCatchableRaise good hgood cont hc.2 resumed rCode
              · simp
            | «break» => simp
            | «continue» => simp
            | _ => exact ih1
  | call tail fn args =>
    rcases tail with _ | ⟨dest, hdl⟩
    · simp [shape, noCatchableRaise] at hp
    · cases hdl with
      | some _ => simp [shape, noCatchableRaise] at hp
      | none =>
        have hf : good fn = true := by simpa [shape, noCatchableRaise] using hp
        rw [evaluateHOLFiniteState_call]
        rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
        · simp
        · dsimp only
          rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
          · simp
          · dsimp only
            have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by rwa [← hcode]
            have bodyOk := hgood fn hf values body callee rs hl'
            split
            · simp
            · have ih1 := evaluate_noCatchableRaise good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
              have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
              rw [hrun] at ih1 cl
              dsimp only at ih1 cl ⊢
              change st.clock ≤ s.clock - 1 at cl
              have small : st.clock < s.clock := by omega
              rcases res with _ | (_ | _ | _ | _ | v | ⟨exId, exVal⟩ | _)
              · simp
              · exact ih1
              · exact ih1
              · simp
              · simp
              · dsimp only
                split
                · rcases dest with _ | ⟨_, _⟩
                  · simp
                  · dsimp only; split <;> simp
                · simp
              · dsimp only; exact ih1
              · exact ih1
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply lex_ncr
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

def htabMutCallees (f : MlS) : Bool :=
  f == ofString "trap_with" || f == ofString "alloc" || f == ofString "memcpy" ||
  f == ofString "memeq" || f == ofString "htab_first_diff" || f == ofString "htab_find_leaf" ||
  f == ofString "htab_new_node" || f == ofString "htab_new_leaf" ||
  f == ofString "htab_new_internal" || f == ofString "htab_grow" ||
  f == ofString "htab_set" || f == ofString "htab_del"

theorem htabMutCallees_good :
    ∀ f, htabMutCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise htabMutCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [htabMutCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl
    change originalRuntimeCode.lookup (ofString "trap_with") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
    change originalRuntimeCode.lookup (ofString "alloc") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl
    change originalRuntimeCode.lookup (ofString "memcpy") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memeq) rfl
    change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 130 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_first_diff) rfl
    change originalRuntimeCode.lookup (ofString "htab_first_diff") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 134 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_node) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_node") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 135 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 136 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_new_internal) rfl
    change originalRuntimeCode.lookup (ofString "htab_new_internal") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 137 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_grow) rfl
    change originalRuntimeCode.lookup (ofString "htab_grow") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_set) rfl
    change originalRuntimeCode.lookup (ofString "htab_set") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · have hl := lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_del) rfl
    change originalRuntimeCode.lookup (ofString "htab_del") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

theorem nz_htab_set_r16 :
    FunSpec GuestInv (fun s r _ => Resumes r → locN s "t" ≠ 0) (ofString "htab_set") := by
  rcases InitECandidate.Solver.Wave8Contracts.M25.nz_htab_set with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hg hsh hnt hr
  exact hrun s hc hg hsh hnt hr

theorem callee_param_three {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 p3 : MlS)
    (s1 s2 s3 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3)], body, ret))
    (e1 e2 e3 : ExpHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧ evalAt state e3 = some v3 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧ callee.lookup p3 = some v3 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · simp [he1, he2] at hargs
    · rcases he3 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e3 with _ | v3
      · simp [he1, he2, he3] at hargs
      · simp only [he1, he2, he3, Option.some.injEq] at hargs
        subst hargs
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
        split at hlook
        · cases hlook
        · rename_i exactBody exactLocals exactShape raw
          have heq := Option.some.inj hlook
          rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
          rcases Prod.mk.inj hrest with ⟨rfl, _⟩
          unfold lookupCodeHOLExact at raw
          rw [hl] at raw
          dsimp only at raw
          split at raw
          · rename_i hcond
            have rawEq := Option.some.inj raw
            rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
            rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
            subst hloc
            obtain ⟨hnd, -, -⟩ := hcond
            simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
              not_or, List.not_mem_nil, or_false] at hnd
            refine ⟨v1, v2, v3, he1, he2, he3, ?_, ?_, ?_⟩
            · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2]
            · simp [List.zip, List.foldl, hnd.2.1]
            · simp [List.zip, List.foldl]
          · cases raw

theorem evalAt_loadG_nz {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (g : String) (k : BitVec 64) (hk : k.toNat < sourceBase)
    (v : ValueHOL 64)
    (hev : evalAt s (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW s (globN s g + k.toNat) ∧
      globN s g ≠ 0 := by
  obtain ⟨a, rfl, ha⟩ := evalAt_loadG s g k v hev
  refine ⟨a, rfl, ha, ?_⟩
  intro hg0
  simp [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases hg : s.globals.lookup (ofString g) with _ | gv
  · simp [hg] at hev
  · rcases gv with ⟨⟨gw⟩⟩ | _ | _
    · have hgw0 : gw = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa [globN, hg] using hg0
      subst hgw0
      simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hG.memaddrs] at hev
      have hdom := (InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff k).1 hev.1
      omega
    · simp [hg, valueIsWord] at hev
    · simp [hg, valueIsWord] at hev

theorem disj_fresh_of_zero_or_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with hz | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

theorem m08_ivlUnhit_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    M08IvlUnhit s post i := by
  intro a ha8 h1 h2
  apply hfr a
  · intro j hj hcj
    exact absurd hcj (InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 (hk_al j hj) ⟨h1, h2⟩ (hk j hj))
  · intro hcf
    exact absurd hcf (InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hf_al ⟨h1, h2⟩ hf)

theorem mem_worldRoleSlots_recRole {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : String) (k : Nat) (r : String)
    (_hgnz : globN s g ≠ 0) (htnz : memW s (globN s g + k) ≠ 0)
    (hmem : (memW s (globN s g + k), r) ∈
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]) :
    (memW s (globN s g + k), r) ∈ worldRoleSlots s := by
  unfold worldRoleSlots
  refine List.mem_filter.2 ⟨?_, by simp [htnz]⟩
  apply List.mem_append.2; left; apply List.mem_append.2; left
  apply List.mem_append.2; left; apply List.mem_append.2; left
  exact hmem

theorem slot_ne_of_diff_nonshared_role {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hroles : RolesOK s S (worldRoleSlots s) (journalRoleSlots s))
    {t1 t2 : Nat} {r1 r2 : String}
    (h1 : (t1, r1) ∈ worldRoleSlots s) (h2 : (t2, r2) ∈ worldRoleSlots s)
    (hne_r : r1 ≠ r2) :
    t1 ≠ t2 := by
  intro heq
  subst heq
  obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 h1
  obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 h2
  rcases Nat.lt_trichotomy i1 i2 with hlt | rfl | hgt
  · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i1 i2 hi1 hi2 hlt
    rw [heq1, heq2] at hp
    exact hne_r (hp rfl).1
  · rw [heq1] at heq2
    exact hne_r (Prod.mk.inj heq2).2
  · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i2 i1 hi2 hi1 hgt
    rw [heq1, heq2] at hp
    exact hne_r (hp rfl).1.symm

theorem balObjects_eq_of_unhit_except {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hbal_eq : globN post "bal_accounts" = globN s "bal_accounts")
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i)
    (ht0_not_bal : globN s "bal_accounts" ≠ t0 ∧ ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    balObjects post = balObjects s ∧
    (∀ ad ∈ balRecords post, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      htabValues post (memW post ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s :=
    InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT hbal_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_other _ hm ht0_not_bal.1)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat),
        memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
        memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
        memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16)) ∧
      (∀ l ∈ htabValues s (memW s ad),
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 (ht0_not_bal.2 ad had))
    have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
        memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
      intro l hl_bal
      rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      have hhi_l := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hA hal_l).2
      have hl8 : l % 8 = 0 := hw_l.1
      have hul := hu_bal _ hl_bal (by simp)
      refine ⟨?_, ?_, ?_⟩
      · simpa using InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
      · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
      · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    refine ⟨hoff_eq, hvals_ad, ?_, ?_⟩
    · intro k hk
      by_cases hk0 : memW s (ad + k) = 0
      · simp [hk0, hm0.1, hm0.2.1, hm0.2.2]
      · apply hlst_eq
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hk0]
    · intro l hl
      by_cases hl0 : l = 0
      · subst hl0; simp [hm0.1, hm0.2.1, hm0.2.2]
      · apply hlst_eq
        unfold balObjects
        refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
        apply List.mem_cons_of_mem; apply List.mem_append.2; right
        exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hl0]⟩
  constructor
  · unfold balObjects
    rw [hrecs]
    apply List.flatMap_congr
    intro ad had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp)
    have h24 := hoff_eq 24 (by simp)
    have h32 := hoff_eq 32 (by simp)
    obtain ⟨hk16_0, _, hk16_16⟩ := hklst 16 (by simp)
    obtain ⟨hk24_0, _, hk24_16⟩ := hklst 24 (by simp)
    obtain ⟨hk32_0, _, hk32_16⟩ := hklst 32 (by simp)
    have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
      rw [h0, hvals_ad]
      apply List.flatMap_congr
      intro l hl
      obtain ⟨hl0, _, hl16⟩ := hllst l hl
      simp [lstObjects, hl0, hl16]
    rw [htail, h16, h24, h32]
    simp [lstObjects, hk16_0, hk16_16, hk24_0, hk24_16, hk32_0, hk32_16]
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hvals_ad, hklst, hllst⟩ := had_props ad had
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      obtain ⟨_, hk8, hk16⟩ := hklst k hk
      unfold LstOK; rw [hk8, hk16]; exact had_T.2.2.1 k hk
    · intro l hl
      rw [h0, hvals_ad] at hl
      obtain ⟨_, hl8, hl16⟩ := hllst l hl
      unfold LstOK; rw [hl8, hl16]; exact had_T.2.2.2 l hl

theorem worldRoleSlots_eq_of_unhit_except {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hgs : InitECandidate.Solver.Wave8Contracts.M08.WorldGlobalsSame s post)
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i)
    (ht0_not_nest : (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
                    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
                    globN s "bal_accounts" ≠ t0 ∧ ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72))
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    worldRoleSlots post = worldRoleSlots s := by
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · have hw16 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ws" 40 (by decide) hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
      have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ws" 40 (by decide) hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
      simp only [hws_g] at hw16 hw32 ⊢; simp [h, hw16, hw32]
  have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
    unfold recRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · simp only [hbs_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "bs" 80 (by decide) hbs_g h (hu_bs h) hk.1 hk.2
      simp only [hbs_g] at hw; simp [hw]
  have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
    unfold recRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · simp only [hts_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
      have hw := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ts" 72 (by decide) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw; simp [hw]
  have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "bs" 80 (by decide) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_not_nest.1 h))]
  have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ts" 72 (by decide) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢
      simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (ht0_not_nest.2.1 h))]
  have hrecs_bal := InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_other _ hm ht0_not_nest.2.2.1)
  have hbal_part := (balObjects_eq_of_unhit_except hA hT hF hba_g hu_other
    ⟨ht0_not_nest.2.2.1, ht0_not_nest.2.2.2⟩ hu_bal hm0).2
  unfold worldRoleSlots
  rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
  congr 1; congr 1
  apply List.flatMap_congr
  intro ad had
  rw [← hrecs_bal] at had
  obtain ⟨h0, h8, _⟩ := hbal_part ad had
  rw [h0, h8]

/-- General W2 world step for `HtabExit` on any table `t0` that is in `S` and is NOT one of the
value-bearing tables (`bs+32`, `ts+32`, `bal_accounts`, `ad+0` for `ad ∈ balRecords`, `ws+32`). -/
theorem worldStep_of_htabExit_nonValue {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {gw : List String}
    (hW0 : WorldOK s) (hbe : post.be = s.be)
    (hg_kept : GlobalsKept gw s post)
    (hg_nonHeap : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    {t0 : Nat}
    (ht0_mem : ∀ S, TablesTyped s S → t0 ∈ S ∧
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
      globN s "bal_accounts" ≠ t0 ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0))
    (hAp : ArenaReady post) (hwf_t0 : HtabWF post t0)
    (hhdr0_t0 : hdr post t0 0 = hdr s t0 0)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t0 : ∀ i ∈ htabFootprint post t0, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t0, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s t0) (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    WorldStep (fun _ => []) gw
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra s r post := by
  have hAs := hW0.1
  have hag : AllocatorGrows s post := by
    refine ⟨hhp, ?_⟩
    rw [InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup (hg_nonHeap (ofString "scratch_ptr") (by decide))]
  have hgs : InitECandidate.Solver.Wave8Contracts.M08.WorldGlobalsSame s post :=
    InitECandidate.Solver.Wave8Contracts.M08.worldGlobalsSame_of_kept
      (gw := ["heap_ptr"]) hg_nonHeap (fun _ h => Or.inl (by simpa using h))
  obtain ⟨S0, hWT0_ex⟩ := hW0.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have ht0_S0 : t0 ∈ S0 := (ht0_mem S0 hWT0.1).1
  have hf_al1 : (globN s "heap_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.1
  have ht0_al0 : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 := fun j hj =>
    ((hWT0.1.2.1 t0 ht0_S0).1.1 j hj).2.1
  have hrk : RecordsKept (fun _ => [])
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      s post := by
    intro rec hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
      · refine ⟨80, by simp [typedRecords], ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · refine ⟨72, by simp [typedRecords], ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · refine ⟨88, by simp [typedRecords], ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨sz, htr, hk8, hksz⟩ := hrec_sz
    have hmf := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal).2
      have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
      have hu_rec : M08IvlUnhit s post (globN s rec.1, sz) :=
        m08_ivlUnhit_of_frameOutside hfr ht0_al0 hf_al1
          (fun j hj => InitECandidate.Solver.Wave8Contracts.M08.disj_symm (((hWT0.1.2.1 t0 ht0_S0).2 j hj).2 _ hmf))
          (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal))
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_rec (by omega) hhi ⟨by omega, by omega⟩
  refine ⟨hAp, hhp, hg_kept, hrk, fun S Nd hWT _ => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ht0_S, hno_bs32, hno_ts32, hno_ba, hno_ad, hno_ws32⟩ := ht0_mem S hT
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 := fun j hj =>
    ((hT.2.1 t0 ht0_S).1.1 j hj).2.1
  have hunhit_disj : ∀ i : Ivl, (∀ j ∈ htabFootprint s t0, Disj i j) →
      (i.2 = 0 ∨ Allocated s i) → M08IvlUnhit s post i := fun i hdi hal =>
    m08_ivlUnhit_of_frameOutside hfr ht0_al hf_al1 hdi
      (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp hal)
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i := fun u hu hne i hi =>
    hunhit_disj i (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj)
      (Or.inr ((hT.2.1 u hu).2 i hi).1)
  have hu_fix : ∀ i ∈ fixedObjects s, M08IvlUnhit s post i := fun i hi =>
    hunhit_disj i (fun j hj => InitECandidate.Solver.Wave8Contracts.M08.disj_symm (((hT.2.1 t0 ht0_S).2 j hj).2 i hi))
      (by rcases hF.1 i hi with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal)
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    exact hunhit_disj _ (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj)
      (Or.inr (hTr.1.1 n hn).2.1)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have hmem := hfr c
        (fun j hj hcj => by
          obtain ⟨h1, h2⟩ := hcj
          rw [hc_nat] at h1 h2
          have hj_al := ((hT.2.1 t0 ht0_S).1.1 j hj).2
          have hj1 := hj_al.1; have hj2 := hj_al.2.1
          have hdj := (hTr.2.1 _ hp_ne).1 t0 ht0_S j hj
          rcases hdj with d | d | d | d <;> omega)
        (fun hcf => by
          obtain ⟨h1, h2⟩ := hcf
          dsimp at h1 h2
          rw [hc_nat] at h1 h2
          have hp_hp8 : (globN post "heap_ptr") % 8 = 0 := hAp.2.2.2.2.2.2.1
          have hdj := disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal_p)
          rcases hdj with d | d | d | d <;> (try dsimp at d) <;> omega)
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hbe]
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          obtain ⟨h1, _⟩ := hcj
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := hAs.2.1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm
  have hu_jr : globN s "journal_cap" ≠ 0 → M08IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix
    unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
    simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → M08IvlUnhit s post i := fun i hi _ =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi))))
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i := fun i hi _ =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bo" 88 (by decide) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_eq := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun h h40 => hu_bo_lst (memW s (globN s "bo" + 40), 24) (by simp [blockOutObjects, h, h40]) rfl)
    (fun h h72 => hu_bo_lst (memW s (globN s "bo" + 72), 24) (by simp [blockOutObjects, h, h72]) rfl)
  have hbal_eq := balObjects_eq_of_unhit_except hAs.2 hT hF
    (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) hu_other
    ⟨hno_ba, hno_ad⟩ hu_bal hm0
  have hfix_eq := InitECandidate.Solver.Wave8Contracts.M08.fixedObjects_eq_of_parts hgs hbo_eq.1 hbal_eq.1
  have hF_post := InitECandidate.Solver.Wave8Contracts.M08.fixedTyped_transfer hAs.1 hAp.1 hag hF hfix_eq
  obtain ⟨hjr_eq, hJ_post⟩ := InitECandidate.Solver.Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq := worldRoleSlots_eq_of_unhit_except hAs.2 hT hF hgs hu_other
    ⟨hno_bs32, hno_ts32, hno_ba, hno_ad⟩ hu_ws hu_bs hu_ts hu_bal hm0
  obtain ⟨hNH_post, hne_eq⟩ := InitECandidate.Solver.Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_other u hu hne _ ht_fp)
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
    intro i hi
    rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
    · refine ⟨fun u hu hne j hj => InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin (hT.2.2.1 t0 ht0_S u hu hne.symm k hk j hj),
              fun j hj => InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin (((hT.2.1 t0 ht0_S).2 k hk).2 j hj),
              fun o ho => InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin (InitECandidate.Solver.Wave8Contracts.M08.disj_symm ((hTr.2.1 o ho).1 t0 ht0_S k hk))⟩
    · refine ⟨fun u hu _ j hj => InitECandidate.Solver.Wave8Contracts.M08.disj_symm (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hT.2.1 u hu).2 j hj).1))),
              fun j hj => InitECandidate.Solver.Wave8Contracts.M08.disj_symm (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp
                  (by rcases hF.1 j hj with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal))),
              fun o ho => InitECandidate.Solver.Wave8Contracts.M08.disj_symm (InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_right hfresh
                (disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (by
                  unfold nodeExtents at ho
                  obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
                  rcases hno with rfl | rfl
                  · exact Or.inr (hTr.1.1 n hn).2.1
                  · unfold nodePath; split_ifs with hc
                    · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                      · exact absurd h0 hc.2
                      · exact Or.inr hal
                    · exact Or.inl rfl)))⟩
  have hT_post : TablesTyped post S := by
    have hT0 := hT
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    have ews := hgs.1 ("ws", 40) (by simp [globalBuffers])
    have ebs := hgs.1 ("bs", 80) (by simp [globalBuffers])
    have ets := hgs.1 ("ts", 72) (by simp [globalBuffers])
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, ?_⟩
    · intro u hu
      by_cases heq : u = t0
      · subst heq; rw [hfix_eq]
        exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj_other i hi).2.1⟩⟩
      · rw [(hother_fp u hu heq).2, hfix_eq]
        exact ⟨InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = t0
      · subst hu0; rw [(hother_fp v hv hne.symm).2] at hj
        exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · subst hv0; rw [(hother_fp u hu hu0).2] at hi
          exact InitECandidate.Solver.Wave8Contracts.M08.disj_symm ((ht0_disj_other j hj).1 u hu hu0 i hi)
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem; rw [hgs.2.1 g hg_mem]; exact hgR g hg_mem
    · intro hnz hmem
      rw [ebs] at hnz
      have ew := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [ets] at hnz
      have ew := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_ts32 hnz)) (fun _ hx => hx) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by
        rwa [InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT0 (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hnz
          · exact hu_other _ hm hno_ba)] at had
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      by_cases ha0 : a.1 = t0
      · rw [ha0] at hkl ⊢; exact ⟨ht0_S, hhdr0_t0.trans hkl⟩
      · exact ⟨haS, ((hother_fp a.1 haS ha0).1 0 (by omega)).trans hkl⟩
  have hTr_post : TriesTypedWith post S Nd := by
    have ews := hgs.1 ("ws", 40) (by simp [globalBuffers])
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq, hfix_eq]
      intro o ho
      refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho).2⟩
      by_cases hu0 : u = t0
      · subst hu0; exact InitECandidate.Solver.Wave8Contracts.M08.disj_symm ((ht0_disj_other i hi).2.2 o ho)
      · rw [(hother_fp u hu hu0).2] at hi; exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz
      rw [ews] at hws_nz
      have e24 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) ews hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) ews hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := hno_ws32 hws_nz
      have hu32 := hu_other _ htS hne32
      have hwf32 := (hT.2.1 _ htS).1
      have hvals_eq := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
      obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 htS i hi
  refine ⟨S, Nd, fun _ h => h, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_, trivial⟩
  · -- OwnedGrows
    intro o ho
    unfold worldOwned at ho
    simp only [List.mem_append] at ho
    rcases ho with (ho_tab | ho_fix) | ho_nd
    · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_tab
      by_cases hu0 : u = t0
      · rw [hu0] at hi
        rcases (hfp_t0 o hi).2 with ⟨j, hj, hin⟩ | hfresh
        · refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
          unfold worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, ht0_S, hj⟩))
        · exact Or.inr (Or.inr ⟨hfresh.1, by have := hfresh.2; omega⟩)
      · rw [(hother_fp u hu hu0).2] at hi
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩))
    · rw [hfix_eq] at ho_fix
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_right _ ho_fix)
    · rw [hne_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned
      exact List.mem_append_right _ ho_nd
  · -- FrameOutside
    intro a hkeep hnot_hf
    apply hfr a
    · intro j hj
      apply hkeep j
      apply List.mem_append_left; apply List.mem_append_left
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, ht0_S, hj⟩))
    · intro hcf
      apply hnot_hf
      obtain ⟨h1, h2⟩ := hcf
      unfold heapFree CellHits at *
      dsimp at h1 h2 ⊢
      have := hAp.2.2.1
      omega

end Helpers

/-- `mark_account_created` (AST line 13562): relational world step (`ContractParts/C08.lean:641`). -/
theorem «wk_mark_account_created» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "mark_account_created") := by
  refine ⟨_, _, _, lookup_mark_account_created, ?_⟩
  intro F s hcode hW _ hnt hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_mark_account_created,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hcall : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 56#64]),
         .var .local (ofString "addr"), .const 1#64]) with ⟨r1, mid⟩
  simp only [hcall] at hnt hres ⊢
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "ts"), .const 56#64]),
       .var .local (ofString "addr"), .const 1#64] with _ | values
  · rw [hargs] at hcall; injection hcall with hr1 _; subst hr1
    exact absurd hres not_resumes_error
  · rw [hargs] at hcall; dsimp only at hcall
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hcall; injection hcall with hr1 _; subst hr1
      exact absurd hres not_resumes_error
    · rw [hl] at hcall; dsimp only at hcall
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hcall; injection hcall with hr1 _; subst hr1; simp at hnt
      · rw [if_neg hz] at hcall
        obtain ⟨v1, _, _, he1, _, _, hc_t, _, _⟩ := callee_param_three s (ofString "htab_set")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact lookup_htab_set) _ _ _ values body' callee ret' hargs hl
        obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_nz s hW.1.1 "ts" 56 (by decide) v1 he1
        have hloc_t : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "ts" + 56) := by
          simp [locN, callEntryStateHOLFinite, hc_t, htw_nat]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        rw [hrun] at hcall
        have hbe_post : post.be = s.be := by
          have inv := (M13.evaluateHOLFiniteState_guestInv_be (callEntryStateHOLFinite s callee) body'
            (guestInv_callEntry s callee hW.1.1)).2
          rwa [hrun] at inv
        cases res with
        | none =>
          injection hcall with hr1 _; subst hr1
          exact absurd hres not_resumes_error
        | some cr =>
          cases cr with
          | timeOut =>
            injection hcall with hr1 _; subst hr1; simp at hnt
          | error =>
            injection hcall with hr1 _; subst hr1
            exact absurd hres not_resumes_error
          | «break» =>
            injection hcall with hr1 _; subst hr1
            exact absurd hres not_resumes_error
          | «continue» =>
            injection hcall with hr1 _; subst hr1
            exact absurd hres not_resumes_error
          | finalFfi _ =>
            injection hcall with hr1 _; subst hr1
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h)
          | exception e ev =>
            injection hcall with hr1 _; subst hr1
            exfalso
            rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
            · cases h
            · injection h with h'; injection h' with he hev
              subst he hev
              have hbody_ok : noCatchableRaise htabMutCallees body' = true :=
                htabMutCallees_good (ofString "htab_set") (by decide) values body' callee ret'
                  (by rwa [← hcode])
              have hno := evaluate_noCatchableRaise htabMutCallees htabMutCallees_good
                body' hbody_ok (callEntryStateHOLFinite s callee) hcode e ev hne
              rw [hrun] at hno
              exact hno rfl
          | returned v =>
            dsimp only at hcall
            split at hcall
            · injection hcall with hr1 hmid
              subst hr1
              dsimp only at hres ⊢
              have hret_eval : evaluateHOLFiniteState mid (.return (.const 0#64)) =
                  (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite mid) := by
                simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
              rw [hret_eval]
              dsimp only
              have hnz_at := FunSpec.at_lookup nz_htab_set_r16 s hcode values body' callee ret' hl
                (guestInv_callEntry s callee hW.1.1) (by rw [hrun]; simp)
              rw [hrun] at hnz_at
              have ht0_nz : memW s (globN s "ts" + 56) ≠ 0 := by
                rw [← hloc_t]; exact hnz_at (Or.inl ⟨v, rfl⟩)
              have hArgWF : HtabArgWF (callEntryStateHOLFinite s callee) := by
                obtain ⟨hAs, S, hT, _⟩ := hW
                rcases hT.2.2.2.2.2.1 56 (by simp [tsTableSlots]) hts_nz with h0 | hmS
                · exact absurd h0 ht0_nz
                · refine ⟨localsFree_arenaReady s _ _ hAs, ?_, ?_⟩
                  · rw [hloc_t]
                    exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hT.2.1 _ hmS).1
                  · rw [hloc_t]
                    exact fun i hi => ((hT.2.1 _ hmS).2 i hi).1
              have hexit := FunSpec.at_lookup htab_set_spec s hcode values body' callee ret' hl
                hArgWF (by rw [hrun]; simp)
              rw [hrun] at hexit
              have hex := hexit v rfl
              dsimp only [HtabExit] at hex
              rw [hloc_t] at hex
              change let t := memW s (globN s "ts" + 56)
                let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
                ArenaReady post ∧ HtabWF post t ∧ hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
                globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
                (∀ i ∈ htabFootprint post t, Allocated post i ∧
                  ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
                FrameOutside s post (htabFootprint s t) fresh ∧
                (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
                  s.globals.lookup k = post.globals.lookup k) at hex
              obtain ⟨hAp, hwf_t0, hh0, _, hhp, hfp_t0, hfr_t0, hg_t0⟩ := hex
              set final := emptyLocalsHOLFinite mid
              have hfinal_eq : final = { post with locals := final.locals, clock := post.clock } := by
                dsimp only [final, emptyLocalsHOLFinite]; rw [← hmid]
              have hAp_f : ArenaReady final := by
                rw [hfinal_eq]; exact localsFree_arenaReady post _ _ hAp
              have hwf_f : HtabWF final (memW s (globN s "ts" + 56)) := by
                rw [hfinal_eq]; exact (htabWF_with_locals post _ _ _).2 hwf_t0
              have hbe_f : final.be = s.be := by rw [hfinal_eq]; exact hbe_post
              have hmem_f : final.memory = post.memory := by rw [hfinal_eq]
              have hglob_f : final.globals = post.globals := by rw [hfinal_eq]
              have hhp_f : globN s "heap_ptr" ≤ globN final "heap_ptr" := by
                simpa [globN, hglob_f] using hhp
              have hh0_f : hdr final (memW s (globN s "ts" + 56)) 0 = hdr s (memW s (globN s "ts" + 56)) 0 := by
                simpa [hdr, memW, hmem_f] using hh0
              have hfp_eq_f : htabFootprint final (memW s (globN s "ts" + 56)) = htabFootprint post (memW s (globN s "ts" + 56)) := by
                simp [htabFootprint, hdr, memW, hmem_f]
              have hfp_f : ∀ i ∈ htabFootprint final (memW s (globN s "ts" + 56)), Allocated final i ∧
                  ((∃ j ∈ htabFootprint s (memW s (globN s "ts" + 56)), Inside i j.1 (j.1 + j.2)) ∨
                    Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN final "heap_ptr" - globN s "heap_ptr"))) := by
                intro i hi
                rw [hfp_eq_f] at hi
                obtain ⟨hal_i, hor_i⟩ := hfp_t0 i hi
                exact ⟨by simpa [Allocated, globN, hglob_f] using hal_i,
                       by simpa [globN, hglob_f] using hor_i⟩
              have hfr_f : FrameOutside s final (htabFootprint s (memW s (globN s "ts" + 56)))
                  (globN s "heap_ptr", globN final "heap_ptr" - globN s "heap_ptr") := by
                intro a hk hf
                rw [hmem_f]
                exact hfr_t0 a hk (by simpa [globN, hglob_f] using hf)
              have hg_f : GlobalsKept ["heap_ptr"] s final := by
                intro k hk; rw [hglob_f]; exact hg_t0 k hk
              refine worldStep_of_htabExit_nonValue hW hbe_f hg_f hg_f ?_ hAp_f hwf_f hh0_f hhp_f hfp_f hfr_f
              intro S hT
              have ht0_S : memW s (globN s "ts" + 56) ∈ S := by
                rcases hT.2.2.2.2.2.1 56 (by simp [tsTableSlots]) hts_nz with h0 | hm
                · exact absurd h0 ht0_nz
                · exact hm
              have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
              have ht0_wrs : (memW s (globN s "ts" + 56), "ts+56") ∈ worldRoleSlots s := by
                apply mem_worldRoleSlots_recRole s "ts" 56 "ts+56" hts_nz ht0_nz
                apply List.mem_append.2; right
                unfold recRoles; simp [hts_nz]
              refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_⟩
              · intro hbs h32
                have h32_nz : memW s (globN s "bs" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
                have hm : (memW s (globN s "bs" + 32), "bs+32") ∈ worldRoleSlots s := by
                  apply mem_worldRoleSlots_recRole s "bs" 32 "bs+32" hbs h32_nz
                  apply List.mem_append.2; left; apply List.mem_append.2; right
                  unfold recRoles; simp [hbs]
                exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h32
              · intro hts h32
                have h32_nz : memW s (globN s "ts" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
                have hm : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
                  apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts h32_nz
                  apply List.mem_append.2; right
                  unfold recRoles; simp [hts]
                exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h32
              · intro hba
                have hba_nz : globN s "bal_accounts" ≠ 0 := by rw [hba]; exact ht0_nz
                have hm : (globN s "bal_accounts", "bal_accounts") ∈ worldRoleSlots s := by
                  unfold worldRoleSlots
                  refine List.mem_filter.2 ⟨?_, by simp [hba_nz]⟩
                  apply List.mem_append.2; left; apply List.mem_append.2; left
                  apply List.mem_append.2; left; apply List.mem_append.2; right; simp
                exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) hba
              · intro ad had had0
                have had0_nz : memW s ad ≠ 0 := by rw [had0]; exact ht0_nz
                have hm : (memW s ad, "bal.stor") ∈ worldRoleSlots s := by
                  unfold worldRoleSlots
                  refine List.mem_filter.2 ⟨?_, by simp [had0_nz]⟩
                  apply List.mem_append.2; right
                  exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
                exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) had0
              · intro hws h32
                have h32_nz : memW s (globN s "ws" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
                have hm : (memW s (globN s "ws" + 32), "ws+32") ∈ worldRoleSlots s := by
                  apply mem_worldRoleSlots_recRole s "ws" 32 "ws+32" hws h32_nz
                  apply List.mem_append.2; left; apply List.mem_append.2; left
                  unfold recRoles; simp [hws]
                exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs (by decide) h32
            · injection hcall with hr1 _; subst hr1
              exact absurd hres not_resumes_error

end InitECandidate.Solver.Wave8GuestInv.R16WkMarkAccountCreated
