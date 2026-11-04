import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Invariant
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Compose
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_PtxPhase5

/-! Core callee lookups, expression evaluators, and heap/table step lemmas for
Phase 2 of `process_transaction`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.FastPhase5

/-! ## 1. Callee code-table lookups -/

theorem lookup_memcpy_fn :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ((sourceFunctionEntry Guest.Software.guestFn_memcpy).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_keccak256_fn :
    originalRuntimeCode.lookup (ofString "keccak256") =
      some ((sourceFunctionEntry Guest.Software.guestFn_keccak256).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_keccak256) rfl

theorem lookup_htab_set_fn :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ((sourceFunctionEntry Guest.Software.guestFn_htab_set).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

theorem lookup_tx_has_access_list_fn :
    originalRuntimeCode.lookup (ofString "tx_has_access_list") =
      some ((sourceFunctionEntry Guest.Software.guestFn_tx_has_access_list).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 315 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_has_access_list) rfl

theorem lookup_get_account_fn :
    originalRuntimeCode.lookup (ofString "get_account") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_account).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 375 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_account) rfl

theorem lookup_msg_new_fn :
    originalRuntimeCode.lookup (ofString "msg_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_msg_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 465 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_msg_new) rfl

theorem lookup_compute_contract_address_fn :
    originalRuntimeCode.lookup (ofString "compute_contract_address") =
      some ((sourceFunctionEntry Guest.Software.guestFn_compute_contract_address).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 596 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_contract_address) rfl

theorem lookup_tx_is_blob_fn :
    originalRuntimeCode.lookup (ofString "tx_is_blob") =
      some ((sourceFunctionEntry Guest.Software.guestFn_tx_is_blob).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 865 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_is_blob) rfl

theorem lookup_tx_is_setcode_fn :
    originalRuntimeCode.lookup (ofString "tx_is_setcode") =
      some ((sourceFunctionEntry Guest.Software.guestFn_tx_is_setcode).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 866 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_tx_is_setcode) rfl

theorem lookup_te_new_fn :
    originalRuntimeCode.lookup (ofString "te_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_te_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 869 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_te_new) rfl

/-! ## 2. Expression evaluation and flatten helpers -/

theorem evalAt_varL {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (v : ValueHOL 64)
    (h : evalAt s (.var .local (ofString name)) = some v) :
    s.locals.lookup (ofString name) = some v := by
  simpa [evalAt, evalHOLExact] using h

theorem evalAt_varL_word {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (w : BitVec 64)
    (h : evalAt s (.var .local (ofString name)) = some (.val (.word w))) :
    s.locals.lookup (ofString name) = some (.val (.word w)) ∧ locN s name = w.toNat := by
  have hl := evalAt_varL s name (.val (.word w)) h
  exact ⟨hl, by simp [locN, hl]⟩

theorem evalAt_const_word {F : Type} (s : PanSemStateFiniteExact 64 F) (c : BitVec 64) (v : ValueHOL 64)
    (h : evalAt s (.const c) = some v) : v = .val (.word c) := by
  simpa [evalAt, evalHOLExact] using h.symm

theorem evalAt_loadL_word {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local (ofString name), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW s (locN s name + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : s.locals.lookup (ofString name) with _ | u
  · simp [hl] at h
  rcases u with ⟨x⟩ | _ | _
  · cases x with
    | word x =>
      simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
      rcases hm : s.memory (x + k) with ⟨y⟩
      refine ⟨y, by rw [← h.2, hm], ?_⟩
      have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by rw [BitVec.add_def]
      simp only [locN, memW, hl, hadd, hm]
  · simp [hl, valueIsWord] at h
  · simp [hl, valueIsWord] at h

theorem evalAt_add_local_const {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
    (k x : BitVec 64)
    (h : evalAt s (.op .add [.var .local (ofString name), .const k]) = some (.val (.word x))) :
    ∃ b : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word b)) ∧
      locN s name = b.toNat ∧ x = b + k := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : s.locals.lookup (ofString name) with _ | u
  · simp [hl] at h
  rcases u with ⟨b⟩ | _ | _
  · cases b with
    | word b =>
      simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp] at h
      exact ⟨b, rfl, by simp [locN, hl], h.symm⟩
  · simp [hl, valueIsWord] at h
  · simp [hl, valueIsWord] at h

theorem flattenHOL_load_one {F : Type} (s : PanSemStateFiniteExact 64 F) (addr : ExpHOL 64)
    (v : ValueHOL 64) (h : evalAt s (.load .one addr) = some v) :
    (flattenHOL v).length = 1 := by
  simp [evalAt, evalHOLExact] at h
  split at h
  · rename_i a _
    simp [memLoadHOLExact] at h
    rcases h with ⟨_, rfl⟩
    simp [flattenHOL]
  · cases h

theorem flattenHOL_load_quad {F : Type} (s : PanSemStateFiniteExact 64 F) (addr : ExpHOL 64)
    (v : ValueHOL 64)
    (h : evalAt s (.load (.comb [.one, .one, .one, .one]) addr) = some v) :
    (flattenHOL v).length = 4 := by
  simp only [evalAt, evalHOLExact, isWfShapeExactHOL, isWfShapesExactHOL,
    Bool.and_true, ↓reduceIte] at h
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addr
    with _ | va
  · simp [ha] at h
  rcases va with ⟨wa⟩ | _ | _
  · cases wa with
    | word a =>
      simp only [ha, memLoadHOLExact, memLoadsHOLExact] at h
      split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      simp [flattenHOL]
  · simp [ha] at h
  · simp [ha] at h

theorem flattenHOL_val {w : HolWordLab 64} :
    (flattenHOL (.val w)).length = 1 := by simp [flattenHOL]

theorem flattenHOL_quad {a b c d : HolWordLab 64} :
    (flattenHOL (.rStruct [.val a, .val b, .val c, .val d])).length = 4 := by simp [flattenHOL]

/-! ## 3. Exact evaluation of `tx_has_access_list` -/

theorem tx_has_access_list_ret {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode)
    {vs : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL} {v : ValueHOL 64}
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "tx")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "tx_has_access_list") vs =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    (memW s (locN s "tx") = 0 ∧ v = .val (.word 0)) ∨
    (memW s (locN s "tx") ≠ 0 ∧ v = .val (.word 1)) := by
  have hfn : (sourceFunctionEntry Guest.Software.guestFn_tx_has_access_list).2 =
      ([(ofString "tx", .one)],
       .seq
         (.ite
           (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "tx"), .const 0])) (.const 0))
           (.return (.const 1)) .skip)
         (.return (.const 0)),
       .one) := rfl
  have hinstalled : s.code.lookup (ofString "tx_has_access_list") =
      some ([(ofString "tx", .one)],
       .seq
         (.ite
           (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "tx"), .const 0])) (.const 0))
           (.return (.const 1)) .skip)
         (.return (.const 0)),
       .one) := by
    rw [hcode, lookup_tx_has_access_list_fn, hfn]
  obtain ⟨tv, he, htp⟩ := params_one_value s (ofString "tx_has_access_list") (ofString "tx")
    .one _ .one hinstalled (.var .local (ofString "tx")) vs body callee ret ha hl
  have hbody_eq := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "tx_has_access_list")
    _ _ body _ ret vs callee hinstalled hl
  have hsh : shapeOfHOLExact tv = .one := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i raw
      rw [evalListHOLFinite_eq_toExact] at ha
      simp only [evalListHOLExact, he, Option.some.injEq] at ha
      subst ha
      unfold lookupCodeHOLExact at raw
      rw [hinstalled] at raw
      dsimp only at raw
      split at raw
      · rename_i hcond
        have hshapes := hcond.2.2
        simp at hshapes
        exact ((shapeEqHOL_eq_true _ _).1 hshapes).symm
      · cases raw
  obtain ⟨txw, rfl⟩ := shape_one_word hsh
  have htx_loc : locN s "tx" = txw.toNat := (evalAt_varL_word s "tx" txw he).2
  subst hbody_eq
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hb
  set entry := callEntryStateHOLFinite s callee
  rcases hcmp : evalAt entry (.cmp .notEqual
      (.load .one (.op .add [.var .local (ofString "tx"), .const 0])) (.const 0)) with _ | vc
  · unfold evalAt at hcmp; rw [hcmp] at hb; simp at hb
  rcases vc with ⟨wc⟩ | _ | _
  · cases wc with
    | word wc =>
      obtain ⟨lw, rw0, hlw, hrw0, hwc_eq⟩ := evalAt_cmp entry .notEqual _ _ wc hcmp
      obtain ⟨lw', hlw_eq, hlw_mem⟩ := evalAt_loadL_word entry "tx" 0 (.val (.word lw)) hlw
      cases hlw_eq
      have hrw0' : rw0 = 0 := by
        have := evalAt_const_word entry 0 (.val (.word rw0)) hrw0
        cases this; rfl
      subst hrw0'
      have hentry_loc : locN entry "tx" = txw.toNat := by
        simp [entry, callEntryStateHOLFinite, locN, htp]
      have hentry_mem : memW entry (txw.toNat + (0 : BitVec 64).toNat) = memW s (locN s "tx") := by
        simp [entry, callEntryStateHOLFinite, memW, htx_loc]
      rw [hentry_loc, hentry_mem] at hlw_mem
      have hcmp' := hcmp
      unfold evalAt at hcmp'
      rw [hcmp'] at hb
      dsimp only at hb
      by_cases hnz : lw = 0
      · subst hnz
        have hwc0 : wc = 0 := by simp [hwc_eq, wordCmpHOL]
        subst hwc0
        simp [evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return, evalHOLExact,
          shapeOfHOLExact] at hb
        exact Or.inl ⟨hlw_mem.symm, hb.1.symm⟩
      · have hne : wordCmpHOL .notEqual lw 0 = true := by
          simp [wordCmpHOL]; exact hnz
        have hwc1 : wc = 1 := by rw [hwc_eq, hne]; rfl
        subst hwc1
        simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact] at hb
        refine Or.inr ⟨?_, hb.1.symm⟩
        intro hm0
        apply hnz
        apply BitVec.eq_of_toNat_eq
        simpa using hlw_mem.trans hm0
  · unfold evalAt at hcmp; rw [hcmp] at hb; simp at hb
  · unfold evalAt at hcmp; rw [hcmp] at hb; simp at hb

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase2
