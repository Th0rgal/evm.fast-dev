import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmHtabStep

/-! `StateRestoreEpilogue`: proves `ek_state_restore` and `frame_epilogue_spec`
(0 `sorry`, cycle-free pre-`C00` module). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports (htab_del_spec)
open InitECandidate.Solver.Wave8GuestInv.SoloHtabSet (htab_set_spec_proof three_word_params_of_lookupCode)
open InitECandidate.Solver.Wave8Contracts.M08 (globN_eq_of_lookup ivl_allocated_bound
  typedRecords typedRecord_mem_fixedObjects)
open InitECandidate.Solver.Wave8Contracts.M23 (EvmInvAt EvmStep EvmKeeps Resumes
  GlobalsKept frameWF_bounds)

/-! ## 1. `noCatchableRaise` for `state_restore` -/

def noCatchableRaise (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ b => noCatchableRaise good b
  | .seq a b => noCatchableRaise good a && noCatchableRaise good b
  | .ite _ a b => noCatchableRaise good a && noCatchableRaise good b
  | .while _ b => noCatchableRaise good b
  | .decCall _ _ f _ cont => good f && noCatchableRaise good cont
  | .call (some (_, none)) f _ => good f
  | .raise eid _ => eid == ofString "TrapErr"
  | .skip | .break | .continue | .annot _ _ | .return _
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .shMemStore _ _ _ | .extCall _ _ _ _ _ => true
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
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split <;> simp
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
    rcases tail with _ | ⟨retOpt, hdlOpt⟩
    · simp [shape, noCatchableRaise] at hp
    · rcases hdlOpt with _ | _
      · have hf : good fn = true := by simpa [shape, noCatchableRaise] using hp
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
              cases res with
              | none => simp
              | some r =>
                cases r with
                | returned _ =>
                  dsimp only
                  split
                  · rcases retOpt with _ | ⟨_, _⟩
                    · simp
                    · dsimp only; split <;> simp
                  · simp
                | «break» => simp
                | «continue» => simp
                | exception _ _ => dsimp only; exact ih1
                | timeOut => simp
                | finalFfi _ => simp
                | error => simp
      · simp [shape, noCatchableRaise] at hp
  | _ => simp [shape, noCatchableRaise] at hp
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
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
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

/-! ## 1b. Local/clock invariance of `evmChain`, `evmR`, `EvmInvAt`, and `EvmInv` (pre-`C00`) -/

theorem freeChain_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals globals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, globals := globals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | _ :: rest, _ => by
    simp only [FreeChain]
    exact and_congr Iff.rfl (freeChain_lc s locals globals k nodes rest _)

theorem htabWF_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals globals : HolFiniteMapExact MlS (ValueHOL 64)) (k t : Nat) :
    HtabWF { s with locals := locals, globals := globals, clock := k } t ↔ HtabWF s t := by
  simp only [HtabWF, freeChain_lc]
  exact Iff.rfl

theorem tablesTyped_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    TablesTyped { s with locals := locals, clock := k } S ↔ TablesTyped s S := by
  simp only [TablesTyped, htabWF_lc s locals s.globals k]
  exact Iff.rfl

theorem worldTyped_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    WorldTyped { s with locals := locals, clock := k } S ↔ WorldTyped s S := by
  simp only [WorldTyped, tablesTyped_lc]
  exact Iff.rfl

theorem arenaReady_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem evmChainFrom_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ∀ (fuel e c : Nat),
      evmChainFrom { s with locals := locals, clock := k } fuel e c = evmChainFrom s fuel e c
  | 0, _, _ => rfl
  | fuel + 1, _, _ => by
    simp only [evmChainFrom, evmChainFrom_lc s locals k fuel]
    rfl

theorem evmChain_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmChain { s with locals := locals, clock := k } = evmChain s :=
  evmChainFrom_lc s locals k _ _ _

theorem evmR_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmR { s with locals := locals, clock := k } = evmR s := by
  simp only [evmR, evmChain_lc]
  rfl

theorem evmInvAt_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    EvmInvAt { s with locals := locals, clock := k } S ↔ EvmInvAt s S := by
  simp only [EvmInvAt, FrameWF, MsgOwned, worldTyped_lc, evmChain_lc]
  exact Iff.rfl

theorem evmInv_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    EvmInv { s with locals := locals, clock := k } ↔ EvmInv s := by
  simp only [EvmInv, FrameWF, MsgOwned, worldTyped_lc, arenaReady_lc, evmChain_lc]
  exact Iff.rfl

/-! ## 2. Role non-aliasing of a journaled table `t0` -/

private theorem journaled_table_role_props {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S) {idx : Nat} (hidx : idx < globN s "journal_n") :
    let r := globN s "journal" + 32 * idx
    let t0 := memW s r
    t0 ∈ S ∧
    (∀ (i : Nat) (hi : i + 1 < (evmChain s).length), ¬ DelExclusive s S (evmChain s) i t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    ((globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∨
      (globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) = t0 ∧ journalRole s t0 = "ts+32")) ∧
    (memW s (r + 16) ≠ 0 → journalRole s t0 = "ts+32" →
      (memW s (r + 24), "ts.inner") ∈ journalRoleSlots s) := by
  dsimp only
  set r := globN s "journal" + 32 * idx
  set t0 := memW s r
  obtain ⟨⟨hT, hJ, _, _⟩, _, _, _, _, _, _, _, _, _, _, hRoles, _⟩ := hInv
  have ht0_S : t0 ∈ S := hJ.2.2.2 idx hidx
  have ht0_pos : 0 < t0 := by
    have := ((hT.2.1 t0 ht0_S).1.1 (t0, 88) (by simp [htabFootprint])).1.1
    have hsb : 0 < sourceBase := by decide
    dsimp at this; omega
  have ht0_jr : (t0, journalRole s t0) ∈ journalRoleSlots s := by
    unfold journalRoleSlots
    exact List.mem_flatMap.2 ⟨idx, List.mem_range.2 hidx, List.mem_cons_self⟩
  have hrole_j : journalRole s t0 ∈ ["ts+16", "ts+32", "ts+48", "ts+64", "ts.inner"] := by
    unfold journalRole; split_ifs <;> simp
  have hnot_role : ∀ rname : String,
      rname ∉ ["ts+16", "ts+32", "ts+48", "ts+64", "ts.inner"] →
      (t0, rname) ∉ worldRoleSlots s := by
    intro rname hr_not hmem
    have heq : journalRole s t0 = rname := hRoles.2.2 (t0, journalRole s t0) ht0_jr (t0, rname)
      (List.mem_append_left _ (List.mem_append_left _ hmem)) rfl
    exact hr_not (heq ▸ hrole_j)
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `¬ DelExclusive`: `t0 ∈ worldTableRefs s S` via the journal entry `idx`!
    intro i _ hdel
    apply hdel.1
    unfold worldTableRefs
    exact List.mem_append_right _ (List.mem_map.2 ⟨idx, List.mem_range.2 hidx, rfl⟩)
  · intro hws heq
    apply hnot_role "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot_role "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot_role "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    simp [heq]
  · intro ad had heq
    apply hnot_role "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · by_cases hts : globN s "ts" = 0
    · exact Or.inl (fun h => absurd hts h)
    · by_cases heq32 : memW s (globN s "ts" + 32) = t0
      · right
        refine ⟨hts, heq32, ?_⟩
        have hm32 : (t0, "ts+32") ∈ worldRoleSlots s := by
          unfold worldRoleSlots
          refine List.mem_filter.2 ⟨?_, by simp [Nat.ne_of_gt ht0_pos]⟩
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
          apply List.mem_append_left; apply List.mem_append_right
          unfold recRoles; simp [hts, heq32]
        exact hRoles.2.2 (t0, journalRole s t0) ht0_jr (t0, "ts+32")
          (List.mem_append_left _ (List.mem_append_left _ hm32)) rfl
      · exact Or.inl (fun _ => heq32)
  · intro hp16 hr32
    unfold journalRoleSlots
    refine List.mem_flatMap.2 ⟨idx, List.mem_range.2 hidx, ?_⟩
    exact List.mem_cons_of_mem _ (by simp [r, t0, hp16, hr32])

/-! ## 3. One iteration of `state_restore` preserves `EvmInv` + `evmChain` + `evmR` -/

private abbrev srCond : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "snap")) (.var .global (ofString "journal_n"))

private abbrev srAssign : ProgHOL 64 :=
  .assign .global (ofString "journal_n")
    (.op .sub [.var .global (ofString "journal_n"), .const (BitVec.ofNat 64 1)])

private abbrev srTail : ProgHOL 64 :=
  .dec (ofString "r") .one
    (.op .add [.var .global (ofString "journal"),
      .panop .mul [.var .global (ofString "journal_n"), .const (BitVec.ofNat 64 32)]])
    (.dec (ofString "t") .one (.load .one (.var .local (ofString "r")))
      (.dec (ofString "key") .one
        (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 8)]))
        (.ite (.cmp .notEqual
            (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 16)]))
            (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "t"), .var .local (ofString "key"),
             .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])])
          (.call (some (none, none)) (ofString "htab_del")
            [.var .local (ofString "t"), .var .local (ofString "key")]))))

private theorem srBody_not_cont_break_ret {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.seq srAssign srTail)).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s (.seq srAssign srTail)).1 ≠ some .break ∧
    (∀ u, (evaluateHOLFiniteState s (.seq srAssign srTail)).1 ≠ some (.returned u)) := by
  have hcall_ncb : ∀ (st : PanSemStateFiniteExact 64 F) fn args,
      (evaluateHOLFiniteState st (.call (some (none, none)) fn args)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState st (.call (some (none, none)) fn args)).1 ≠ some .break ∧
      (∀ u, (evaluateHOLFiniteState st (.call (some (none, none)) fn args)).1 ≠ some (.returned u)) := by
    intro st fn args
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) args with _ | _
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite st.code.lookup fn _ with _ | ⟨_, _, _⟩
      · simp
      · dsimp only; split
        · simp
        · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
          rcases res with _ | r
          · simp
          · cases r <;> (dsimp only; try split) <;> simp
  have hdec_ncb : ∀ {st : PanSemStateFiniteExact 64 F} {nm sh init bd},
      (∀ (t : PanSemStateFiniteExact 64 F),
        (evaluateHOLFiniteState t bd).1 ≠ some .continue ∧
        (evaluateHOLFiniteState t bd).1 ≠ some .break ∧
        (∀ u, (evaluateHOLFiniteState t bd).1 ≠ some (.returned u))) →
      (evaluateHOLFiniteState st (.dec nm sh init bd)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState st (.dec nm sh init bd)).1 ≠ some .break ∧
      (∀ u, (evaluateHOLFiniteState st (.dec nm sh init bd)).1 ≠ some (.returned u)) := by
    intro st nm sh init bd hb
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · split
      · exact hb _
      · simp
  have htail_ncb : ∀ (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st srTail).1 ≠ some .continue ∧
      (evaluateHOLFiniteState st srTail).1 ≠ some .break ∧
      (∀ u, (evaluateHOLFiniteState st srTail).1 ≠ some (.returned u)) := by
    intro st; unfold srTail
    refine hdec_ncb fun _ => hdec_ncb fun _ => hdec_ncb fun t => ?_
    rw [evaluateHOLFiniteState_ite]
    split
    · split <;> exact hcall_ncb _ _ _
    · simp
  rw [evaluateHOLFiniteState_seq_line780]
  rcases ha : evaluateHOLFiniteState s srAssign with ⟨ra, ma⟩
  cases ra with
  | none => exact htail_ncb ma
  | some ra' =>
    revert ha; rw [evaluateHOLFiniteState_assign]
    split
    · intro h; injection h with h1 _; injection h1 with h2; subst h2; simp
    · split
      · intro h; injection h with h1 _; cases h1
      · intro h; injection h with h1 _; injection h1 with h2; subst h2; simp

private theorem srBody_step {F : Type}
    {st post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hcode : st.code = originalRuntimeCode)
    (hAs : ArenaReady st) (hInv : EvmInvAt st S)
    (hact : ∃ cw : BitVec 64, @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
      srCond = some (.val (.word cw)) ∧ cw ≠ 0)
    (hrun : evaluateHOLFiniteState st (.seq srAssign srTail) = (none, post)) :
    ArenaReady post ∧
    EvmInvAt post S ∧
    globN st "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept ["heap_ptr", "journal_n"] st post ∧
    evmChain post = evmChain st ∧
    evmR post = evmR st ∧
    (∀ ec ∈ evmChain st, IvlUnhit st post (ec.1, 280) ∧ IvlUnhit st post (ec.2, 104)) := by
  obtain ⟨cw, hcond_ev, hcwnz⟩ := hact
  rw [evalHOLFinite_eq_toExact] at hcond_ev
  obtain ⟨va, jnw, hva, hjb_ev, hcweq⟩ := Wave8M19.evalAt_cmp st .lower _ _ cw hcond_ev
  have hjb : st.globals.lookup (ofString "journal_n") = some (.val (.word jnw)) := by
    simpa [Wave8M19.evalAt, evalHOLExact] using hjb_ev
  have hcmp_t : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower va jnw = true := by
    by_contra hc'; simp [hc'] at hcweq; exact hcwnz hcweq
  have hva_lt_jn : va.toNat < jnw.toNat := by
    simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] using hcmp_t
  have hjn_nat : globN st "journal_n" = jnw.toNat := by simp [globN, hjb]
  have hjn_pos : 0 < jnw.toNat := by omega
  set idx := (jnw - 1).toNat
  have hidx_eq : idx = jnw.toNat - 1 := by
    have hlt := jnw.isLt
    change (jnw - 1).toNat = jnw.toNat - 1
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ jnw.toNat; omega))]
    rfl
  have hidx_lt : idx < globN st "journal_n" := by rw [hjn_nat, hidx_eq]; omega
  obtain ⟨ht0_S, ht0_ndel, ht0_nws32, ht0_nbs32, ht0_nba, ht0_nad, ht0_ts32, ht0_val_jr⟩ :=
    journaled_table_role_props hInv hidx_lt
  -- 1. Execute `srAssign`:
  have hassign : evaluateHOLFiniteState st srAssign =
      (none, setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw - 1))) st) := by
    simp [srAssign, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
      hjb, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
      setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
  rw [evaluateHOLFiniteState_seq_line780, hassign] at hrun
  dsimp only at hrun
  set s1 := setGlobalHOLFinite (ofString "journal_n") (.val (.word (jnw - 1))) st
  have hs1_jn : s1.globals.lookup (ofString "journal_n") = some (.val (.word (jnw - 1))) := by
    simp [s1, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_jn_nat : globN s1 "journal_n" = idx := by simp [globN, hs1_jn, idx]
  have hs1_g_other : ∀ k : MlS, k ≠ ofString "journal_n" → s1.globals.lookup k = st.globals.lookup k :=
    fun k hk => by simp [s1, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk.symm]
  have hs1_gn_other : ∀ g : String, ofString g ≠ ofString "journal_n" → globN s1 g = globN st g :=
    fun g hg => globN_eq_of_lookup (hs1_g_other (ofString g) hg).symm
  -- 2. Unpack the three `dec`s (`r`, `t`, `key`) and the `ite` in `srTail`:
  unfold srTail at hrun
  have dec_none_inv : ∀ {s_in s_out : PanSemStateFiniteExact 64 F} {nm sh init bd},
      evaluateHOLFiniteState s_in (.dec nm sh init bd) = (none, s_out) →
      ∃ val, @evalHOLExact 64 F _ s_in.toExact (fun a => Classical.propDecidable (s_in.memaddrs a)) init = some val ∧
        ∃ mid, evaluateHOLFiniteState (setVarHOLFinite nm val s_in) bd = (none, mid) ∧
          s_out = { mid with locals := HolFiniteMapExact.resVarEq mid.locals (nm, s_in.locals.lookup nm) } := by
    intro s_in s_out nm sh init bd h
    rw [evaluateHOLFiniteState_dec_total] at h; dsimp only at h
    split at h
    · simp at h
    · rename_i val hev
      split at h
      · rcases hb : evaluateHOLFiniteState (setVarHOLFinite nm val s_in) bd with ⟨rb, mid⟩
        rw [hb] at h
        cases rb with
        | none => injection h with _ hso; exact ⟨val, hev, mid, hb, hso.symm⟩
        | some _ => simp at h
      · simp at h
  obtain ⟨vr, hvr_ev, m_r, hrun_r, hp_eq1⟩ := dec_none_inv hrun
  obtain ⟨vt, hvt_ev, m_t, hrun_t, hm_r_eq⟩ := dec_none_inv hrun_r
  obtain ⟨vk, hvk_ev, m_k, hrun_k, hm_t_eq⟩ := dec_none_inv hrun_t
  -- Evaluate `vr` = `.val (.word rw)` with `rw.toNat = globN st "journal" + 32 * idx`:
  have hj_cap_nz : globN st "journal_cap" ≠ 0 := by have := hInv.1.2.1.1; omega
  rcases hInv.1.2.1.2.2.1 with h0 | ⟨hal_j, hw_j⟩
  · exact absurd h0 hj_cap_nz
  have hj_hi := (ivl_allocated_bound hAs.2 hal_j).2
  have hj_word_opt := hAs.2.2.2.2.2.2.2.2.2 "journal" (by decide)
  obtain ⟨jw, hjw_lk⟩ := hj_word_opt
  have hs1_jw : s1.globals.lookup (ofString "journal") = some (.val (.word jw)) := by
    rw [hs1_g_other _ (by decide)]; exact hjw_lk
  have hjw_nat : jw.toNat = globN st "journal" := by unfold GlobalWord at hjw_lk; simp [globN, hjw_lk]
  have hvr_word : vr = .val (.word (jw + (jnw - 1) * 32#64)) := by
    simp only [evalHOLExact, evalListHOLExact, hs1_jw, hs1_jn, List.all, List.map, Option.map,
      Bool.and_self, ↓reduceIte, List.foldr, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] at hvr_ev
    have hz : (jnw - 1) * 32#64 + (0 : BitVec 64) = (jnw - 1) * 32#64 := BitVec.add_zero _
    rw [hz] at hvr_ev
    exact (Option.some.inj hvr_ev).symm
  subst hvr_word
  set rw := jw + (jnw - 1) * 32#64
  have hrw_nat : rw.toNat = globN st "journal" + 32 * idx := by
    have hidx_cap : idx < globN st "journal_cap" := lt_of_lt_of_le hidx_lt hInv.1.2.1.1
    have hmul : ((jnw - 1) * 32#64).toNat = 32 * idx := by
      rw [BitVec.toNat_mul, show (32#64 : BitVec 64).toNat = 32 from rfl]
      change (idx * 32) % 2 ^ 64 = 32 * idx
      rw [Nat.mul_comm, Nat.mod_eq_of_lt (by dsimp at hj_hi; omega)]
    change (jw + (jnw - 1) * 32#64).toNat = globN st "journal" + 32 * idx
    rw [BitVec.toNat_add, hjw_nat, hmul, Nat.mod_eq_of_lt (by dsimp at hj_hi; omega)]
  -- Evaluate `vt` = `.val (.word tw)` with `tw.toNat = memW st (globN st "journal" + 32 * idx)`:
  let s_r := setVarHOLFinite (ofString "r") (.val (.word rw)) s1
  have hvt_word : ∃ tw : BitVec 64, vt = .val (.word tw) ∧
      tw.toNat = memW st (globN st "journal" + 32 * idx) := by
    have hml_word : ∀ dom (dec : DecidablePred dom),
        @memLoadHOLExact 64 _ .one rw dom dec s1.memory s1.structs = some vt →
        vt = .val (st.memory rw) := by
      intro dom dec hml
      unfold memLoadHOLExact at hml
      by_cases hd : dom rw
      · rw [if_pos hd] at hml
        simpa [s1, setGlobalHOLFinite] using (Option.some.inj hml).symm
      · rw [if_neg hd] at hml; cases hml
    simp [s_r, setVarHOLFinite, evalHOLExact, PanSemStateFiniteExact.toExact,
      HolFiniteMapExact.lookup_update, FUPDATE] at hvt_ev
    have hv_eq := hml_word _ _ hvt_ev
    rcases hm : st.memory rw with ⟨tw⟩
    rw [hm] at hv_eq
    refine ⟨tw, hv_eq, ?_⟩
    unfold memW; rw [← hrw_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq, hm]
  obtain ⟨tw, rfl, htw_nat⟩ := hvt_word
  -- Evaluate `vk` = `.val (.word kw)`:
  let s_rt := setVarHOLFinite (ofString "t") (.val (.word tw)) s_r
  have hvk_word : ∃ kw : BitVec 64, vk = .val (.word kw) := by
    have hr_lk : s_rt.locals.lookup (ofString "r") = some (.val (.word rw)) := by
      simp [s_rt, s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "t" ≠ ofString "r" by decide]
    obtain ⟨_, hv⟩ := Wave8M19.Htab.ev_field_load s_rt (ofString "r") rw 8#64 hr_lk vk hvk_ev
    rcases hm8 : s_rt.memory (rw + 8#64) with ⟨kw⟩
    rw [hm8] at hv
    exact ⟨kw, hv⟩
  obtain ⟨kw, rfl⟩ := hvk_word
  let s_rtk := setVarHOLFinite (ofString "key") (.val (.word kw)) s_rt
  have hr_rtk : s_rtk.locals.lookup (ofString "r") = some (.val (.word rw)) := by
    simp [s_rtk, s_rt, s_r, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "key" ≠ ofString "r" by decide, show ofString "t" ≠ ofString "r" by decide]
  have ht_rtk : s_rtk.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_rtk, s_rt, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "key" ≠ ofString "t" by decide]
  have hk_rtk : s_rtk.locals.lookup (ofString "key") = some (.val (.word kw)) := by
    simp [s_rtk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Helper linking `post` and `m_k`: `post` has the exact same memory, globals, be, memaddrs as `m_k`!
  have hpost_mk : post = { m_k with locals := post.locals } := by
    rw [hp_eq1, hm_r_eq, hm_t_eq]
  -- Now split `ite` in `hrun_k`:
  rw [evaluateHOLFiniteState_ite] at hrun_k
  revert hrun_k
  split
  · rename_i cw_p hcw_p
    obtain ⟨vp16, vb0, hvp16, hvb0, hcw_peq⟩ := Wave8M19.evalAt_cmp s_rtk .notEqual _ _ cw_p hcw_p
    obtain ⟨_, hvp16_eq⟩ := Wave8M19.Htab.ev_field_load s_rtk (ofString "r") rw 16#64 hr_rtk (.val (.word vp16)) hvp16
    have hm16 : st.memory (rw + 16#64) = .word vp16 := by
      simpa [s_rtk, s_rt, s_r, s1, setVarHOLFinite, setGlobalHOLFinite, ValueHOL.val.injEq, HolWordLab.word.injEq] using hvp16_eq.symm
    have hvb0_eq : vb0 = 0#64 := by
      simpa [Wave8M19.evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using hvb0.symm
    subst hvb0_eq
    have hr16_nat : memW st (globN st "journal" + 32 * idx + 16) = vp16.toNat := by
      have hidx_cap : idx < globN st "journal_cap" := lt_of_lt_of_le hidx_lt hInv.1.2.1.1
      have hrw16 : BitVec.ofNat 64 (globN st "journal" + 32 * idx + 16) = rw + 16#64 := by
        apply BitVec.eq_of_toNat_eq
        have hlt16 : globN st "journal" + 32 * idx + 16 < 2 ^ 64 := by dsimp at hj_hi; omega
        rw [BitVec.toNat_ofNat, BitVec.toNat_add, hrw_nat, show (16#64 : BitVec 64).toNat = 16 from rfl,
            Nat.mod_eq_of_lt hlt16]
      unfold memW; rw [hrw16, hm16]
    have hA_rtk : ArenaReady s_rtk := by
      refine ⟨guestInv_congr (s := st) (t := s_rtk) rfl rfl rfl rfl hAs.1, ?_⟩
      unfold ArenaOK
      have hhp_eq : globN s_rtk "heap_ptr" = globN st "heap_ptr" := hs1_gn_other "heap_ptr" (by decide)
      have hfm_eq : globN s_rtk "frame_mem_ptr" = globN st "frame_mem_ptr" := hs1_gn_other "frame_mem_ptr" (by decide)
      have hsc_eq : globN s_rtk "scratch_ptr" = globN st "scratch_ptr" := hs1_gn_other "scratch_ptr" (by decide)
      rw [hhp_eq, hfm_eq, hsc_eq]
      exact ⟨hAs.2.1, hAs.2.2.1, hAs.2.2.2.1, hAs.2.2.2.2.1, hAs.2.2.2.2.2.1,
        hAs.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.2.1,
        globalsWord_update (ofString "journal_n") (jnw - 1) rfl hAs.2.2.2.2.2.2.2.2.2⟩
    split
    · -- `cw_p = 0` -> `htab_del(t, key)`!
      intro hcall_del
      change evaluateHOLFiniteState s_rtk _ = (none, m_k) at hcall_del
      obtain ⟨vals, body_d, cal_d, ret_d, rvd, cpost_d, hargs_d, hl_d, hrun_d, hmk_eq⟩ :=
        Wave8M19.Htab.call0_flow s_rtk _ _ (Or.inl (congrArg Prod.fst hcall_del))
      have hcode_rtk : s_rtk.code = originalRuntimeCode := hcode
      have hlk_del := lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_htab_del) rfl
      change originalRuntimeCode.lookup (ofString "htab_del") = _ at hlk_del
      have hbd_eq : body_d = sourceFnBody Guest.Software.guestFn_htab_del := by
        obtain ⟨_, _, hinst⟩ := lookupCode_installed (by rwa [← hcode_rtk] : lookupCodeHOLFinite originalRuntimeCode.lookup _ _ = _)
        rw [hlk_del] at hinst
        exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1.symm
      subst hbd_eq
      obtain ⟨tv, vs1, rfl, htv⟩ := Wave8M19.Htab.evalList_cons_inv s_rtk _ _ hargs_d
      obtain ⟨_, hct⟩ := Wave8M19.Htab.lookupCodeHOLFinite_param_at s_rtk.code.lookup (ofString "htab_del") []
        (ofString "t") .one [(ofString "key", .one)] _ .one
        (by intro p hp; simp at hp; rw [hp]; decide)
        (by rw [hcode_rtk]; exact hlk_del) (vpre := []) (by simp) hl_d
      have hcal_t : cal_d.lookup (ofString "t") = some (.val (.word tw)) := by
        rw [hct]; simp only [evalHOLExact, ht_rtk] at htv; exact htv.symm
      let entry_d := callEntryStateHOLFinite s_rtk cal_d
      have hloc_td : locN entry_d "t" = tw.toNat := by simp [entry_d, callEntryStateHOLFinite, locN, hcal_t]
      have hArg_d : HtabArgWF entry_d := by
        refine ⟨⟨guestInv_congr (s := s_rtk) rfl rfl rfl rfl hA_rtk.1, hA_rtk.2⟩, ?_, ?_⟩
        · rw [hloc_td, htw_nat]
          exact (htabWF_lc st entry_d.locals s1.globals entry_d.clock _).mpr (hInv.1.1.2.1 _ ht0_S).1
        · rw [hloc_td, htw_nat]
          intro i hi
          have hal_st := ((hInv.1.1.2.1 _ ht0_S).2 i hi).1
          unfold Allocated at hal_st ⊢
          have hh1 : globN entry_d "heap_ptr" = globN st "heap_ptr" := hs1_gn_other "heap_ptr" (by decide)
          have hs1' : globN entry_d "scratch_ptr" = globN st "scratch_ptr" := hs1_gn_other "scratch_ptr" (by decide)
          rwa [hh1, hs1']
      have hdel_sub := htab_del_values_sub entry_d hcode_rtk hArg_d rvd (by rw [hrun_d])
      have hcpost_eq : (evaluateHOLFiniteState entry_d (sourceFnBody Guest.Software.guestFn_htab_del)).2 = cpost_d := by
        rw [hrun_d]
      rw [hcpost_eq, hloc_td, htw_nat] at hdel_sub
      obtain ⟨hexit_d, hbe_d, hvals_d⟩ := hdel_sub
      unfold HtabExit at hexit_d; dsimp only at hexit_d
      rw [hloc_td, htw_nat] at hexit_d
      obtain ⟨hAp_d, hwf_d, hhdr0_d, _, hhp_d, hfp_d, hfr_d, hg_d⟩ := hexit_d
      have hhp_entry : globN entry_d "heap_ptr" = globN st "heap_ptr" := hs1_gn_other "heap_ptr" (by decide)
      have hfp_ed_st : htabFootprint entry_d (memW st (globN st "journal" + 32 * idx)) =
          htabFootprint st (memW st (globN st "journal" + 32 * idx)) := rfl
      obtain ⟨hInv_cd, hch_cd, hR_cd, hu_cd⟩ := evmInvAt_of_htab_step
        hAs hInv hAp_d hbe_d hwf_d hhdr0_d
        (by rw [← hhp_entry]; exact hhp_d)
        (by rw [hhp_entry, hfp_ed_st] at hfp_d; exact hfp_d)
        (by rw [hhp_entry, hfp_ed_st] at hfr_d; exact hfr_d)
        (fun k hk => by
          have hk_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
          have hk_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
          exact (hs1_g_other k hk_jn).symm.trans (hg_d k (by simp [hk_hp])))
        (by
          have hjn_cd : globN cpost_d "journal_n" = globN entry_d "journal_n" :=
            globN_eq_of_lookup (hg_d (ofString "journal_n") (by decide))
          have hjn_ed : globN entry_d "journal_n" = idx := hs1_jn_nat
          omega)
        ht0_S ht0_ndel ht0_nws32 ht0_nbs32 ht0_nba ht0_nad
        (by
          rcases ht0_ts32 with h1 | ⟨h1, h2, _⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, h2, fun v hv => Or.inl (hvals_d v hv)⟩)
      have hmk_cd : m_k = { cpost_d with locals := s_rtk.locals } :=
        (Prod.mk.inj (hcall_del.symm.trans hmk_eq)).2
      have hp_cd : post = { cpost_d with locals := post.locals, clock := cpost_d.clock } := by
        rw [hpost_mk, hmk_cd]
      rw [hp_cd]
      exact ⟨(arenaReady_lc cpost_d _ _).2 hAp_d,
             (evmInvAt_lc cpost_d _ _ S).2 hInv_cd,
             by change globN st "heap_ptr" ≤ globN cpost_d "heap_ptr"; rwa [← hhp_entry],
             fun k hk => by
               have hk_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
               have hk_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
               exact (hs1_g_other k hk_jn).symm.trans (hg_d k (by simp [hk_hp])),
             (evmChain_lc cpost_d _ _).trans hch_cd,
             (evmR_lc cpost_d _ _).trans hR_cd,
             hu_cd⟩
    · -- `cw_p ≠ 0` -> `vp16 ≠ 0` -> `htab_set(t, key, load(r + 24))`!
      rename_i hcw_pnz
      intro hcall_set
      change evaluateHOLFiniteState s_rtk _ = (none, m_k) at hcall_set
      have hvp16_nz : vp16.toNat ≠ 0 := by
        intro hz
        have hv0 : vp16 = 0#64 := BitVec.eq_of_toNat_eq hz
        simp [Compiler.Encoders.Asm.wordCmpHOL, hv0] at hcw_peq
        exact hcw_pnz hcw_peq
      have hr16_nz : memW st (globN st "journal" + 32 * idx + 16) ≠ 0 := by rw [hr16_nat]; exact hvp16_nz
      obtain ⟨vals, body_s, cal_s, ret_s, rvs, cpost_s, hargs_s, hl_s, hrun_s, hmk_eq⟩ :=
        Wave8M19.Htab.call0_flow s_rtk _ _ (Or.inl (congrArg Prod.fst hcall_set))
      have hcode_rtk : s_rtk.code = originalRuntimeCode := hcode
      have hlk_set := SoloHtabSet.lookup_htab_set
      have hbs_eq : body_s = sourceFnBody Guest.Software.guestFn_htab_set := by
        obtain ⟨_, _, hinst⟩ := lookupCode_installed (by rwa [← hcode_rtk] : lookupCodeHOLFinite originalRuntimeCode.lookup _ _ = _)
        rw [hlk_set] at hinst
        exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1.symm
      subst hbs_eq
      have hrs_eq : ret_s = .one := by
        have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
          originalRuntimeCode.lookup (ofString "htab_set") vals _ cal_s ret_s (by rwa [← hcode_rtk])
        unfold lookupCodeHOLExact at hx; rw [hlk_set] at hx; dsimp only at hx
        split at hx
        · exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hx)).2).2.symm
        · simp at hx
      subst hrs_eq
      have hl_s' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set") vals =
          some (sourceFnBody Guest.Software.guestFn_htab_set, cal_s, .one) := by rwa [← hcode_rtk]
      obtain ⟨tw', kw', valw, hcal_t, hcal_k, hcal_v⟩ :=
        three_word_params_of_lookupCode (callEntryStateHOLFinite s_rtk cal_s) (ofString "htab_set")
          (ofString "t") (ofString "key") (ofString "value")
          (by decide) (by decide) (by decide) _ _ hlk_set vals hl_s'
      -- Extract `tw' = tw` and `valw.toNat = memW st (globN st "journal" + 32 * idx + 24)` from `hargs_s` + `hl_s'`:
      obtain ⟨v1, vs1, rfl, he1⟩ := Wave8M19.Htab.evalList_cons_inv s_rtk _ _ hargs_s
      have hargs_s2 : evalListHOLFinite s_rtk (h := fun a => Classical.propDecidable (s_rtk.memaddrs a))
          [.var .local (ofString "key"),
           .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])] = some vs1 := by
        rw [evalListHOLFinite_eq_toExact] at hargs_s ⊢
        cases hrest : @evalListHOLExact 64 F _ s_rtk.toExact (fun a => Classical.propDecidable (s_rtk.memaddrs a))
          [.var .local (ofString "key"),
           .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])] with
        | none =>
          have hcons : @evalListHOLExact 64 F _ s_rtk.toExact (fun a => Classical.propDecidable (s_rtk.memaddrs a))
            [.var .local (ofString "t"), .var .local (ofString "key"),
             .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])] = none := by
            unfold evalListHOLExact; rw [he1, hrest]
          rw [hcons] at hargs_s; simp at hargs_s
        | some l =>
          have hcons : @evalListHOLExact 64 F _ s_rtk.toExact (fun a => Classical.propDecidable (s_rtk.memaddrs a))
            [.var .local (ofString "t"), .var .local (ofString "key"),
             .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])] = some (v1 :: l) := by
            unfold evalListHOLExact; rw [he1, hrest]
          rw [hcons] at hargs_s; injection hargs_s with hc; injection hc with _ hl_eq; subst hl_eq; rfl
      obtain ⟨v2, vs2, rfl, he2⟩ := Wave8M19.Htab.evalList_cons_inv s_rtk _ _ hargs_s2
      have hargs_s3 : evalListHOLFinite s_rtk (h := fun a => Classical.propDecidable (s_rtk.memaddrs a))
          [.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])] = some vs2 := by
        rw [evalListHOLFinite_eq_toExact] at hargs_s2 ⊢
        cases hrest : @evalListHOLExact 64 F _ s_rtk.toExact (fun a => Classical.propDecidable (s_rtk.memaddrs a))
          [.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])] with
        | none =>
          have hcons : @evalListHOLExact 64 F _ s_rtk.toExact (fun a => Classical.propDecidable (s_rtk.memaddrs a))
            [.var .local (ofString "key"),
             .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])] = none := by
            unfold evalListHOLExact; rw [he2, hrest]
          rw [hcons] at hargs_s2; simp at hargs_s2
        | some l =>
          have hcons : @evalListHOLExact 64 F _ s_rtk.toExact (fun a => Classical.propDecidable (s_rtk.memaddrs a))
            [.var .local (ofString "key"),
             .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])] = some (v2 :: l) := by
            unfold evalListHOLExact; rw [he2, hrest]
          rw [hcons] at hargs_s2; injection hargs_s2 with hc; injection hc with _ hl_eq; subst hl_eq; rfl
      obtain ⟨v3, vs3, rfl, he3⟩ := Wave8M19.Htab.evalList_cons_inv s_rtk _ _ hargs_s3
      have hvs3 : vs3 = [] := by
        rw [evalListHOLFinite_eq_toExact] at hargs_s3
        simp only [evalListHOLExact, he3, Option.some.injEq, List.cons.injEq] at hargs_s3
        exact hargs_s3.2.symm
      subst hvs3
      have hv1_eq : v1 = .val (.word tw) := by simpa [evalHOLExact, ht_rtk] using he1.symm
      obtain ⟨_, hv3_mem⟩ := Wave8M19.Htab.ev_field_load s_rtk (ofString "r") rw 24#64 hr_rtk v3 he3
      have hex_lk := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
        originalRuntimeCode.lookup (ofString "htab_set") [v1, v2, v3] _ cal_s .one hl_s'
      unfold lookupCodeHOLExact at hex_lk; rw [hlk_set] at hex_lk; dsimp only at hex_lk
      split at hex_lk
      · have hmap_eq := congrArg (fun x => x.2.1) (Option.some.inj hex_lk)
        have hct1 : cal_s.lookup (ofString "t") = some v1 := by
          have := congrFun hmap_eq.symm (ofString "t")
          simpa [List.map, List.zip, List.foldl,
            show ofString "t" ≠ ofString "value" by decide,
            show ofString "t" ≠ ofString "key" by decide] using this
        have hcv3 : cal_s.lookup (ofString "value") = some v3 := by
          have := congrFun hmap_eq.symm (ofString "value")
          simpa [List.map, List.zip, List.foldl] using this
        let entry_s := callEntryStateHOLFinite s_rtk cal_s
        have htw_eq : tw' = tw := by
          change entry_s.locals.lookup (ofString "t") = _ at hcal_t
          dsimp [entry_s, callEntryStateHOLFinite] at hcal_t
          rw [hct1, hv1_eq] at hcal_t
          simpa [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using hcal_t.symm
        subst htw_eq
        have hm24 : st.memory (rw + 24#64) = .word valw := by
          change entry_s.locals.lookup (ofString "value") = _ at hcal_v
          dsimp [entry_s, callEntryStateHOLFinite] at hcal_v
          rw [hcv3] at hcal_v
          have hv3_w : v3 = .val (.word valw) := Option.some.inj hcal_v
          rw [hv3_w] at hv3_mem
          simpa [s_rtk, s_rt, s_r, s1, setVarHOLFinite, setGlobalHOLFinite,
            ValueHOL.val.injEq, HolWordLab.word.injEq] using hv3_mem.symm
        have hr24_nat : memW st (globN st "journal" + 32 * idx + 24) = valw.toNat := by
          have hidx_cap : idx < globN st "journal_cap" := lt_of_lt_of_le hidx_lt hInv.1.2.1.1
          have hrw24 : BitVec.ofNat 64 (globN st "journal" + 32 * idx + 24) = rw + 24#64 := by
            apply BitVec.eq_of_toNat_eq
            have hlt24 : globN st "journal" + 32 * idx + 24 < 2 ^ 64 := by dsimp at hj_hi; omega
            rw [BitVec.toNat_ofNat, BitVec.toNat_add, hrw_nat, show (24#64 : BitVec 64).toNat = 24 from rfl,
                Nat.mod_eq_of_lt hlt24]
          unfold memW; rw [hrw24, hm24]
        have hloc_ts : locN entry_s "t" = tw'.toNat := by
          change (match entry_s.locals.lookup (ofString "t") with | some (.val (.word w)) => w.toNat | _ => 0) = tw'.toNat
          rw [hcal_t]
        have hloc_vs : locN entry_s "value" = valw.toNat := by
          change (match entry_s.locals.lookup (ofString "value") with | some (.val (.word w)) => w.toNat | _ => 0) = valw.toNat
          rw [hcal_v]
        have hArg_s : HtabArgWF entry_s := by
          refine ⟨⟨guestInv_congr (s := s_rtk) rfl rfl rfl rfl hA_rtk.1, hA_rtk.2⟩, ?_, ?_⟩
          · rw [hloc_ts, htw_nat]
            exact (htabWF_lc st entry_s.locals s1.globals entry_s.clock _).mpr (hInv.1.1.2.1 _ ht0_S).1
          · rw [hloc_ts, htw_nat]
            intro i hi
            have hal_st := ((hInv.1.1.2.1 _ ht0_S).2 i hi).1
            unfold Allocated at hal_st ⊢
            have hh1 : globN entry_s "heap_ptr" = globN st "heap_ptr" := hs1_gn_other "heap_ptr" (by decide)
            have hs1' : globN entry_s "scratch_ptr" = globN st "scratch_ptr" := hs1_gn_other "scratch_ptr" (by decide)
            rwa [hh1, hs1']
        have hset_sub := htab_set_values_sub entry_s tw' kw' valw hcal_t hcal_k hcal_v hArg_s rvs (by rw [hrun_s])
        have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
          rw [hrun_s]
        rw [hcpost_eq, hloc_ts, hloc_vs, htw_nat, ← hr24_nat] at hset_sub
        obtain ⟨hexit_s, hbe_s, hvals_s⟩ := hset_sub
        unfold HtabExit at hexit_s; dsimp only at hexit_s
        rw [hloc_ts, htw_nat] at hexit_s
        obtain ⟨hAp_s, hwf_s, hhdr0_s, _, hhp_s, hfp_s, hfr_s, hg_s⟩ := hexit_s
        have hhp_entry : globN entry_s "heap_ptr" = globN st "heap_ptr" := hs1_gn_other "heap_ptr" (by decide)
        have hfp_es_st : htabFootprint entry_s (memW st (globN st "journal" + 32 * idx)) =
            htabFootprint st (memW st (globN st "journal" + 32 * idx)) := rfl
        obtain ⟨hInv_cs, hch_cs, hR_cs, hu_cs⟩ := evmInvAt_of_htab_step
          hAs hInv hAp_s hbe_s hwf_s hhdr0_s
          (by rw [← hhp_entry]; exact hhp_s)
          (by rw [hhp_entry, hfp_es_st] at hfp_s; exact hfp_s)
          (by rw [hhp_entry, hfp_es_st] at hfr_s; exact hfr_s)
          (fun k hk => by
            have hk_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
            have hk_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
            exact (hs1_g_other k hk_jn).symm.trans (hg_s k (by simp [hk_hp])))
          (by
            have hjn_cs : globN cpost_s "journal_n" = globN entry_s "journal_n" :=
              globN_eq_of_lookup (hg_s (ofString "journal_n") (by decide))
            have hjn_es : globN entry_s "journal_n" = idx := hs1_jn_nat
            omega)
          ht0_S ht0_ndel ht0_nws32 ht0_nbs32 ht0_nba ht0_nad
          (by
            rcases ht0_ts32 with h1 | ⟨h1, h2, hr32⟩
            · exact Or.inl h1
            · refine Or.inr ⟨h1, h2, fun v hv => ?_⟩
              rcases hvals_s v hv with rfl | hv_old
              · exact Or.inr (ht0_val_jr hr16_nz hr32)
              · exact Or.inl hv_old)
        have hmk_cs : m_k = { cpost_s with locals := s_rtk.locals } :=
          (Prod.mk.inj (hcall_set.symm.trans hmk_eq)).2
        have hp_cs : post = { cpost_s with locals := post.locals, clock := cpost_s.clock } := by
          rw [hpost_mk, hmk_cs]
        rw [hp_cs]
        exact ⟨(arenaReady_lc cpost_s _ _).2 hAp_s,
               (evmInvAt_lc cpost_s _ _ S).2 hInv_cs,
               by change globN st "heap_ptr" ≤ globN cpost_s "heap_ptr"; rwa [← hhp_entry],
               fun k hk => by
                 have hk_hp : k ≠ ofString "heap_ptr" := fun h => hk (by simp [h])
                 have hk_jn : k ≠ ofString "journal_n" := fun h => hk (by simp [h])
                 exact (hs1_g_other k hk_jn).symm.trans (hg_s k (by simp [hk_hp])),
               (evmChain_lc cpost_s _ _).trans hch_cs,
               (evmR_lc cpost_s _ _).trans hR_cs,
               hu_cs⟩
      · cases hex_lk
  · simp

/-! ## 4. Full `state_restore` loop + `ek_state_restore` + `frame_epilogue_spec` -/

theorem state_restore_body_spec {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (hcode : s0.code = originalRuntimeCode)
    (hInv : EvmInv s0)
    (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_state_restore)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_state_restore)).2
    EvmInv post ∧
    globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
    GlobalsKept ["heap_ptr", "journal_n"] s0 post ∧
    evmChain post = evmChain s0 ∧
    evmR post = evmR s0 ∧
    (∀ ec ∈ evmChain s0, IvlUnhit s0 post (ec.1, 280) ∧ IvlUnhit s0 post (ec.2, 104)) := by
  intro post
  have hbody : sourceFnBody Guest.Software.guestFn_state_restore =
      .seq (.while srCond (.seq srAssign srTail)) (.return (.const 0)) := rfl
  have hwh_noret : ∀ u, (evaluateHOLFiniteState s0 (.while srCond (.seq srAssign srTail))).1 ≠
      some (.returned u) := by
    intro u
    suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
        (evaluateHOLFiniteState st (.while srCond (.seq srAssign srTail))).1 ≠ some (.returned u) from
      this s0.clock s0 rfl
    intro k; induction k using Nat.strongRecOn with
    | ind k ih =>
      intro st hk
      rw [evaluateHOLFiniteState_while_total]
      split
      · split
        · split
          · simp
          · dsimp only; rw [fixClockHOLFinite_evaluateState]
            have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) (.seq srAssign srTail)
            rcases hb : evaluateHOLFiniteState (decClockHOLFinite st) (.seq srAssign srTail) with ⟨r1, mid⟩
            have hlt : mid.clock < k := by rw [hb] at hrem; change mid.clock ≤ st.clock - 1 at hrem; omega
            cases r1 with
            | none => exact ih mid.clock hlt mid rfl
            | some r1' =>
              cases r1' with
              | «continue» => exact ih mid.clock hlt mid rfl
              | «break» => simp
              | returned u' => exact absurd (congrArg Prod.fst hb) ((srBody_not_cont_break_ret _).2.2 u')
              | _ => simp
        · simp
      · simp
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hv
  rcases hwh : evaluateHOLFiniteState s0 (.while srCond (.seq srAssign srTail)) with ⟨rw_res, m1⟩
  rw [hwh] at hv
  cases rw_res with
  | some rw' =>
    cases rw' with
    | returned u => exact absurd (congrArg Prod.fst hwh) (hwh_noret u)
    | _ => simp at hv
  | none =>
    dsimp only at hv
    have hpost_eq : post = emptyLocalsHOLFinite m1 := by
      show (evaluateHOLFiniteState s0 _).2 = emptyLocalsHOLFinite m1
      rw [hbody, evaluateHOLFiniteState_seq_line780, hwh]; dsimp only
      rw [evaluateHOLFiniteState_return]
      have hc0 : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
          (.const 0) = some (.val (.word 0)) := rfl
      have hle32 : sizeOfShapeWithContextHOL m1.structs
          (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by simp [shapeOfHOLExact]
      rw [hc0]; dsimp only; rw [if_pos hle32]
    obtain ⟨hAs0, S, hInvAt0⟩ := hInv
    -- Induction on `st.clock` across the `while` loop:
    have hloop : ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
        st.clock = k → st.code = originalRuntimeCode →
        ArenaReady st → EvmInvAt st S →
        evaluateHOLFiniteState st (.while srCond (.seq srAssign srTail)) = (none, m1) →
        ArenaReady m1 ∧ EvmInvAt m1 S ∧
        globN st "heap_ptr" ≤ globN m1 "heap_ptr" ∧
        GlobalsKept ["heap_ptr", "journal_n"] st m1 ∧
        evmChain m1 = evmChain st ∧
        evmR m1 = evmR st ∧
        (∀ ec ∈ evmChain st, IvlUnhit st m1 (ec.1, 280) ∧ IvlUnhit st m1 (ec.2, 104)) := by
      intro k; induction k using Nat.strongRecOn with
      | ind k ih =>
        intro st hk st_code hAst hIst hst_run
        rw [evaluateHOLFiniteState_while_total] at hst_run
        split at hst_run
        · rename_i cw hcw
          split at hst_run
          · rename_i hcwnz
            split at hst_run
            · simp at hst_run
            · dsimp only at hst_run
              rw [fixClockHOLFinite_evaluateState] at hst_run
              have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) (.seq srAssign srTail)
              have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite st) (.seq srAssign srTail)).1
              rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) (.seq srAssign srTail) with ⟨r1, mid⟩
              rw [bRun] at hst_run hrem hmeta
              have hclk_lt : mid.clock < k := by change mid.clock ≤ st.clock - 1 at hrem; omega
              have hncb := srBody_not_cont_break_ret (decClockHOLFinite st)
              cases r1 with
              | some r1' =>
                cases r1' with
                | «continue» => exact absurd (congrArg Prod.fst bRun) hncb.1
                | «break» => exact absurd (congrArg Prod.fst bRun) hncb.2.1
                | _ => simp at hst_run
              | none =>
                dsimp only at hst_run
                have hact_dec : ∃ cw' : BitVec 64,
                    @evalHOLFinite 64 F _ (decClockHOLFinite st)
                      (fun a => Classical.propDecidable ((decClockHOLFinite st).memaddrs a))
                      srCond = some (.val (.word cw')) ∧ cw' ≠ 0 := by
                  refine ⟨cw, ?_, hcwnz⟩
                  rw [evalHOLFinite_eq_toExact] at hcw ⊢
                  exact hcw
                have hA_dec : ArenaReady (decClockHOLFinite st) :=
                  (arenaReady_lc st st.locals (st.clock - 1)).2 hAst
                have hI_dec : EvmInvAt (decClockHOLFinite st) S :=
                  (evmInvAt_lc st st.locals (st.clock - 1) S).2 hIst
                obtain ⟨hA_mid, hI_mid, hhp_1, hg_1, hch_1, hR_1, hu_1⟩ :=
                  srBody_step (st := decClockHOLFinite st) st_code hA_dec hI_dec hact_dec bRun
                change evmChain mid = evmChain { st with locals := st.locals, clock := st.clock - 1 } at hch_1
                change ∀ ec ∈ evmChain { st with locals := st.locals, clock := st.clock - 1 }, _ at hu_1
                change evmR mid = evmR { st with locals := st.locals, clock := st.clock - 1 } at hR_1
                rw [evmChain_lc st st.locals (st.clock - 1)] at hch_1 hu_1
                rw [evmR_lc st st.locals (st.clock - 1)] at hR_1
                obtain ⟨hA_m1, hI_m1, hhp_2, hg_2, hch_2, hR_2, hu_2⟩ :=
                  ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) hA_mid hI_mid hst_run
                refine ⟨hA_m1, hI_m1, le_trans hhp_1 hhp_2,
                  fun g hg => (hg_1 g hg).trans (hg_2 g hg),
                  hch_2.trans hch_1,
                  hR_2.trans hR_1,
                  fun ec hec => ?_⟩
                have hec_mid : ec ∈ evmChain mid := by rwa [hch_1]
                obtain ⟨hu1a, hu1b⟩ := hu_1 ec hec
                obtain ⟨hu2a, hu2b⟩ := hu_2 ec hec_mid
                exact ⟨fun a ha8 hc => (hu2a a ha8 hc).trans (hu1a a ha8 hc),
                       fun a ha8 hc => (hu2b a ha8 hc).trans (hu1b a ha8 hc)⟩
          · injection hst_run with _ hp; subst hp
            exact ⟨hAst, hIst, le_rfl, fun _ _ => rfl, rfl, rfl,
              fun _ _ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩
        · simp at hst_run
    obtain ⟨hA_m1, hI_m1, hhp_m1, hg_m1, hch_m1, hR_m1, hu_m1⟩ :=
      hloop s0.clock s0 rfl hcode hAs0 hInvAt0 hwh
    rw [hpost_eq]
    exact ⟨⟨(arenaReady_lc m1 _ m1.clock).2 hA_m1, S, (evmInvAt_lc m1 _ m1.clock S).2 hI_m1⟩,
      hhp_m1, hg_m1,
      (evmChain_lc m1 _ m1.clock).trans hch_m1,
      (evmR_lc m1 _ m1.clock).trans hR_m1,
      hu_m1⟩

theorem lookup_state_restore :
    originalRuntimeCode.lookup (ofString "state_restore") =
      some ([(ofString "snap", .one)], sourceFnBody Guest.Software.guestFn_state_restore, .one) :=
  lookup_of_guestAst_getElem 359 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_state_restore) rfl

theorem lookup_frame_epilogue :
    originalRuntimeCode.lookup (ofString "frame_epilogue") =
      some ([], sourceFnBody Guest.Software.guestFn_frame_epilogue, .one) :=
  lookup_of_guestAst_getElem 582 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_epilogue) rfl

/-- `state_restore` (AST line 12903): EVM step: `EvmInv`, `ev`/`cur_cont` and the frame chain kept. -/
theorem ek_state_restore :
    EvmKeeps EvmInv
    ["heap_ptr", "journal_n"] (ofString "state_restore") := by
  refine ⟨[(ofString "snap", .one)], sourceFnBody Guest.Software.guestFn_state_restore, .one,
    lookup_state_restore, ?_⟩
  intro F s hcode hInv _ _ hres
  rcases hres with ⟨v, hv⟩ | ⟨e, v, hex, hne⟩
  · obtain ⟨hInv_p, hhp_p, hg_p, hch_p, _, _⟩ := state_restore_body_spec s hcode hInv v hv
    exact ⟨hInv_p, hhp_p, hg_p, hch_p⟩
  · exfalso
    exact evaluate_noCatchableRaise htabMutCallees htabMutCallees_good
      (sourceFnBody Guest.Software.guestFn_state_restore) rfl s hcode e v hne hex

/-- The epilogue only rolls back the journal (tables in the typed set). -/
theorem frame_epilogue_spec :
    FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_frame_epilogue, .one, lookup_frame_epilogue, ?_⟩
  intro F s hcode ⟨hInv, hDone⟩ _ _ v hv
  have hbody : sourceFnBody Guest.Software.guestFn_frame_epilogue =
      .seq (.ite (.cmp .notEqual
          (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 160)]))
          (.const (BitVec.ofNat 64 0)))
        (.call (some (none, none)) (ofString "state_restore")
          [.load .one (.op .add [.var .global (ofString "cur_cont"), .const (BitVec.ofNat 64 24)])])
        .skip) (.return (.const 0)) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hv
  rcases hite : evaluateHOLFiniteState s
      (.ite (.cmp .notEqual
          (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 160)]))
          (.const (BitVec.ofNat 64 0)))
        (.call (some (none, none)) (ofString "state_restore")
          [.load .one (.op .add [.var .global (ofString "cur_cont"), .const (BitVec.ofNat 64 24)])])
        .skip) with ⟨r_ite, m1⟩
  rw [hite] at hv
  cases r_ite with
  | some ri =>
    cases ri with
    | returned u =>
      exfalso; revert hite; rw [evaluateHOLFiniteState_ite]
      split
      · split
        · rw [evaluateHOLFiniteState_skip]; simp
        · rw [evaluateHOLFiniteState_call]
          rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | _
          · simp
          · dsimp only
            rcases lookupCodeHOLFinite s.code.lookup _ _ with _ | ⟨_, _, _⟩
            · simp
            · dsimp only; split
              · simp
              · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
                rcases res with _ | r
                · simp
                · cases r <;> (dsimp only; try split) <;> simp
      · simp
    | _ => simp at hv
  | none =>
    have hpost_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 =
        emptyLocalsHOLFinite m1 := by
      rw [hbody, evaluateHOLFiniteState_seq_line780, hite]; dsimp only
      rw [evaluateHOLFiniteState_return]
      have hc0 : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
          (.const 0) = some (.val (.word 0)) := rfl
      have hle32 : sizeOfShapeWithContextHOL m1.structs
          (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by simp [shapeOfHOLExact]
      rw [hc0]; dsimp only; rw [if_pos hle32]
    change EvmInv (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ∧
      EvmDone (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ∧
      (evmChain (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2).length =
        (evmChain s).length ∧
      evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_epilogue)).2 ≤ evmR s
    rw [hpost_eq]
    rw [evaluateHOLFiniteState_ite] at hite
    revert hite
    split
    · split
      · rw [evaluateHOLFiniteState_skip]; intro hm1; injection hm1 with _ hm1_eq; subst hm1_eq
        exact ⟨(evmInv_lc s _ s.clock).2 hInv, hDone,
          by rw [emptyLocalsHOLFinite, evmChain_lc s _ s.clock],
          by rw [emptyLocalsHOLFinite, evmR_lc s _ s.clock]⟩
      · intro hm1_call
        obtain ⟨vals, body1, cal1, ret1, rv1, cpost1, _, hl1, hrun1, hm1_eq⟩ :=
          Wave8M19.Htab.call0_flow s _ _ (Or.inl (congrArg Prod.fst hm1_call))
        have hbody1 : body1 = sourceFnBody Guest.Software.guestFn_state_restore := by
          obtain ⟨_, _, hinst⟩ := lookupCode_installed (by rwa [← hcode] : lookupCodeHOLFinite originalRuntimeCode.lookup _ _ = _)
          rw [lookup_state_restore] at hinst
          exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1.symm
        subst hbody1
        obtain ⟨hAs, S, hInvAt⟩ := hInv
        have hInv_ce : EvmInv (callEntryStateHOLFinite s cal1) :=
          (evmInv_lc s cal1 (s.clock - 1)).2 ⟨hAs, S, hInvAt⟩
        obtain ⟨hInv_cp, _, hg_cp, hch_cp, hR_cp, hu_cp⟩ :=
          state_restore_body_spec (callEntryStateHOLFinite s cal1) hcode hInv_ce rv1 (by rw [hrun1])
        have hcpost_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
            (sourceFnBody Guest.Software.guestFn_state_restore)).2 = cpost1 := by rw [hrun1]
        rw [hcpost_eq] at hInv_cp hg_cp hch_cp hR_cp hu_cp
        change evmChain cpost1 = evmChain { s with locals := cal1, clock := s.clock - 1 } at hch_cp
        change ∀ ec ∈ evmChain { s with locals := cal1, clock := s.clock - 1 }, _ at hu_cp
        change evmR cpost1 = evmR { s with locals := cal1, clock := s.clock - 1 } at hR_cp
        rw [evmChain_lc s cal1 (s.clock - 1)] at hch_cp hu_cp
        rw [evmR_lc s cal1 (s.clock - 1)] at hR_cp
        have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
        obtain ⟨hu_ev, hu_cc⟩ := hu_cp _ hhead_mem
        have hev_eq : globN cpost1 "ev" = globN s "ev" :=
          globN_eq_of_lookup (hg_cp (ofString "ev") (by decide))
        have hcc_eq : globN cpost1 "cur_cont" = globN s "cur_cont" :=
          globN_eq_of_lookup (hg_cp (ofString "cur_cont") (by decide))
        have hhead_wf := hInvAt.2.2.2.2.1 (globN s "ev", globN s "cur_cont") hhead_mem
        obtain ⟨he_lt, hc_lt, _, _⟩ := frameWF_bounds hAs.2 hhead_wf
        have hev8 : (globN s "ev") % 8 = 0 := (hhead_wf.1 (globN s "ev", 280) (by simp)).2.1
        have hcc8 : (globN s "cur_cont") % 8 = 0 := (hhead_wf.1 (globN s "cur_cont", 104) (by simp)).2.1
        have hm_cc32 := memW_eq_of_ivlUnhit hu_cc (a := globN s "cur_cont" + 32) (by omega) hc_lt ⟨by omega, by omega⟩
        have hm_ev104 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev" + 104) (by omega) he_lt ⟨by omega, by omega⟩
        have hm_ev56 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev" + 56) (by omega) he_lt ⟨by omega, by omega⟩
        have hm_ev0 := memW_eq_of_ivlUnhit hu_ev (a := globN s "ev") (by omega) he_lt ⟨by omega, by omega⟩
        have hm1_eq' : m1 = { cpost1 with locals := s.locals } :=
          (Prod.mk.inj (hm1_call.symm.trans hm1_eq)).2
        have hm1_cpost : emptyLocalsHOLFinite m1 = { cpost1 with locals := HolFiniteMapExact.empty, clock := cpost1.clock } := by
          rw [hm1_eq']; rfl
        have hDone_post : EvmDone (emptyLocalsHOLFinite m1) := by
          rw [hm1_cpost]
          unfold EvmDone at hDone ⊢
          change memW cpost1 (globN cpost1 "cur_cont" + 32) ≠ 0 ∨
            memW cpost1 (globN cpost1 "ev" + 104) = 0 ∨ memW cpost1 (globN cpost1 "ev" + 56) ≤ memW cpost1 (globN cpost1 "ev")
          rw [hev_eq, hcc_eq, hm_cc32, hm_ev104, hm_ev56, hm_ev0]; exact hDone
        refine ⟨hm1_cpost ▸ (evmInv_lc cpost1 _ cpost1.clock).2 hInv_cp, hDone_post, ?_, ?_⟩
        · rw [hm1_cpost, evmChain_lc cpost1 _ cpost1.clock, hch_cp]
        · rw [hm1_cpost, evmR_lc cpost1 _ cpost1.clock, hR_cp]
    · simp

end InitECandidate.Solver.Wave8GuestInv.R16Shards

