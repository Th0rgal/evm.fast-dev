import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.SetLstNew

/-! Zero-sorry proofs of `wk_add_code_change`, `wk_add_nonce_change`,
`wk_add_balance_change`, and `wk_add_storage_write` (`ContractParts/C08.lean`). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M08
open InitECandidate.Solver.Wave8GuestInv.M11

/-! ## 1. AST lookups and `noCatchableRaise` closure -/

private theorem lookup_lst_push_add :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        sourceFnBody Guest.Software.guestFn_lst_push, .one) :=
  lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

private theorem lookup_bal_ensure_account_add :
    originalRuntimeCode.lookup (ofString "bal_ensure_account") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_bal_ensure_account, .one) :=
  lookup_of_guestAst_getElem 412 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_ensure_account) rfl

private theorem lookup_lst_upsert_idx_add :
    originalRuntimeCode.lookup (ofString "lst_upsert_idx") =
      some ([(ofString "l", .one), (ofString "esz", .one), (ofString "idx", .one)],
        sourceFnBody Guest.Software.guestFn_lst_upsert_idx, .one) :=
  lookup_of_guestAst_getElem 413 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_upsert_idx) rfl

private theorem lookup_add_storage_write_add :
    originalRuntimeCode.lookup (ofString "add_storage_write") =
      some ([(ofString "addr", .one), (ofString "slot", .one), (ofString "idx", .one),
             (ofString "new_value", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_add_storage_write, .one) :=
  lookup_of_guestAst_getElem 414 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_storage_write) rfl

private theorem lookup_add_balance_change_add :
    originalRuntimeCode.lookup (ofString "add_balance_change") =
      some ([(ofString "addr", .one), (ofString "idx", .one),
             (ofString "post_balance", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_add_balance_change, .one) :=
  lookup_of_guestAst_getElem 416 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_balance_change) rfl

private theorem lookup_add_nonce_change_add :
    originalRuntimeCode.lookup (ofString "add_nonce_change") =
      some ([(ofString "addr", .one), (ofString "idx", .one), (ofString "new_nonce", .one)],
        sourceFnBody Guest.Software.guestFn_add_nonce_change, .one) :=
  lookup_of_guestAst_getElem 417 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_nonce_change) rfl

private theorem lookup_add_code_change_add :
    originalRuntimeCode.lookup (ofString "add_code_change") =
      some ([(ofString "addr", .one), (ofString "idx", .one),
             (ofString "code", .one), (ofString "code_len", .one)],
        sourceFnBody Guest.Software.guestFn_add_code_change, .one) :=
  lookup_of_guestAst_getElem 418 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_code_change) rfl

private def balAddCallees (f : MlS) : Bool :=
  htabSetCallees f ||
  f == ofString "htab_get" ||
  f == ofString "htab_new" ||
  f == ofString "lst_new" ||
  f == ofString "lst_push" ||
  f == ofString "bal_ensure_account" ||
  f == ofString "lst_upsert_idx"

private theorem noCatchableRaise_mono {g1 g2 : MlS → Bool}
    (hsub : ∀ f, g1 f = true → g2 f = true) :
    (p : ProgHOL 64) → noCatchableRaise g1 p = true → noCatchableRaise g2 p = true
  | .dec _ _ _ b, h => noCatchableRaise_mono hsub b h
  | .seq a b, h => by
    simp only [noCatchableRaise, Bool.and_eq_true] at h ⊢
    exact ⟨noCatchableRaise_mono hsub a h.1, noCatchableRaise_mono hsub b h.2⟩
  | .ite _ a b, h => by
    simp only [noCatchableRaise, Bool.and_eq_true] at h ⊢
    exact ⟨noCatchableRaise_mono hsub a h.1, noCatchableRaise_mono hsub b h.2⟩
  | .while _ b, h => noCatchableRaise_mono hsub b h
  | .decCall _ _ f _ cont, h => by
    simp only [noCatchableRaise, Bool.and_eq_true] at h ⊢
    exact ⟨hsub f h.1, noCatchableRaise_mono hsub cont h.2⟩
  | .call (some (_, none)) f _, h => hsub f h
  | .call none _ _, h => by simp [noCatchableRaise] at h
  | .call (some (_, some _)) _ _, h => by simp [noCatchableRaise] at h
  | .raise _ _, h => h
  | .skip, _ | .break, _ | .continue, _ | .annot _ _, _ | .return _, _
  | .assign _ _ _, _ | .store _ _, _ | .storeByte _ _, _ | .store32 _ _, _
  | .shMemStore _ _ _, _ | .extCall _ _ _ _ _, _ => rfl
  | .shMemLoad _ _ _ _, h => by simp [noCatchableRaise] at h

private theorem balAddCallees_noCatchableRaise :
    ∀ f, balAddCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise balAddCallees body = true := by
  have hsub_set : ∀ g, htabSetCallees g = true → balAddCallees g = true := by
    intro g hg; simp [balAddCallees, hg]
  intro f hf values body callee rs hfound
  simp only [balAddCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (((((hf_set | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · exact noCatchableRaise_mono hsub_set body
      (htabSetCallees_noCatchableRaise f hf_set values body callee rs hfound)
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_htab_get] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [R10Shards.SoloHtabNew.lookup_htab_new] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_lst_new_wk] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_lst_push_add] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_bal_ensure_account_add] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_lst_upsert_idx_add] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

private theorem lst_push_no_catchable_exn_add {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise balAddCallees balAddCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_lst_push) rfl s hcode e v hne

private theorem bal_ensure_account_no_catchable_exn_add {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bal_ensure_account)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise balAddCallees balAddCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_bal_ensure_account) rfl s hcode e v hne

private theorem lst_upsert_idx_no_catchable_exn_add {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise balAddCallees balAddCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) rfl s hcode e v hne

/-! ## 2. `WorldStep` composition helpers for `["heap_ptr"]` -/

private theorem worldStep_hp_trans {F : Type}
    {s m post : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hAs : ArenaOK s)
    (h1 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r1 m)
    (h2 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra m r2 post) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r2 post := by
  have hsp_eq : globN m "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (h1.2.2.1 (ofString "scratch_ptr") (by decide))
  exact worldStep_trans_bufs hAs h1 h2 (by rw [hsp_eq]) rfl
    (fun _ _ _ _ hx => False.elim (List.not_mem_nil hx))
    (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun _ _ _ _ _ _ => trivial)

private theorem worldStep_nil_to_hp {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStep (fun _ => []) [] stdKeep NoExtra s r post) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r post :=
  worldStep_weaken (fun _ hg => False.elim (List.not_mem_nil hg))
    (fun _ _ _ hD => hD) (fun _ _ _ _ _ hno => hno)
    (fun _ _ _ _ hi => False.elim (List.not_mem_nil hi)) (fun _ _ _ => trivial) h

private theorem worldOK_of_step {F : Type}
    {s m : PanSemStateFiniteExact 64 F} {gw : List String} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (hstep : WorldStep (fun _ => []) gw stdKeep NoExtra s r m) :
    WorldOK m := by
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨Sm, Ndm, _, hWTm, _, _, _⟩ :=
    hstep.2.2.2.2 S0 Nd0 hWT0 (fun _ hx => False.elim (List.not_mem_nil hx))
  exact ⟨hstep.1, ⟨Sm, (worldTyped_iff_with m Sm).2 ⟨Ndm, hWTm⟩⟩⟩

/-! ## 3. Multi-word `panMemStoresHOL` `ByteRegionEffect` and `lst_push` on `BalListSlice` -/

private theorem panMemStoresHOL_frame_add {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ a : BitVec 64, (∀ k, k < ws.length → a ≠ x + BitVec.ofNat 64 (8 * k)) → mem' a = mem a
  | [], _, mem, mem', hst, a, _ => by
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    rw [← hst]
  | w :: ws, x, mem, mem', hst, a, hne => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    have hbw : (panBytesInWord 64 : BitVec 64) = BitVec.ofNat 64 8 := by decide
    have ih := panMemStoresHOL_frame_add ws (x + panBytesInWord 64)
      (fun current => if current = x then w else mem current) mem' hst a (fun k hk => by
        have hk1 : k + 1 < (w :: ws).length := by simp; omega
        have hne1 := hne (k + 1) hk1
        rw [hbw]
        intro heq
        apply hne1
        rw [heq, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega)
    rw [ih]
    exact if_neg (by simpa using hne 0 (by simp))

private theorem panMemStoresHOL_dom_all_add {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ k, k < ws.length → dom (x + BitVec.ofNat 64 (8 * k))
  | [], _, _, _, _, k, hk => by simp at hk
  | w :: ws, x, mem, mem', hst, k, hk => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    cases k with
    | zero => simpa using hdom
    | succ k' =>
      have hbw : (panBytesInWord 64 : BitVec 64) = BitVec.ofNat 64 8 := by decide
      have hk' : k' < ws.length := by simp at hk; omega
      have ih := panMemStoresHOL_dom_all_add ws (x + panBytesInWord 64)
        (fun current => if current = x then w else mem current) mem' hst k' hk'
      rw [hbw, BitVec.add_assoc] at ih
      have heq : (8#64 + BitVec.ofNat 64 (8 * k') : BitVec 64) = BitVec.ofNat 64 (8 * (k' + 1)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rwa [heq] at ih

private theorem bre_of_store_multi {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl} {nw : Nat}
    (hma_ord : s.memaddrs = ordinaryDomain)
    (hnw_pos : 1 ≤ nw)
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post))
    (hval_len : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      (flattenHOL v).length = nw)
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs addr →
      addr.toNat + 8 * nw ≤ 2 ^ 64 ∧
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 * nw ≤ i.1 + i.2) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_store] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with
    _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with
        _ | v
      · simp
      · have hlen := hval_len v hv
        dsimp only
        split
        · rename_i m' hst
          intro hrun
          injection hrun with _ hpost
          subst hpost
          have hdom0 : s.memaddrs addr := by
            have := panMemStoresHOL_dom_all_add (flattenHOL v) addr s.memory m' hst 0 (by omega)
            simpa using this
          obtain ⟨hfit, i, hi, h1, h2⟩ := hin addr hdst hdom0
          have ha8 : addr.toNat % 8 = 0 := by
            have hdom' := hma_ord ▸ hdom0
            rw [Wave8Contracts.M08.ordinaryDomain_iff] at hdom'; exact hdom'.1
          have hstep_toNat : ∀ k, k < nw →
              (addr + BitVec.ofNat 64 (8 * k)).toNat = addr.toNat + 8 * k := by
            intro k hk
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
          · intro a hna
            apply panMemStoresHOL_frame_add (flattenHOL v) addr s.memory m' hst a
            intro k hk rfl
            exact hna (panMemStoresHOL_dom_all_add (flattenHOL v) addr s.memory m' hst k hk)
          · intro a hna
            apply panMemStoresHOL_frame_add (flattenHOL v) addr s.memory m' hst a
            intro k hk heq
            have hk_lt : k < nw := by omega
            have htn := hstep_toNat k hk_lt
            rw [← heq] at htn
            exact hna i hi ⟨by omega, by omega⟩
          · intro b hb hno
            unfold memB
            dsimp only
            have hm_eq : m' (panByteAlignHOL (BitVec.ofNat 64 b)) =
                s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
              apply panMemStoresHOL_frame_add (flattenHOL v) addr s.memory m' hst
              intro k hk heq
              have hk_lt : k < nw := by omega
              have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
                rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
              rw [heq, hstep_toNat k hk_lt] at hal_b
              exact hno i hi ⟨by omega, by omega⟩
            rw [hm_eq]
        · simp
    · simp
    · simp

/-! ## 3b. `bal_list_grow_worldStep` and `lst_push` on `BalListSlice` -/

private def BalListOrigin {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz : Nat) : Prop :=
  (∃ ad ∈ balRecords s,
    ((memW s (ad + 16) = l ∧ esz = 40) ∨
     (memW s (ad + 24) = l ∧ esz = 16) ∨
     (memW s (ad + 32) = l ∧ esz = 24))) ∨
  (∃ ad ∈ balRecords s, l ∈ htabValues s (memW s ad) ∧ esz = 40)

private theorem balListOrigin_slice {F : Type} {s : PanSemStateFiniteExact 64 F}
    {l esz : Nat} (horig : BalListOrigin s l esz) :
    BalListSlice s l esz := by
  rcases horig with ⟨ad, had, hwe⟩ | ⟨ad, had, hl, rfl⟩
  · rcases hwe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact bal_list_slice_of_ad_field had (Or.inl ⟨rfl, rfl⟩)
    · exact bal_list_slice_of_ad_field had (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact bal_list_slice_of_ad_field had (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact bal_list_slice_of_stor_val had hl

private theorem not_disj_self_24 (l : Nat) : ¬ Disj (l, 24) (l, 24) := by
  intro hdj; rcases hdj with d | d | d | d <;> dsimp only at d <;> omega

private theorem bal_list_grow_worldStep {F : Type}
    {s0 m post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l esz np cap : Nat}
    (hW : WorldOK s0)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (horig_all : ∀ S Nd, WorldTypedWith s0 S Nd → LstOK s0 l ∧ BalListOrigin s0 l esz)
    (hcap_eq : memW s0 (l + 16) = cap)
    (hAm : ArenaReady m)
    (hm_mem : m.memory = s0.memory)
    (hm_be : m.be = s0.be)
    (hm_gl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s0.globals.lookup k = m.globals.lookup k)
    (hnp_eq : np = globN s0 "heap_ptr")
    (hhp_m : globN m "heap_ptr" = np + 2 * esz * cap)
    (heff : M11.ByteRegionEffect m post [(np, 2 * esz * cap), (l, 24)])
    (hl0_post : memW post l = np)
    (hl8_post : memW post (l + 8) ≤ 2 * cap)
    (hl16_post : memW post (l + 16) = 2 * cap) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s0 r post := by
  have hslice_all : ∀ S Nd, WorldTypedWith s0 S Nd → LstOK s0 l ∧ BalListSlice s0 l esz :=
    fun S Nd h => ⟨(horig_all S Nd h).1, balListOrigin_slice (horig_all S Nd h).2⟩
  have hAs := hW.1
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAm.1
  have hAp : ArenaReady post := ⟨hinv_post, arenaOK_congr heff.globals hAm.2⟩
  have hglob_mp : ∀ nm, globN post nm = globN m nm := fun nm => by simp [globN, heff.globals]
  have hhp_post : globN post "heap_ptr" = np + 2 * esz * cap := by rw [hglob_mp, hhp_m]
  have hhp_le : globN s0 "heap_ptr" ≤ globN post "heap_ptr" := by omega
  have hsp_eq : globN post "scratch_ptr" = globN s0 "scratch_ptr" := by
    rw [hglob_mp]
    exact Wave8Contracts.M08.globN_eq_of_lookup (hm_gl (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s0 post := ⟨hhp_le, by rw [hsp_eq]⟩
  have hG : GlobalsKept ["heap_ptr"] s0 post := by
    intro g hg
    have hg_ne : g ≠ ofString "heap_ptr" := by
      intro rfl; exact hg (List.mem_singleton.2 rfl)
    rw [heff.globals]
    exact hm_gl g hg_ne
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s0 post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by decide)
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s0 S0).1 hWT0_ex
  obtain ⟨hlst0, hslice0⟩ := hslice_all S0 Nd0 hWT0
  obtain ⟨hl_fix0, hp_fix0, _, _, _, _⟩ :=
    bal_list_slice_props hWT0.2.2.1 hl_nz hesz hlst0 hslice0
  have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
  have hcap_pos : 1 ≤ cap := by rw [← hcap_eq]; exact hlst0.1
  have hpos_arr : esz * memW s0 (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by omega))
  have hpos_new : esz * (2 * cap) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by omega))
  rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l0, hw_l0⟩
  · simp at h0
  have hl_hi : l + 24 ≤ 2 ^ 64 :=
    (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l0).2
  have hnew_sz_eq : 2 * esz * cap = esz * (2 * cap) := by ring
  have hin_new : Inside (np, esz * (2 * cap)) (globN s0 "heap_ptr") (globN post "heap_ptr") := by
    refine ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hal_new : Allocated post (np, esz * (2 * cap)) := by
    left
    refine ⟨le_trans hAs.2.1 (by dsimp only; omega), by dsimp only; omega⟩
  have hnp8 : np % 8 = 0 := by rw [hnp_eq]; exact hAs.2.2.2.2.2.2.1
  have hsz8 : (esz * (2 * cap)) % 8 = 0 := by
    rcases hesz with rfl | rfl | rfl <;> omega
  have hw_new : WordsOK post (np, esz * (2 * cap)) :=
    M13.wordsOK_of_allocated hAp hal_new hnp8 hsz8
  have hdj_new_l : Disj (l, 24) (np, esz * (2 * cap)) :=
    disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_l0 hin_new)
  have hunhit_of_disj : ∀ i : Ivl, Allocated s0 i → Disj i (l, 24) →
      M08IvlUnhit s0 post i := by
    intro i hal_i hdj_l a ha8 hi1 hi2
    have hdj_n : Disj i (np, 2 * esz * cap) := by
      rw [hnew_sz_eq]
      exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_i hin_new)
    have hm_a := heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; rcases hdj_n with d | d | d | d <;> omega
      · dsimp only at hc1 hc2; rcases hdj_l with d | d | d | d <;> omega)
    rw [hm_a, hm_mem]
  have hRK : RecordsKept (fun _ => []) stdKeep s0 post := by
    intro ⟨rec_nm, rec_ks⟩ hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec_nm, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := M11.typedRec_in_fixedObjects s0 htr
    simp only [hgnz, ↓reduceIte] at hmf
    have hgb_mem : (globN s0 rec_nm, sz) ∈
        (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] ++
        blockOutObjects s0 := by
      apply List.mem_append_left; apply List.mem_append_left
      have hr_gb : (rec_nm, sz) ∈ globalBuffers :=
        Wave8Contracts.M08.typedRecord_mem_globalBuffers htr
      have hm : (globN s0 rec_nm, if globN s0 rec_nm = 0 then 0 else sz) ∈
          globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2) :=
        List.mem_map.2 ⟨(rec_nm, sz), hr_gb, rfl⟩
      rwa [if_neg hgnz] at hm
    have hpw_top := List.pairwise_append.1 hWT0.2.2.1.2
    have hl_bal0 : (l, 24) ∈ balObjects s0 := by
      obtain ⟨L1, L2, hb, _⟩ := hslice0; rw [hb]; simp [lstObjects, hl_nz]
    have hdj_l : Disj (globN s0 rec_nm, sz) (l, 24) := hpw_top.2.2 _ hgb_mem _ hl_bal0
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal_r, hw_r⟩
    · exact absurd h0 hsz_nz
    have hhi_r := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_r).2
    have hg8 : (globN s0 rec_nm) % 8 = 0 := hw_r.1
    change memW post (globN s0 rec_nm + k) = memW s0 (globN s0 rec_nm + k)
    exact Wave8Contracts.M08.memW_eq_of_ivlUnhit
      (hunhit_of_disj _ hal_r hdj_l) (by omega) hhi_r ⟨by omega, by omega⟩
  refine ⟨hAp, hhp_le, hG, hRK, fun S Nd hWT _ => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hlst, hslice⟩ := hslice_all S Nd ⟨hT, hJ, hF, hTr⟩
  obtain ⟨hl_fix, hp_fix, hdj_lp, had_dj, hfk_dj, hst_dj⟩ :=
    bal_list_slice_props hF hl_nz hesz hlst hslice
  have hl_bal : (l, 24) ∈ balObjects s0 := by
    obtain ⟨L1, L2, hb, _⟩ := hslice; rw [hb]; simp [lstObjects, hl_nz]
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s0 t, M08IvlUnhit s0 post i := fun t ht i hi =>
    hunhit_of_disj i ((hT.2.1 t ht).2 i hi).1 (((hT.2.1 t ht).2 i hi).2 _ hl_fix)
  have hu_prefix : ∀ i ∈
      (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
      [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] ++
      blockOutObjects s0, M08IvlUnhit s0 post i := by
    intro i hi
    have hi_fix : i ∈ fixedObjects s0 := List.mem_append.2 (Or.inl hi)
    rcases hF.1 i hi_fix with h0 | ⟨hal_i, _⟩
    · intro a _ ha1 ha2; omega
    · exact hunhit_of_disj i hal_i ((List.pairwise_append.1 hF.2).2.2 i hi _ hl_bal)
  have hmem_gb_prefix : ∀ (nm : String) (sz : Nat), (nm, sz) ∈ globalBuffers → globN s0 nm ≠ 0 →
      (globN s0 nm, sz) ∈
        (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] ++
        blockOutObjects s0 := fun nm sz hgb hnz => by
    apply List.mem_append_left; apply List.mem_append_left
    have hm_in : (globN s0 nm, if globN s0 nm = 0 then 0 else sz) ∈
        globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2) :=
      List.mem_map.2 ⟨(nm, sz), hgb, rfl⟩
    rwa [if_neg hnz] at hm_in
  have hu_ws : globN s0 "ws" ≠ 0 → M08IvlUnhit s0 post (globN s0 "ws", 40) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "ws" 40 (by decide) hnz)
  have hu_bs : globN s0 "bs" ≠ 0 → M08IvlUnhit s0 post (globN s0 "bs", 80) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "bs" 80 (by decide) hnz)
  have hu_ts : globN s0 "ts" ≠ 0 → M08IvlUnhit s0 post (globN s0 "ts", 72) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "ts" 72 (by decide) hnz)
  have hu_bo : globN s0 "bo" ≠ 0 → M08IvlUnhit s0 post (globN s0 "bo", 88) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "bo" 88 (by decide) hnz)
  have hu_jr : globN s0 "journal_cap" ≠ 0 →
      M08IvlUnhit s0 post (globN s0 "journal", 32 * globN s0 "journal_cap") := fun hnz =>
    hu_prefix _ (List.mem_append_left _ (List.mem_append_right _ (by simp [hnz])))
  have hu_bo_lst : ∀ i ∈ blockOutObjects s0, i.2 = 24 → M08IvlUnhit s0 post i := fun i hi _ =>
    hu_prefix _ (List.mem_append_right _ hi)
  have hm0 : memW post 0 = memW s0 0 ∧ memW post 8 = memW s0 8 ∧ memW post 16 = memW s0 16 := by
    have hdom_writes : ∀ a : BitVec 64, post.memory a ≠ s0.memory a → s0.memaddrs a := by
      intro a hne
      apply Classical.byContradiction
      intro hna
      have hna_m : ¬ m.memaddrs a := by
        rw [hAm.1.memaddrs, ← hAs.1.memaddrs]
        exact hna
      have heq := heff.out_dom a hna_m
      rw [hm_mem] at heq
      exact hne heq
    exact Wave8Contracts.M08.mem0_8_16_eq_of_domain_writes hdom_writes hAs.1
  have hlst_l_post : LstOK post l := by
    unfold LstOK
    rw [hl16_post]
    exact ⟨by omega, hl8_post⟩
  have hlst_l_objs_post : ∀ esz_k, esz_k = esz →
      lstObjects post l esz_k = [(l, 24), (np, esz * (2 * cap))] := by
    intro esz_k rfl
    simp [lstObjects, hl_nz, hl0_post, hl16_post, hpos_new]
  have hba_g : globN post "bal_accounts" = globN s0 "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hrecs_bal : balRecords post = balRecords s0 :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have hlst_hdr_unhit_eq : ∀ (x esz_x : Nat), x ≠ 0 → (x, 24) ∈ fixedObjects s0 →
      Disj (x, 24) (l, 24) →
      lstObjects post x esz_x = lstObjects s0 x esz_x ∧ (LstOK s0 x → LstOK post x) := by
    intro x esz_x hx_nz hx_fix hdj1
    rcases hF.1 _ hx_fix with h0 | ⟨hal_x, hw_x⟩
    · simp at h0
    have hhi_x := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_x).2
    have hx8 : x % 8 = 0 := hw_x.1
    have hux := hunhit_of_disj _ hal_x hdj1
    have hw0 : memW post x = memW s0 x := by
      simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hux (by omega) hhi_x ⟨by omega, by omega⟩
    have hw8 : memW post (x + 8) = memW s0 (x + 8) :=
      Wave8Contracts.M08.memW_eq_of_ivlUnhit hux (by omega) hhi_x ⟨by omega, by omega⟩
    have hw16 : memW post (x + 16) = memW s0 (x + 16) :=
      Wave8Contracts.M08.memW_eq_of_ivlUnhit hux (by omega) hhi_x ⟨by omega, by omega⟩
    refine ⟨by simp [lstObjects, hx_nz, hw0, hw16], fun hx_ok => ?_⟩
    unfold LstOK at hx_ok ⊢; rw [hw8, hw16]; exact hx_ok
  have had_all : ∀ ad ∈ balRecords s0,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s0 (ad + off)) ∧
      htabValues post (memW s0 ad) = htabValues s0 (memW s0 ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW s0 (ad + k))) ∧
      (∀ l' ∈ htabValues s0 (memW s0 ad), LstOK post l') := by
    intro ad had
    have had_fix : (ad, 40) ∈ fixedObjects s0 :=
      List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨ad, had, by simp⟩))
    rcases hF.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hu_ad := hunhit_of_disj _ hal_ad (had_dj ad had).1
    have hoff : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s0 (ad + off) := by
      intro off hoff_m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff_m
      rcases hoff_m with rfl | rfl | rfl | rfl | rfl <;>
        exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ad (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s0 ad) = htabValues s0 (memW s0 ad) :=
      Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
    refine ⟨hoff, hvals_ad, ?_, ?_⟩
    · intro k hk
      by_cases hkz : memW s0 (ad + k) = 0
      · have h_old := had_T.2.2.1 k hk
        unfold LstOK at h_old ⊢; rw [hkz, hm0.2.1, hm0.2.2]; simpa [hkz] using h_old
      · by_cases hkl : memW s0 (ad + k) = l
        · rw [hkl]; exact hlst_l_post
        · have hmem_bal := (bal_chunk_mem_of_record s0 had).2.1 k hk hkz
          exact (hlst_hdr_unhit_eq _ 40 hkz (List.mem_append.2 (Or.inr hmem_bal))
            (hfk_dj ad had k hk hkz hkl).1).2 (had_T.2.2.1 k hk)
    · intro l' hl'
      by_cases hlz : l' = 0
      · subst hlz
        have h_old := had_T.2.2.2 0 hl'
        unfold LstOK at h_old ⊢; rw [hm0.2.1, hm0.2.2]; exact h_old
      · by_cases hll : l' = l
        · subst hll; exact hlst_l_post
        · have hmem_bal := (bal_chunk_mem_of_record s0 had).2.2 l' hl' hlz
          exact (hlst_hdr_unhit_eq _ 40 hlz (List.mem_append.2 (Or.inr hmem_bal))
            (hst_dj ad had l' hl' hlz hll).1).2 (had_T.2.2.2 l' hl')
  have hpw_bal_s0 : (balObjects s0).Pairwise Disj := (List.pairwise_append.1 hF.2).2.1
  have hlst_other_bal : ∀ x esz_x, x ≠ l →
      (x ≠ 0 → (x, 24) ∈ fixedObjects s0 ∧ Disj (x, 24) (l, 24)) →
      lstObjects post x esz_x = lstObjects s0 x esz_x := by
    intro x esz_x hxl hcond
    by_cases hxz : x = 0
    · subst hxz; simp [lstObjects]
    · obtain ⟨hxf, hdj1⟩ := hcond hxz
      exact (hlst_hdr_unhit_eq x esz_x hxz hxf hdj1).1
  have horig := (horig_all S Nd ⟨hT, hJ, hF, hTr⟩).2
  -- Strengthen `balObjects_replace_of_origin` inline using `had_all` and `hlst_other_bal`:
  have flatMap_eq_of_off : ∀ {α β : Type} {xs : List α} {f g : α → List β},
      (∀ x ∈ xs, f x = g x) → xs.flatMap f = xs.flatMap g := fun h => List.flatMap_congr h
  let f0 := fun a : Nat => (a, 40) :: lstObjects s0 (memW s0 (a + 16)) 40 ++
    lstObjects s0 (memW s0 (a + 24)) 16 ++ lstObjects s0 (memW s0 (a + 32)) 24 ++
    (htabValues s0 (memW s0 a)).flatMap (fun x => lstObjects s0 x 40)
  let fp := fun a : Nat => (a, 40) :: lstObjects post (memW post (a + 16)) 40 ++
    lstObjects post (memW post (a + 24)) 16 ++ lstObjects post (memW post (a + 32)) 24 ++
    (htabValues post (memW post a)).flatMap (fun x => lstObjects post x 40)
  have hslice_both : ∃ L1 L2,
      balObjects s0 = L1 ++ lstObjects s0 l esz ++ L2 ∧
      balObjects post = L1 ++ lstObjects post l esz ++ L2 := by
    have hmem_head_of_eq : ∀ {y esz_y : Nat}, y = l → (l, 24) ∈ lstObjects s0 y esz_y := by
      intro y esz_y hy; subst hy; exact lstObjects_head_mem s0 hl_nz
    have hf_eq_of_not_mem : ∀ a ∈ balRecords s0, (l, 24) ∉ f0 a → fp a = f0 a := by
      intro a ha hnin
      have hp := had_all a ha
      have e0 : memW post a = memW s0 a := by simpa using hp.1 0 (by simp)
      have e16 := hp.1 16 (by simp)
      have e24 := hp.1 24 (by simp)
      have e32 := hp.1 32 (by simp)
      have hne16 : memW s0 (a + 16) ≠ l := fun he =>
        hnin (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (hmem_head_of_eq he)))))
      have hne24 : memW s0 (a + 24) ≠ l := fun he =>
        hnin (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (hmem_head_of_eq he))))
      have hne32 : memW s0 (a + 32) ≠ l := fun he =>
        hnin (List.mem_append_left _ (List.mem_append_right _
          (hmem_head_of_eq he)))
      have hne_st : ∀ x ∈ htabValues s0 (memW s0 a), x ≠ l := fun x hx he =>
        hnin (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩))
      have ho16 := hlst_other_bal (memW s0 (a + 16)) 40 hne16 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 ha).2.1 16 (by simp) hnz)),
         (hfk_dj a ha 16 (by simp) hnz hne16).1⟩
      have ho24 := hlst_other_bal (memW s0 (a + 24)) 16 hne24 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 ha).2.1 24 (by simp) hnz)),
         (hfk_dj a ha 24 (by simp) hnz hne24).1⟩
      have ho32 := hlst_other_bal (memW s0 (a + 32)) 24 hne32 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 ha).2.1 32 (by simp) hnz)),
         (hfk_dj a ha 32 (by simp) hnz hne32).1⟩
      dsimp only [fp, f0]
      rw [e0, e16, e24, e32, hp.2.1, ho16, ho24, ho32]
      congr 1
      apply List.flatMap_congr; intro x hx
      exact hlst_other_bal x 40 (hne_st x hx) fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 ha).2.2 x hx hnz)),
         (hst_dj a ha x hx hnz (hne_st x hx)).1⟩
    rcases horig with ⟨ad, had, hwe⟩ | ⟨ad, had, hl_in, rfl⟩
    · obtain ⟨R1, R2, hrec⟩ := List.append_of_mem had
      have hbal0 : balObjects s0 = R1.flatMap f0 ++ f0 ad ++ R2.flatMap f0 := by
        change (balRecords s0).flatMap f0 = _
        rw [hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have hbalp : balObjects post = R1.flatMap fp ++ fp ad ++ R2.flatMap fp := by
        change (balRecords post).flatMap fp = _
        rw [hrecs_bal, hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have hl_in_fad : (l, 24) ∈ f0 ad := by
        rcases hwe with ⟨h16, _⟩ | ⟨h24, _⟩ | ⟨h32, _⟩
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (hmem_head_of_eq h16))))
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (hmem_head_of_eq h24)))
        · exact List.mem_append_left _ (List.mem_append_right _
            (hmem_head_of_eq h32))
      have hpw3 := hbal0 ▸ hpw_bal_s0
      have hR1_eq : R1.flatMap fp = R1.flatMap f0 := by
        apply List.flatMap_congr; intro a ha
        refine hf_eq_of_not_mem a (by rw [hrec]; exact List.mem_append_left _ ha) fun hin => ?_
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw3
          (Or.inl (List.mem_flatMap.2 ⟨a, ha, hin⟩)) hl_in_fad)
      have hR2_eq : R2.flatMap fp = R2.flatMap f0 := by
        apply List.flatMap_congr; intro a ha
        refine hf_eq_of_not_mem a (by rw [hrec]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)) fun hin => ?_
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw3
          (Or.inr (List.mem_flatMap.2 ⟨a, ha, hin⟩)) hl_in_fad)
      have hpw_fad : (f0 ad).Pairwise Disj :=
        (List.pairwise_append.1 (List.pairwise_append.1 hpw3).1).2.1
      have hp := had_all ad had
      have e0 : memW post ad = memW s0 ad := by simpa using hp.1 0 (by simp)
      have e16 := hp.1 16 (by simp)
      have e24 := hp.1 24 (by simp)
      have e32 := hp.1 32 (by simp)
      rcases hwe with ⟨h16, rfl⟩ | ⟨h24, rfl⟩ | ⟨h32, rfl⟩
      · have hpw_sub : (([(ad, 40)]) ++ lstObjects s0 l 40 ++
            (lstObjects s0 (memW s0 (ad + 24)) 16 ++ lstObjects s0 (memW s0 (ad + 32)) 24 ++
              (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40))).Pairwise Disj := by
          simpa [f0, h16, List.append_assoc] using hpw_fad
        have hne24 : memW s0 (ad + 24) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_left _ (List.mem_append_left _ (hmem_head_of_eq he))))
            (lstObjects_head_mem s0 hl_nz))
        have hne32 : memW s0 (ad + 32) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_left _ (List.mem_append_right _ (hmem_head_of_eq he))))
            (lstObjects_head_mem s0 hl_nz))
        have hne_st : ∀ x ∈ htabValues s0 (memW s0 ad), x ≠ l := fun x hx he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩)))
            (lstObjects_head_mem s0 hl_nz))
        have ho24 := hlst_other_bal (memW s0 (ad + 24)) 16 hne24 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 24 (by simp) hnz)),
           (hfk_dj ad had 24 (by simp) hnz hne24).1⟩
        have ho32 := hlst_other_bal (memW s0 (ad + 32)) 24 hne32 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 32 (by simp) hnz)),
           (hfk_dj ad had 32 (by simp) hnz hne32).1⟩
        refine ⟨R1.flatMap f0 ++ [(ad, 40)],
          lstObjects s0 (memW s0 (ad + 24)) 16 ++ lstObjects s0 (memW s0 (ad + 32)) 24 ++
            (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40) ++ R2.flatMap f0,
          by rw [hbal0]; simp [f0, h16, List.append_assoc], ?_⟩
        rw [hbalp, hR1_eq, hR2_eq]; dsimp only [fp]
        rw [e0, e16, e24, e32, hp.2.1, h16, ho24, ho32,
          flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_st x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x hx hnz)),
             (hst_dj ad had x hx hnz (hne_st x hx)).1⟩]
        simp [List.append_assoc]
      · have hpw_sub : (([(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40) ++ lstObjects s0 l 16 ++
            (lstObjects s0 (memW s0 (ad + 32)) 24 ++
              (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40))).Pairwise Disj := by
          simpa [f0, h24, List.append_assoc] using hpw_fad
        have hne16 : memW s0 (ad + 16) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inl (List.mem_append_right _ (hmem_head_of_eq he)))
            (lstObjects_head_mem s0 hl_nz))
        have hne32 : memW s0 (ad + 32) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_left _ (hmem_head_of_eq he)))
            (lstObjects_head_mem s0 hl_nz))
        have hne_st : ∀ x ∈ htabValues s0 (memW s0 ad), x ≠ l := fun x hx he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩)))
            (lstObjects_head_mem s0 hl_nz))
        have ho16 := hlst_other_bal (memW s0 (ad + 16)) 40 hne16 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 16 (by simp) hnz)),
           (hfk_dj ad had 16 (by simp) hnz hne16).1⟩
        have ho32 := hlst_other_bal (memW s0 (ad + 32)) 24 hne32 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 32 (by simp) hnz)),
           (hfk_dj ad had 32 (by simp) hnz hne32).1⟩
        refine ⟨R1.flatMap f0 ++ [(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40,
          lstObjects s0 (memW s0 (ad + 32)) 24 ++
            (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40) ++ R2.flatMap f0,
          by rw [hbal0]; simp [f0, h24, List.append_assoc], ?_⟩
        rw [hbalp, hR1_eq, hR2_eq]; dsimp only [fp]
        rw [e0, e16, e24, e32, hp.2.1, h24, ho16, ho32,
          flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_st x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x hx hnz)),
             (hst_dj ad had x hx hnz (hne_st x hx)).1⟩]
        simp [List.append_assoc]
      · have hpw_sub : (([(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40 ++
              lstObjects s0 (memW s0 (ad + 24)) 16) ++ lstObjects s0 l 24 ++
            (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40)).Pairwise Disj := by
          simpa [f0, h32, List.append_assoc] using hpw_fad
        have hne16 : memW s0 (ad + 16) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inl (List.mem_append_left _ (List.mem_append_right _ (hmem_head_of_eq he))))
            (lstObjects_head_mem s0 hl_nz))
        have hne24 : memW s0 (ad + 24) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inl (List.mem_append_right _ (hmem_head_of_eq he)))
            (lstObjects_head_mem s0 hl_nz))
        have hne_st : ∀ x ∈ htabValues s0 (memW s0 ad), x ≠ l := fun x hx he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩))
            (lstObjects_head_mem s0 hl_nz))
        have ho16 := hlst_other_bal (memW s0 (ad + 16)) 40 hne16 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 16 (by simp) hnz)),
           (hfk_dj ad had 16 (by simp) hnz hne16).1⟩
        have ho24 := hlst_other_bal (memW s0 (ad + 24)) 16 hne24 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 24 (by simp) hnz)),
           (hfk_dj ad had 24 (by simp) hnz hne24).1⟩
        refine ⟨R1.flatMap f0 ++ [(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40 ++
            lstObjects s0 (memW s0 (ad + 24)) 16,
          (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40) ++ R2.flatMap f0,
          by rw [hbal0]; simp [f0, h32, List.append_assoc], ?_⟩
        rw [hbalp, hR1_eq, hR2_eq]; dsimp only [fp]
        rw [e0, e16, e24, e32, hp.2.1, h32, ho16, ho24,
          flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_st x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x hx hnz)),
             (hst_dj ad had x hx hnz (hne_st x hx)).1⟩]
        simp [List.append_assoc]
    · obtain ⟨R1, R2, hrec⟩ := List.append_of_mem had
      obtain ⟨V1, V2, hval⟩ := List.append_of_mem hl_in
      have hbal0 : balObjects s0 = R1.flatMap f0 ++ f0 ad ++ R2.flatMap f0 := by
        change (balRecords s0).flatMap f0 = _
        rw [hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have hbalp : balObjects post = R1.flatMap fp ++ fp ad ++ R2.flatMap fp := by
        change (balRecords post).flatMap fp = _
        rw [hrecs_bal, hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have hl_in_fad : (l, 24) ∈ f0 ad :=
        List.mem_append_right _ (List.mem_flatMap.2 ⟨l, hl_in, lstObjects_head_mem s0 hl_nz⟩)
      have hpw3 := hbal0 ▸ hpw_bal_s0
      have hR1_eq : R1.flatMap fp = R1.flatMap f0 := by
        apply List.flatMap_congr; intro a ha
        refine hf_eq_of_not_mem a (by rw [hrec]; exact List.mem_append_left _ ha) fun hin => ?_
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw3
          (Or.inl (List.mem_flatMap.2 ⟨a, ha, hin⟩)) hl_in_fad)
      have hR2_eq : R2.flatMap fp = R2.flatMap f0 := by
        apply List.flatMap_congr; intro a ha
        refine hf_eq_of_not_mem a (by rw [hrec]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)) fun hin => ?_
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw3
          (Or.inr (List.mem_flatMap.2 ⟨a, ha, hin⟩)) hl_in_fad)
      have hpw_fad : (f0 ad).Pairwise Disj :=
        (List.pairwise_append.1 (List.pairwise_append.1 hpw3).1).2.1
      have hp := had_all ad had
      have e0 : memW post ad = memW s0 ad := by simpa using hp.1 0 (by simp)
      have e16 := hp.1 16 (by simp)
      have e24 := hp.1 24 (by simp)
      have e32 := hp.1 32 (by simp)
      have hpw_sub : (([(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40 ++
          lstObjects s0 (memW s0 (ad + 24)) 16 ++ lstObjects s0 (memW s0 (ad + 32)) 24 ++
          V1.flatMap (fun x => lstObjects s0 x 40)) ++ lstObjects s0 l 40 ++
          V2.flatMap (fun x => lstObjects s0 x 40)).Pairwise Disj := by
        dsimp only [f0] at hpw_fad
        rw [hval] at hpw_fad
        simpa [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hpw_fad
      have hne16 : memW s0 (ad + 16) ≠ l := fun he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ (hmem_head_of_eq he))))))
          (lstObjects_head_mem s0 hl_nz))
      have hne24 : memW s0 (ad + 24) ≠ l := fun he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inl (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ (hmem_head_of_eq he)))))
          (lstObjects_head_mem s0 hl_nz))
      have hne32 : memW s0 (ad + 32) ≠ l := fun he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inl (List.mem_append_left _ (List.mem_append_right _ (hmem_head_of_eq he))))
          (lstObjects_head_mem s0 hl_nz))
      have hne_V1 : ∀ x ∈ V1, x ≠ l := fun x hx he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inl (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩)))
          (lstObjects_head_mem s0 hl_nz))
      have hne_V2 : ∀ x ∈ V2, x ≠ l := fun x hx he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inr (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩))
          (lstObjects_head_mem s0 hl_nz))
      have ho16 := hlst_other_bal (memW s0 (ad + 16)) 40 hne16 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 16 (by simp) hnz)),
         (hfk_dj ad had 16 (by simp) hnz hne16).1⟩
      have ho24 := hlst_other_bal (memW s0 (ad + 24)) 16 hne24 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 24 (by simp) hnz)),
         (hfk_dj ad had 24 (by simp) hnz hne24).1⟩
      have ho32 := hlst_other_bal (memW s0 (ad + 32)) 24 hne32 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 32 (by simp) hnz)),
         (hfk_dj ad had 32 (by simp) hnz hne32).1⟩
      refine ⟨R1.flatMap f0 ++ [(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40 ++
          lstObjects s0 (memW s0 (ad + 24)) 16 ++ lstObjects s0 (memW s0 (ad + 32)) 24 ++
          V1.flatMap (fun x => lstObjects s0 x 40),
        V2.flatMap (fun x => lstObjects s0 x 40) ++ R2.flatMap f0,
        by rw [hbal0]; dsimp only [f0]; rw [hval]
           simp [List.flatMap_append, List.flatMap_cons, List.append_assoc], ?_⟩
      rw [hbalp, hR1_eq, hR2_eq]; dsimp only [fp]
      rw [e0, e16, e24, e32, hp.2.1, hval, ho16, ho24, ho32]
      simp only [List.flatMap_append, List.flatMap_cons]
      rw [flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_V1 x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x
              (by rw [hval]; exact List.mem_append_left _ hx) hnz)),
             (hst_dj ad had x (by rw [hval]; exact List.mem_append_left _ hx) hnz (hne_V1 x hx)).1⟩,
          flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_V2 x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x
              (by rw [hval]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hnz)),
             (hst_dj ad had x (by rw [hval]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hnz (hne_V2 x hx)).1⟩]
      simp [List.append_assoc]
  obtain ⟨L1, L2, hbal_s0_eq, hbal_post_eq⟩ := hslice_both
  have hlst_post_eq : lstObjects post l esz = [(l, 24), (np, esz * (2 * cap))] :=
    hlst_l_objs_post esz rfl
  have hbo_g : globN post "bo" = globN s0 "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hws_g : globN post "ws" = globN s0 "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s0 "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s0 "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hbia_g : globN post "bal_idx_accts" = globN s0 "bal_idx_accts" :=
    hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g : globN post "bal_idx_stor" = globN s0 "bal_idx_stor" :=
    hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  have htr_ws : ("ws", 40) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_bs : ("bs", 80) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_ts : ("ts", 72) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_bo : ("bo", 88) ∈ Wave8Contracts.M08.typedRecords := by decide
  have hbo_words : globN s0 "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s0 "bo" + k) = memW s0 (globN s0 "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using Wave8Contracts.M08.rec_word_eq_of_unhit
      hAs.2 hF "bo" 88 htr_bo hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun h h40 => hu_bo_lst (memW s0 (globN s0 "bo" + 40), 24) (by simp [blockOutObjects, h, h40]) rfl)
    (fun h h72 => hu_bo_lst (memW s0 (globN s0 "bo" + 72), 24) (by simp [blockOutObjects, h, h72]) rfl)
  let pref0 := (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
    [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] ++
    blockOutObjects s0
  have hfix_post_eq : fixedObjects post = pref0 ++ (L1 ++ lstObjects post l esz ++ L2) := by
    unfold fixedObjects
    rw [hbo_part.1, hbal_post_eq, hgs.2.2.1, hgs.2.2.2.1]
    congr 1; congr 1; congr 1
    apply List.map_congr_left; intro gn hgn; rw [hgs.1 gn hgn]
  have hfix_s0_eq : fixedObjects s0 = pref0 ++ (L1 ++ lstObjects s0 l esz ++ L2) := by
    unfold fixedObjects; rw [hbal_s0_eq]
  have hfix_from : ∀ x ∈ fixedObjects post,
      x ∈ fixedObjects s0 ∨ x = (np, esz * (2 * cap)) := by
    intro x hx
    rw [hfix_post_eq, hlst_post_eq] at hx
    rcases List.mem_append.1 hx with hxp | hxb
    · exact Or.inl (List.mem_append.2 (Or.inl hxp))
    · rcases List.mem_append.1 hxb with hxb1 | hx2
      · rcases List.mem_append.1 hxb1 with hx1 | hxm
        · exact Or.inl (by rw [hfix_s0_eq]; exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hx1)))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxm
          rcases hxm with rfl | rfl
          · exact Or.inl hl_fix
          · exact Or.inr rfl
      · exact Or.inl (by rw [hfix_s0_eq]; exact List.mem_append_right _ (List.mem_append_right _ hx2))
  have hdisj_old_new : ∀ x ∈ fixedObjects s0, Disj x (np, esz * (2 * cap)) := by
    intro x hx
    rcases hF.1 x hx with h0 | ⟨hal_x, _⟩
    · exact Or.inl h0
    · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_x hin_new)
  have hF_post : FixedTyped post := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases hfix_from x hx with hx_s | rfl
      · rcases hF.1 x hx_s with h0 | ⟨hal_x, hw_x⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hag.allocated hal_x, Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw_x⟩
      · exact Or.inr ⟨hal_new, hw_new⟩
    · rw [hfix_post_eq, hlst_post_eq]
      have hpw_f0 := hfix_s0_eq ▸ hF.2
      have hpw_f0' : ((pref0 ++ L1) ++ lstObjects s0 l esz ++ L2).Pairwise Disj := by
        simpa [List.append_assoc] using hpw_f0
      have hpw_rep := pairwise_disj_replace_slice hpw_f0'
        (List.pairwise_cons.2 ⟨fun y hy => by simp at hy; subst hy; exact hdj_new_l, List.pairwise_singleton _ _⟩)
        (fun x hx y hy => by
          have hx_f0 : x ∈ fixedObjects s0 := by
            rw [hfix_s0_eq]
            rcases List.mem_append.1 hx with hxp | hx1
            · exact List.mem_append_left _ hxp
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hx1))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact pairwise_disj_outside_slice hpw_f0' (Or.inl hx) (lstObjects_head_mem s0 hl_nz)
          · exact hdisj_old_new x hx_f0)
        (fun x hx y hy => by
          have hy_f0 : y ∈ fixedObjects s0 := by
            rw [hfix_s0_eq]; exact List.mem_append_right _ (List.mem_append_right _ hy)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact disj_flip (pairwise_disj_outside_slice hpw_f0' (Or.inr hy) (lstObjects_head_mem s0 hl_nz))
          · exact disj_flip (hdisj_old_new y hy_f0))
      simpa [List.append_assoc] using hpw_rep
  have hjr_part := Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s0 := by
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles s0 "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN s0 "ws" = 0
      · simp [hws_g, h]
      · have hw16 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
        have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
        simp only [hws_g] at hw16 hw32 ⊢
        simp [h, hw16, hw32]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s0 "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN s0 "bs" = 0
      · simp [hbs_g, h]
      · simp only [hbs_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g h (hu_bs h) hk.1 hk.2
        simp only [hbs_g] at hw; simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s0 "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN s0 "ts" = 0
      · simp [hts_g, h]
      · simp only [hts_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g h (hu_ts h) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s0 "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s0 "bs" = 0
      · simp [hbs_g, h]
      · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s0 (globN s0 "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s0 (globN s0 "bs" + 32) ∈ S := by
            rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s0 "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN s0 "ts" = 0
      · simp [hts_g, h]
      · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s0 (globN s0 "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s0 (globN s0 "ts" + 32) ∈ S := by
            rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
    congr 1; congr 1
    apply List.flatMap_congr; intro ad had
    have had0 : memW post ad = memW s0 ad := by simpa using (had_all ad had).1 0 (by simp)
    have had8 : memW post (ad + 8) = memW s0 (ad + 8) := (had_all ad had).1 8 (by simp)
    rw [had0, had8]
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s0 post (nodeIvl s0 n) := fun n hn => by
    have hne_mem : nodeIvl s0 n ∈ nodeExtents s0 Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
    exact hunhit_of_disj _ (hTr.1.1 n hn).2.1 ((hTr.2.1 _ hne_mem).2 _ hl_fix)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s0 n = 1 ∨ memW s0 n = 2) → memW s0 (n + 40) ≠ 0 →
      ∀ k, k < memW s0 (n + 40) → memB post (memW s0 (n + 32) + k) = memB s0 (memW s0 (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have hnp_mem : nodePath s0 n ∈ nodeExtents s0 Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩
    have hnp_eq : nodePath s0 n = (memW s0 (n + 32), memW s0 (n + 40)) := by
      simp [nodePath, h12, hlen0]
    have hdj_l : Disj (memW s0 (n + 32), memW s0 (n + 40)) (l, 24) := by
      rw [← hnp_eq]; exact (hTr.2.1 _ hnp_mem).2 _ hl_fix
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_np, hin_p, _⟩
    · exact absurd h0 hlen0
    have hdj_n : Disj (memW s0 (n + 32), memW s0 (n + 40)) (np, 2 * esz * cap) := by
      rw [hnew_sz_eq]
      exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_np hin_new)
    have hlim264 : heapLimit ≤ 2 ^ 64 := by decide
    have hbk_lt : memW s0 (n + 32) + k < 2 ^ 64 := by
      have := hin_p.2; dsimp at this; omega
    have hb_eq := heff.byte_frame (memW s0 (n + 32) + k) hbk_lt (fun x hx hbi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hb1, hb2⟩ := hbi
      rcases hx with rfl | rfl
      · dsimp only at hb1 hb2; rcases hdj_n with d | d | d | d <;> omega
      · dsimp only at hb1 hb2; rcases hdj_l with d | d | d | d <;> omega)
    rw [hb_eq]
    unfold memB
    rw [hm_mem, hm_be]
  have hnd_part := Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s0 t k) ∧
      htabFootprint post t = htabFootprint s0 t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s0 t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
      ht8 hhi (hu_tab t ht _ ht_fp)
  have hflat_fp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s0) :=
    List.flatMap_congr fun t ht => (htab_fp_hdr t ht).2
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2]
      refine ⟨Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, fun j hj => ?_⟩⟩
      rcases hfix_from j hj with hj_s | rfl
      · exact ((hTt t ht).2 i hi).2 j hj_s
      · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 ((hTt t ht).2 i hi).1 hin_new)
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg; rw [hgs.2.1 g hg]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      rw [hrecs_bal] at had
      have hp := had_all ad had
      have h0 : memW post ad = memW s0 ad := by simpa using hp.1 0 (by simp)
      have h8 : memW post (ad + 8) = memW s0 (ad + 8) := hp.1 8 (by simp)
      have had_old := hbalT ad had
      refine ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, ?_, ?_⟩
      · intro k hk
        have hk5 : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
          rcases hk with rfl | rfl | rfl <;> simp
        rw [hp.1 k hk5]; exact hp.2.2.1 k hk
      · intro l' hl'; rw [h0, hp.2.1] at hl'; exact hp.2.2.2 l' hl'
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_part.1]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      have ho_alloc : o = (0, 0) ∨ Allocated s0 o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hTr.1.1 n hn).2.1
        · unfold nodePath
          split
          · rename_i hcond
            rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hcond.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [(htab_fp_hdr t ht).2] at hi
        exact (hTr.2.1 o ho).1 t ht i hi
      · rcases hfix_from j hj with hj_s | rfl
        · exact (hTr.2.1 o ho).2 j hj_s
        · rcases ho_alloc with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_o hin_new)
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s0 (globN s0 "ws" + 32)))[i]? =
          (htabValues s0 (memW s0 (globN s0 "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  have hfr : FrameOutside s0 post (worldOwned s0 S Nd ++ ([] : List Ivl) ++ [freeGap s0]) (heapFree s0) := by
    intro a ha hnhf
    have hm_a := heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      have hl_ow : (l, 24) ∈ worldOwned s0 S Nd ++ ([] : List Ivl) ++ [freeGap s0] := by
        apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_left _ (List.mem_append_right _ hl_fix)
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2
        have hlim : np + 2 * esz * cap ≤ heapLimit := by
          have := hAp.2.2.1; omega
        exact hnhf ⟨by unfold heapFree M13.heapFree; dsimp only; omega,
                    by unfold heapFree M13.heapFree; dsimp only; omega⟩
      · exact ha (l, 24) hl_ow ⟨hc1, hc2⟩)
    rw [hm_a, hm_mem]
  have hOG : OwnedGrows s0 post (worldOwned s0 S Nd) (worldOwned post S Nd) := by
    intro o ho
    unfold worldOwned M13.worldOwned at ho
    simp only [List.mem_append] at ho
    rcases ho with (ho_tab | ho_fix) | ho_nd
    · rw [hflat_fp] at ho_tab
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ ho_tab)
    · rcases hfix_from o ho_fix with ho_s | rfl
      · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned M13.worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho_s)
      · exact Or.inr (Or.inr hin_new)
    · rw [hnd_part.2] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_right _ ho_nd
  exact ⟨S, Nd, fun _ hx => hx, ⟨hT_post, hjr_part.2, hF_post, hTr_post⟩, hOG, hfr, trivial⟩

/-! ## 4. `BalListOrigin` preservation and `decCall` stepper for `lst_push` -/

private theorem balListOrigin_preserved_of_grow {F : Type}
    {s0 m post : PanSemStateFiniteExact 64 F}
    {l esz np cap : Nat}
    (hW : WorldOK s0)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (horig_all : ∀ S Nd, WorldTypedWith s0 S Nd → LstOK s0 l ∧ BalListOrigin s0 l esz)
    (hAm : ArenaReady m)
    (hm_mem : m.memory = s0.memory)
    (hm_gl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s0.globals.lookup k = m.globals.lookup k)
    (hnp_eq : np = globN s0 "heap_ptr")
    (hhp_m : globN m "heap_ptr" = np + 2 * esz * cap)
    (heff : M11.ByteRegionEffect m post [(np, 2 * esz * cap), (l, 24)])
    (S Nd : List Nat) (hWT : WorldTypedWith s0 S Nd) :
    BalListOrigin post l esz := by
  have hAs := hW.1
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAm.1
  have hAp : ArenaReady post := ⟨hinv_post, arenaOK_congr heff.globals hAm.2⟩
  have hglob_mp : ∀ nm, globN post nm = globN m nm := fun nm => by simp [globN, heff.globals]
  have hhp_post : globN post "heap_ptr" = np + 2 * esz * cap := by rw [hglob_mp, hhp_m]
  have hG : GlobalsKept ["heap_ptr"] s0 post := by
    intro g hg
    have hg_ne : g ≠ ofString "heap_ptr" := fun rfl => hg (List.mem_singleton.2 rfl)
    rw [heff.globals]; exact hm_gl g hg_ne
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s0 post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by decide)
  obtain ⟨hlst, horig⟩ := horig_all S Nd hWT
  have hslice := balListOrigin_slice horig
  obtain ⟨hT, _, hF, _⟩ := hWT
  obtain ⟨hl_fix, _, _, had_dj, _, _⟩ := bal_list_slice_props hF hl_nz hesz hlst hslice
  have hnew_sz_eq : 2 * esz * cap = esz * (2 * cap) := by ring
  have hin_new : Inside (np, esz * (2 * cap)) (globN s0 "heap_ptr") (globN post "heap_ptr") :=
    ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hnp8 : np % 8 = 0 := by rw [hnp_eq]; exact hAs.2.2.2.2.2.2.1
  have hunhit_of_disj : ∀ i : Ivl, Allocated s0 i → Disj i (l, 24) →
      M08IvlUnhit s0 post i := by
    intro i hal_i hdj_l a ha8 hi1 hi2
    have hdj_n : Disj i (np, 2 * esz * cap) := by
      rw [hnew_sz_eq]
      exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_i hin_new)
    have hm_a := heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; rcases hdj_n with d | d | d | d <;> omega
      · dsimp only at hc1 hc2; rcases hdj_l with d | d | d | d <;> omega)
    rw [hm_a, hm_mem]
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s0 t, M08IvlUnhit s0 post i := fun t ht i hi =>
    hunhit_of_disj i ((hT.2.1 t ht).2 i hi).1 (((hT.2.1 t ht).2 i hi).2 _ hl_fix)
  have hba_g : globN post "bal_accounts" = globN s0 "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hrecs_bal : balRecords post = balRecords s0 :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have had_words : ∀ ad ∈ balRecords s0,
      (∀ off ∈ ([0, 16, 24, 32] : List Nat), memW post (ad + off) = memW s0 (ad + off)) ∧
      htabValues post (memW s0 ad) = htabValues s0 (memW s0 ad) := by
    intro ad had
    have had_fix : (ad, 40) ∈ fixedObjects s0 :=
      List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨ad, had, by simp⟩))
    rcases hF.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hu_ad := hunhit_of_disj _ hal_ad (had_dj ad had).1
    refine ⟨?_, Wave8Contracts.M08.htabValues_eq_of_unhit
      (hT.2.1 _ (hT.2.2.2.2.2.2.2.2.2.1 ad had).1).1
      (hu_tab _ (hT.2.2.2.2.2.2.2.2.2.1 ad had).1)⟩
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ad (by omega) hhi_ad ⟨by omega, by omega⟩
  rcases horig with ⟨ad, had, hwe⟩ | ⟨ad, had, hl_in, rfl⟩
  · left
    refine ⟨ad, by rw [hrecs_bal]; exact had, ?_⟩
    obtain ⟨hw, _⟩ := had_words ad had
    rw [hw 16 (by simp), hw 24 (by simp), hw 32 (by simp)]
    exact hwe
  · right
    obtain ⟨hw, hv⟩ := had_words ad had
    have hw0 : memW post ad = memW s0 ad := by simpa using hw 0 (by simp)
    exact ⟨ad, by rw [hrecs_bal]; exact had, by rw [hw0, hv]; exact hl_in, rfl⟩

private theorem balListOrigin_preserved_of_nogrow {F : Type}
    {s0 post : PanSemStateFiniteExact 64 F}
    {l esz : Nat}
    (hW : WorldOK s0)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (horig_all : ∀ S Nd, WorldTypedWith s0 S Nd → LstOK s0 l ∧ BalListOrigin s0 l esz)
    (heff : M11.ByteRegionEffect s0 post [(l + 8, 8), (memW s0 l, esz * memW s0 (l + 16))])
    (S Nd : List Nat) (hWT : WorldTypedWith s0 S Nd) :
    BalListOrigin post l esz := by
  have hAs := hW.1
  have hG : GlobalsKept [] s0 post := fun _ _ => by rw [heff.globals]
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s0 post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by simp)
  obtain ⟨hlst, horig⟩ := horig_all S Nd hWT
  have hslice := balListOrigin_slice horig
  obtain ⟨hT, _, hF, _⟩ := hWT
  obtain ⟨hl_fix, hp_fix, _, had_dj, _, _⟩ := bal_list_slice_props hF hl_nz hesz hlst hslice
  have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
  have hpos_arr : esz * memW s0 (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst.1; omega))
  rcases hF.1 _ hp_fix with h0 | ⟨_, hw_p⟩
  · exact absurd h0 hpos_arr
  have hp8 : memW s0 l % 8 = 0 := hw_p.1
  have hunhit_of_disj : ∀ i : Ivl, Disj i (l, 24) → Disj i (memW s0 l, esz * memW s0 (l + 16)) →
      M08IvlUnhit s0 post i := by
    intro i hdj1 hdj2 a ha8 hi1 hi2
    exact heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; rcases hdj1 with d | d | d | d <;> omega
      · dsimp only at hc1 hc2; rcases hdj2 with d | d | d | d <;> omega)
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s0 t, M08IvlUnhit s0 post i := fun t ht i hi =>
    hunhit_of_disj i (((hT.2.1 t ht).2 i hi).2 _ hl_fix) (((hT.2.1 t ht).2 i hi).2 _ hp_fix)
  have hba_g : globN post "bal_accounts" = globN s0 "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hrecs_bal : balRecords post = balRecords s0 :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have had_words : ∀ ad ∈ balRecords s0,
      (∀ off ∈ ([0, 16, 24, 32] : List Nat), memW post (ad + off) = memW s0 (ad + off)) ∧
      htabValues post (memW s0 ad) = htabValues s0 (memW s0 ad) := by
    intro ad had
    have had_fix : (ad, 40) ∈ fixedObjects s0 :=
      List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨ad, had, by simp⟩))
    rcases hF.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hu_ad := hunhit_of_disj _ (had_dj ad had).1 (had_dj ad had).2
    refine ⟨?_, Wave8Contracts.M08.htabValues_eq_of_unhit
      (hT.2.1 _ (hT.2.2.2.2.2.2.2.2.2.1 ad had).1).1
      (hu_tab _ (hT.2.2.2.2.2.2.2.2.2.1 ad had).1)⟩
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ad (by omega) hhi_ad ⟨by omega, by omega⟩
  rcases horig with ⟨ad, had, hwe⟩ | ⟨ad, had, hl_in, rfl⟩
  · left
    refine ⟨ad, by rw [hrecs_bal]; exact had, ?_⟩
    obtain ⟨hw, _⟩ := had_words ad had
    rw [hw 16 (by simp), hw 24 (by simp), hw 32 (by simp)]
    exact hwe
  · right
    obtain ⟨hw, hv⟩ := had_words ad had
    have hw0 : memW post ad = memW s0 ad := by simpa using hw 0 (by simp)
    exact ⟨ad, by rw [hrecs_bal]; exact had, by rw [hw0, hv]; exact hl_in, rfl⟩

private theorem decCall_lst_push_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (lExp eszExp : ExpHOL 64) (lw eszw : BitVec 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (hev_l : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lExp =
      some (.val (.word lw)))
    (hev_e : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) eszExp =
      some (.val (.word eszw)))
    (hesz : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40)
    (horig_nz : lw ≠ 0 → ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s lw.toNat ∧ BalListOrigin s lw.toNat eszw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont)).1) :
    ∃ (ew : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw ≠ 0 ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid ∧
      WorldOK mid ∧
      (∀ S' Nd', WorldTypedWith mid S' Nd' →
        LstOK mid lw.toNat ∧ BalListOrigin mid lw.toNat eszw.toNat) ∧
      ew.toNat % 8 = 0 ∧
      sourceBase ≤ ew.toNat ∧
      ew.toNat + eszw.toNat ≤ heapEnd ∧
      memW mid lw.toNat ≤ ew.toNat ∧
      ew.toNat + eszw.toNat ≤ memW mid lw.toNat + eszw.toNat * memW mid (lw.toNat + 16) ∧
      mid.locals.lookup x = some (.val (.word ew)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hG := hW.1.1
  have hAs := hW.1
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [lExp, eszExp] = some [.val (.word lw), .val (.word eszw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev_l, hev_e]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "lst_push")
    (ofString "l") (ofString "esz") (sourceFnBody Guest.Software.guestFn_lst_push) lw eszw
    (by decide) (by rw [hG.code]; exact lookup_lst_push_add)
  rw [hargs] at hnt hres; dsimp only at hnt hres
  rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := (HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
      (ofString "esz", ValueHOL.val (.word eszw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_eq : ent = { s with locals := cmap, clock := s.clock - 1 } := rfl
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAs
    have hent_code : ent.code = originalRuntimeCode := hG.code
    have hent_ma : ent.memaddrs = ordinaryDomain := hG.memaddrs
    have hent_l : ent.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "esz" ≠ ofString "l" by decide]
    have hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    by_cases hlw0 : lw = 0
    · have hnot8 : ¬ ent.memaddrs 8#64 := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff]
        have hsb : sourceBase = 2701131776 := rfl
        simp [hsb]
      have hbody_err : (evaluateHOLFiniteState ent
          (sourceFnBody Guest.Software.guestFn_lst_push)).1 = some .error := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_push,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
        have hl0 : ent.locals.lookup (ofString "l") = some (.val (.word 0#64)) := by
          subst hlw0; exact hent_l
        have hev8 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) = none := by
          simp [evalHOLExact, evalListHOLExact, hl0, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.foldr, hz_8, memLoadHOLExact, hnot8]
        rw [hev8]
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rb, sb⟩
      rw [hrun] at hbody_err hres; dsimp only at hbody_err hres
      subst hbody_err
      exact absurd hres not_resumes_error
    · have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw0 (BitVec.eq_of_toNat_eq (by simpa using h))
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      obtain ⟨hlst0, horig0⟩ := horig_nz hlw0 S0 Nd0 hWT0
      have hslice0 := balListOrigin_slice horig0
      obtain ⟨hl_fix0, hp_fix0, _, _, _, _⟩ :=
        bal_list_slice_props hWT0.2.2.1 hlw_nz_nat hesz hlst0 hslice0
      have hesz_pos : 0 < eszw.toNat := by rcases hesz with h | h | h <;> omega
      have hpos_arr : eszw.toNat * memW s (lw.toNat + 16) ≠ 0 :=
        ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst0.1; omega))
      rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      rcases hWT0.2.2.1.1 _ hp_fix0 with h0 | ⟨hal_p, hw_p⟩
      · exact absurd h0 hpos_arr
      have hhe_264 : heapEnd < 2 ^ 64 := by decide
      have hlim_he : heapLimit ≤ heapEnd := by decide
      have hsb_ss : sourceBase ≤ scratchStart := by decide
      have hl_bnd : sourceBase ≤ lw.toNat ∧ lw.toNat + 24 ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l).1
        rcases hal_l with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hp_bnd : sourceBase ≤ memW s lw.toNat ∧
          memW s lw.toNat + eszw.toNat * memW s (lw.toNat + 16) ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_p).1
        rcases hal_p with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hcap_mul_le : 1 * memW s (lw.toNat + 16) ≤ eszw.toNat * memW s (lw.toNat + 16) :=
        Nat.mul_le_mul_right _ hesz_pos
      let nw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 8))
      let capw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 16))
      let pw0 : BitVec 64 := BitVec.ofNat 64 (memW s lw.toNat)
      have hnw_toNat : nw.toNat = memW s (lw.toNat + 8) := by
        dsimp [nw]; rw [BitVec.toNat_ofNat]
        have := hlst0.2
        exact Nat.mod_eq_of_lt (by omega)
      have hcapw_toNat : capw.toNat = memW s (lw.toNat + 16) := by
        dsimp [capw]; rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hpw0_toNat : pw0.toNat = memW s lw.toNat := by
        dsimp [pw0]; rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hl0_bv : lw + 0#64 = BitVec.ofNat 64 lw.toNat := by simp
      have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rfl
      have hl16_bv : lw + 16#64 = BitVec.ofNat 64 (lw.toNat + 16) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rfl
      have hl8_toNat : (lw + 8#64).toNat = lw.toNat + 8 := by
        rw [hl8_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hl16_toNat : (lw + 16#64).toNat = lw.toNat + 16 := by
        rw [hl16_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hdom_l0 : ent.memaddrs (lw + 0#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff]
        have : (lw + 0#64).toNat = lw.toNat := by simp
        rw [this]; exact ⟨hw_l.1, by omega, by omega⟩
      have hdom_l8 : ent.memaddrs (lw + 8#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff, hl8_toNat]
        exact ⟨by have := hw_l.1; omega, by omega, by omega⟩
      have hdom_l16 : ent.memaddrs (lw + 16#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff, hl16_toNat]
        exact ⟨by have := hw_l.1; omega, by omega, by omega⟩
      have hm_l0 : ent.memory (lw + 0#64) = .word pw0 := by
        change s.memory (lw + 0#64) = .word pw0
        rw [hl0_bv]; dsimp [pw0]; unfold memW
        rcases s.memory (BitVec.ofNat 64 lw.toNat) with ⟨w⟩; simp
      have hm_l8 : ent.memory (lw + 8#64) = .word nw := by
        change s.memory (lw + 8#64) = .word nw
        rw [hl8_bv]; dsimp [nw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 8)) with ⟨w⟩; simp
      have hm_l16 : ent.memory (lw + 16#64) = .word capw := by
        change s.memory (lw + 16#64) = .word capw
        rw [hl16_bv]; dsimp [capw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 16)) with ⟨w⟩; simp
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rb, sb⟩
      have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_lst_push) = (rb, sb) := hrun
      rw [hrun'] at hnt hres
      cases rb with
      | none => exact absurd hres not_resumes_error
      | some rb' =>
        cases rb' with
        | timeOut => exact absurd rfl hnt
        | «break» | «continue» | error => exact absurd hres not_resumes_error
        | finalFfi _ =>
          exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | exception e ev =>
          exfalso
          rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
          · simp at h
          · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
            exact lst_push_no_catchable_exn_add ent hent_code e ev hne (congrArg Prod.fst hrun)
        | returned vb =>
          -- Unfold the two `dec` headers (`n`, `cap`) of `guestFn_lst_push` on `hrun`:
          let e1 := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
          let e2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) e1
          let growProg : ProgHOL 64 :=
            .decCall (ofString "np") .one (ofString "alloc")
              [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]]
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "np"),
                   .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                   .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                (.seq
                  (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
                  (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                    (.panop .mul [.var .local (ofString "cap"), .const 2#64]))))
          let tailProg : ProgHOL 64 :=
            .seq
              (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                (.op .add [.var .local (ofString "n"), .const 1#64]))
              (.return (.op .add
                [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                 .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))
          have hbody_e2 : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) =
              (let out := evaluateHOLFiniteState e2
                (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                        growProg .skip)
                      tailProg);
               (out.1, { out.2 with
                 locals := HolFiniteMapExact.resVarEq
                   (HolFiniteMapExact.resVarEq out.2.locals (ofString "cap", e1.locals.lookup (ofString "cap")))
                   (ofString "n", ent.locals.lookup (ofString "n")) })) := by
            dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_push,
              InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
            rw [evaluateHOLFiniteState_dec_total]; dsimp only
            have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
            have hz_16 : (16#64 : BitVec 64) + 0 = 16#64 := BitVec.add_zero _
            have hev1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
                (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) =
                some (.val (.word nw)) := by
              simp only [evalHOLExact, evalListHOLExact, hent_l, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_8,
                memLoadHOLExact, isWfShapeExactHOL, hdom_l8, hm_l8, ↓reduceIte]
            rw [hev1]; dsimp only
            rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
            have he1_def : setVarHOLFinite (ofString "n") (.val (.word nw)) ent = e1 := rfl
            rw [he1_def, evaluateHOLFiniteState_dec_total]; dsimp only
            have he1_l : e1.locals.lookup (ofString "l") = some (.val (.word lw)) := by
              simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "n" ≠ ofString "l" by decide, hent_l]
            have he1_dom16 : e1.memaddrs (lw + 16#64) := hdom_l16
            have he1_m16 : e1.memory (lw + 16#64) = .word capw := hm_l16
            have hev2 : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
                (.load .one (.op .add [.var .local (ofString "l"), .const 16#64])) =
                some (.val (.word capw)) := by
              simp only [evalHOLExact, evalListHOLExact, he1_l, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_16,
                memLoadHOLExact, isWfShapeExactHOL, he1_dom16, he1_m16, ↓reduceIte]
            rw [hev2]; dsimp only
            rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
          rw [hbody_e2] at hrun
          dsimp only at hrun
          rcases hout_e2 : evaluateHOLFiniteState e2
              (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                      growProg .skip)
                    tailProg) with ⟨ro2, so2⟩
          rw [hout_e2] at hrun
          injection hrun with hro2 hsb_eq
          subst hro2
          have he2_eq : e2 = { s with locals := e2.locals, clock := s.clock - 1 } := by
            simp [e2, e1, setVarHOLFinite, hent_eq]
          have he2_AR : ArenaReady e2 := (arenaReady_with_locals s e2.locals (s.clock - 1)).2 hAs
          have he2_l : e2.locals.lookup (ofString "l") = some (.val (.word lw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cap" ≠ ofString "l" by decide,
              show ofString "n" ≠ ofString "l" by decide, hent_l]
          have he2_e : e2.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cap" ≠ ofString "esz" by decide,
              show ofString "n" ≠ ofString "esz" by decide, hent_e]
          have he2_n : e2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cap" ≠ ofString "n" by decide]
          have he2_c : e2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hcmp_nl : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
              (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap"))) =
              some (.val (.word (if capw.toNat ≤ nw.toNat then 1#64 else 0#64))) := by
            simp only [evalHOLExact, he2_n, he2_c, Compiler.Encoders.Asm.wordCmpHOL,
              BitVec.ult, decide_eq_true_eq]
            by_cases hle : capw.toNat ≤ nw.toNat
            · have hlt_f : ¬ (nw < capw) := fun h => by
                have := (BitVec.lt_def).1 h; omega
              simp [hle, hlt_f]
            · have hlt_bv : nw < capw := (BitVec.lt_def).2 (by omega)
              simp [hle, hlt_bv]
          rw [evaluateHOLFiniteState_seq_line780] at hout_e2
          rcases hite_out : evaluateHOLFiniteState e2
              (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                growProg .skip) with ⟨ri, si⟩
          rw [hite_out] at hout_e2
          cases ri with
          | some ri' =>
            dsimp only at hout_e2
            injection hout_e2 with hri _
            -- Neither `growProg` nor `skip` has a `return` statement!
            exfalso
            rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out
            dsimp only at hite_out
            by_cases hgrow_cond : capw.toNat ≤ nw.toNat
            · rw [if_pos hgrow_cond, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
              -- Show `growProg` cannot return `some (.returned vb)` because its body ends in `.store`, not `.return`:
              have hgrow_nret : (evaluateHOLFiniteState e2 growProg).1 ≠ some (.returned vb) := by
                intro hgr
                have hgr_nt : (evaluateHOLFiniteState e2 growProg).1 ≠ some .timeOut := by
                  rw [hgr]; simp
                have hgr_res : Resumes (evaluateHOLFiniteState e2 growProg).1 :=
                  Or.inl ⟨vb, hgr⟩
                have hmul2_ev : @evalHOLExact 64 F _ e2.toExact
                    (fun a => Classical.propDecidable (e2.memaddrs a))
                    (.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]) =
                    some (.val (.word (eszw * capw * 2#64))) := by
                  simp [evalHOLExact, evalListHOLExact, he2_e, he2_c, valueIsWord, valueWord, panOpHOL]
                obtain ⟨_, _, mid_a, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg_eq1, _⟩ :=
                  decCall_alloc_resumes e2 (ofString "np") _ (eszw * capw * 2#64) _ he2_AR hmul2_ev hgr_nt hgr_res
                rw [hg_eq1] at hgr
                rw [evaluateHOLFiniteState_seq_line780] at hgr
                rcases hmc_o : evaluateHOLFiniteState mid_a
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨rmc, smc⟩
                rw [hmc_o] at hgr
                cases rmc with
                | some rmc' =>
                  dsimp only at hgr
                  -- void `.call (some (none, none))` never produces `some (.returned _)`!
                  rw [evaluateHOLFiniteState_call] at hmc_o
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  · rename_i hnotret _ _ _
                    exact hnotret vb hgr
                | none =>
                  dsimp only at hgr
                  rw [evaluateHOLFiniteState_seq_line780] at hgr
                  rcases hst1_o : evaluateHOLFiniteState smc
                    (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) with ⟨rst1, sst1⟩
                  rw [hst1_o] at hgr
                  cases rst1 with
                  | some _ =>
                    dsimp only at hgr
                    rw [evaluateHOLFiniteState_store] at hst1_o
                    split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
                    split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
                    split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
                  | none =>
                    dsimp only at hgr
                    rw [evaluateHOLFiniteState_store] at hgr
                    split at hgr <;> try simp at hgr
                    split at hgr <;> try simp at hgr
                    split at hgr <;> try simp at hgr
              exact hgrow_nret (by rw [hite_out, hri])
            · rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
              simp at hite_out
          | none =>
            dsimp only at hout_e2
            -- `hite_out` succeeded with `(none, si)` and `hout_e2 : evaluateHOLFiniteState si tailProg = (some (.returned vb), so2)`!
            rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out
            dsimp only at hite_out
            by_cases hgrow_cond : capw.toNat ≤ nw.toNat
            · -- GROW BRANCH: `capw.toNat = nw.toNat` (since `nw.toNat ≤ capw.toNat` by `LstOK`)
              have hn_eq_cap : nw.toNat = capw.toNat := by
                have := hlst0.2; omega
              have hnw_eq_capw : nw = capw := BitVec.eq_of_toNat_eq hn_eq_cap
              rw [if_pos hgrow_cond, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
              -- Unfold `growProg` (`decCall "np" "alloc"` followed by `memcpy`, `[l+0]:=np`, `[l+16]:=cap*2`):
              change evaluateHOLFiniteState e2
                (.decCall (ofString "np") .one (ofString "alloc")
                  [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]]
                  (.seq
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "np"),
                       .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                       .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                    (.seq
                      (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
                      (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                        (.panop .mul [.var .local (ofString "cap"), .const 2#64]))))) = (none, si) at hite_out
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hite_out
              have hev_alloc : evalListHOLFinite e2 (h := fun a => Classical.propDecidable (e2.memaddrs a))
                  [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]] =
                  some [.val (.word (eszw * capw * 2#64))] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he2_e, he2_c,
                  valueIsWord, valueWord, panOpHOL]
              have hlk_alloc := pan_one_word_lookup e2.code.lookup (ofString "alloc") (ofString "n")
                (sourceFnBody Guest.Software.guestFn_alloc) (eszw * capw * 2#64)
                (by rw [he2_AR.1.code]; exact R13Shards.lookup_alloc_r13)
              rw [hev_alloc] at hite_out; dsimp only at hite_out
              rw [hlk_alloc] at hite_out; dsimp only at hite_out
              by_cases hc_e2 : e2.clock = 0
              · rw [if_pos hc_e2] at hite_out; simp at hite_out
              · rw [if_neg hc_e2] at hite_out
                let cmap_a := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (eszw * capw * 2#64)))
                let ent_a := callEntryStateHOLFinite e2 cmap_a
                have hent_a_AR : ArenaReady ent_a := (arenaReady_with_locals e2 cmap_a (e2.clock - 1)).2 he2_AR
                have hent_a_n : locN ent_a "n" = (eszw * capw * 2#64).toNat := by
                  simp [ent_a, cmap_a, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                rcases hrun_a : evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
                have hrun_a' : evaluateHOLFiniteState (callEntryStateHOLFinite e2 cmap_a)
                    (sourceFnBody Guest.Software.guestFn_alloc) = (ra, sa) := hrun_a
                rw [hrun_a'] at hite_out
                cases ra with
                | none => simp at hite_out
                | some ra' =>
                  cases ra' with
                  | timeOut | «break» | «continue» | error | finalFfi _ | exception _ _ =>
                    simp at hite_out
                  | returned va =>
                    have hres_enta : Wave8Contracts.M12.Resumes
                        (evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc)).1 :=
                      Or.inl ⟨va, congrArg Prod.fst hrun_a⟩
                    obtain ⟨npw, qw, hrv_a, hnpw_eq, hqw_eq, hqw_lim, hqw8, hnpw_le_qw,
                      hsa_g, hsa_m, hsa_be, hsa_ma, hAsa, hsa_hp, hsa_sp⟩ :=
                      R13Shards.alloc_body_resumes_props ent_a he2_AR.1.code hent_a_AR hres_enta
                    rw [hrun_a] at hrv_a hsa_g hsa_m hsa_be hsa_ma hAsa hsa_hp hsa_sp
                    dsimp only at hrv_a hsa_g hsa_m hsa_be hsa_ma hAsa hsa_hp hsa_sp hite_out
                    injection hrv_a with hva; injection hva with hva'; subst hva'
                    rw [hent_a_n] at hqw_eq
                    have hsh_a : (shapeEqHOL (shapeOfHOLExact (.val (.word npw) : ValueHOL 64)) .one &&
                        shapeEqHOL (shapeOfHOLExact (.val (.word npw) : ValueHOL 64)) .one) = true := by
                      simp [shapeOfHOLExact, shapeEqHOL]
                    rw [if_pos hsh_a] at hite_out
                    let ma := setVarHOLFinite (ofString "np") (.val (.word npw)) { sa with locals := e2.locals }
                    have hma_AR : ArenaReady ma := (arenaReady_with_locals sa _ sa.clock).2 hAsa
                    have hma_m : ma.memory = s.memory := hsa_m
                    have hma_be : ma.be = s.be := hsa_be
                    have hma_ma : ma.memaddrs = ordinaryDomain := hsa_ma.trans hent_ma
                    have hma_code : ma.code = originalRuntimeCode := hma_AR.1.code
                    have hma_gl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = ma.globals.lookup k := by
                      intro k hk1
                      change s.globals.lookup k = sa.globals.lookup k
                      have hent_a_gl : ent_a.globals = s.globals := rfl
                      rw [hsa_g, hent_a_gl]
                      simp [HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1]
                    have hnpw_eq_s : npw.toNat = globN s "heap_ptr" := hnpw_eq
                    have hnpw8 : npw.toNat % 8 = 0 := by rw [hnpw_eq_s]; exact hAs.2.2.2.2.2.2.1
                    -- Arithmetic: `eszw * capw < 2^64` (from `hp_bnd`), and `(eszw * capw * 2#64).toNat = 2 * eszw.toNat * capw.toNat`!
                    have hmul_ec_lt : eszw.toNat * capw.toNat < 2 ^ 64 := by
                      rw [hcapw_toNat]; omega
                    have hec_bv : (eszw * capw).toNat = eszw.toNat * capw.toNat := by
                      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_ec_lt]
                    have hmul2_lt : eszw.toNat * capw.toNat * 2 < 2 ^ 64 := by
                      rw [hcapw_toNat]
                      have hhe_val : heapEnd = 33806089704 := by decide
                      omega
                    have hmul2_toNat : (eszw * capw * 2#64).toNat = 2 * eszw.toNat * capw.toNat := by
                      rw [BitVec.toNat_mul, hec_bv]
                      have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
                      rw [h2, Nat.mod_eq_of_lt hmul2_lt]
                      ring
                    have hmul2_div : (2 * eszw.toNat * capw.toNat + 7) / 8 * 8 = 2 * eszw.toNat * capw.toNat := by
                      rcases hesz with h | h | h <;> (rw [h]; omega)
                    have hma_hp : globN ma "heap_ptr" = npw.toNat + 2 * eszw.toNat * capw.toNat := by
                      change globN sa "heap_ptr" = _
                      rw [hsa_hp, hqw_eq, hmul2_toNat, hmul2_div]
                    -- Step through `memcpy` + `[l+0] := np` + `[l+16] := cap * 2` on `ma`:
                    rcases hma_cont : evaluateHOLFiniteState ma
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "np"),
                           .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                        (.seq
                          (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
                          (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                            (.panop .mul [.var .local (ofString "cap"), .const 2#64])))) with ⟨rg1, sg1⟩
                    rw [hma_cont] at hite_out
                    dsimp only at hite_out
                    injection hite_out with hrg1 hsi_eq
                    subst hrg1
                    rw [evaluateHOLFiniteState_seq_line780] at hma_cont
                    rcases hmc_out : evaluateHOLFiniteState ma
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "np"),
                         .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                         .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨rmc, smc⟩
                    rw [hmc_out] at hma_cont
                    cases rmc with
                    | some _ => dsimp only at hma_cont; simp at hma_cont
                    | none =>
                      dsimp only at hma_cont
                      have hma_np : ma.locals.lookup (ofString "np") = some (.val (.word npw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      have hma_l : ma.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "l" by decide, he2_l]
                      have hma_e : ma.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "esz" by decide, he2_e]
                      have hma_n : ma.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "n" by decide, he2_n]
                      have hma_c : ma.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "cap" by decide, he2_c]
                      have hma_dom0 : ma.memaddrs (lw + 0#64) := by rw [hma_ma, ← hent_ma]; exact hdom_l0
                      have hma_m0 : ma.memory (lw + 0#64) = .word pw0 := by rw [hma_m]; exact hm_l0
                      have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                      have hev_mc_dst : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                          (.var .local (ofString "np")) = some (.val (.word npw)) := by
                        simp [evalHOLExact, hma_np]
                      have hev_mc_src : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                          (.load .one (.op .add [.var .local (ofString "l"), .const 0#64])) =
                          some (.val (.word pw0)) := by
                        simp only [evalHOLExact, evalListHOLExact, hma_l, valueIsWord, valueWord,
                          wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                          memLoadHOLExact, isWfShapeExactHOL, hma_dom0, hma_m0, ↓reduceIte]
                      have hev_mc_n : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                          (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]) =
                          some (.val (.word (eszw * nw))) := by
                        simp [evalHOLExact, evalListHOLExact, hma_e, hma_n, valueIsWord, valueWord, panOpHOL]
                      let Rg : List Ivl := [(npw.toNat, 2 * eszw.toNat * capw.toNat), (lw.toNat, 24)]
                      have hmc_nt : (evaluateHOLFiniteState ma
                          (.call (some (none, none)) (ofString "memcpy")
                            [.var .local (ofString "np"),
                             .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                             .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])).1 ≠
                          some .timeOut := by
                        rw [hmc_out]; simp
                      have hmc_bre_all := M11.eval_call_memcpy_bre ma _ _ _ npw pw0 (eszw * nw) Rg
                        hma_code hma_ma hev_mc_dst hev_mc_src hev_mc_n
                        (fun _ => by
                          refine ⟨(npw.toNat, 2 * eszw.toNat * capw.toNat), by simp [Rg], le_refl _, ?_⟩
                          dsimp only
                          rw [hnw_eq_capw, hec_bv]
                          nlinarith)
                        hmc_nt
                      obtain ⟨heff_mc, hsmc_loc⟩ := hmc_bre_all.1 (by rw [hmc_out])
                      rw [hmc_out] at heff_mc hsmc_loc
                      dsimp only at heff_mc hsmc_loc
                      -- Now `[l+0] := np` and `[l+16] := cap * 2` on `smc`:
                      rw [evaluateHOLFiniteState_seq_line780] at hma_cont
                      rcases hst0_out : evaluateHOLFiniteState smc
                        (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) with ⟨rst0, sst0⟩
                      rw [hst0_out] at hma_cont
                      cases rst0 with
                      | some _ => dsimp only at hma_cont; simp at hma_cont
                      | none =>
                        dsimp only at hma_cont
                        have hsmc_ma : smc.memaddrs = ordinaryDomain := heff_mc.memaddrs.trans hma_ma
                        have hsmc_l : smc.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                          rw [hsmc_loc]; exact hma_l
                        have hsmc_np : smc.locals.lookup (ofString "np") = some (.val (.word npw)) := by
                          rw [hsmc_loc]; exact hma_np
                        have hsmc_dom0 : smc.memaddrs (lw + 0#64) := by rw [hsmc_ma, ← hent_ma]; exact hdom_l0
                        have hsmc_dom0' : smc.memaddrs lw := by simpa using hsmc_dom0
                        have hev_st0_d : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                            (.op .add [.var .local (ofString "l"), .const 0#64]) =
                            some (.val (.word (lw + 0#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsmc_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                        have hev_st0_v : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                            (.var .local (ofString "np")) = some (.val (.word npw)) := by
                          simp [evalHOLExact, hsmc_np]
                        have hst0_eq : evaluateHOLFiniteState smc
                            (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) =
                            (none, { smc with memory := fun a => if a = lw + 0#64 then .word npw else smc.memory a }) := by
                          rw [evaluateHOLFiniteState_store, hev_st0_d, hev_st0_v]; dsimp only
                          simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsmc_dom0', FUPDATE]
                        obtain ⟨heff_st0, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsmc_ma hst0_out
                          (fun v hv => by rw [hev_st0_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                          (fun addr hdst _ => by
                            rw [hev_st0_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                            subst hd3
                            have : (lw + 0#64).toNat = lw.toNat := by simp
                            exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                        have hsst0_eq : sst0 = { smc with memory := fun a => if a = lw + 0#64 then .word npw else smc.memory a } := by
                          rw [hst0_out] at hst0_eq; exact (Prod.mk.inj hst0_eq).2
                        have hsst0_ma : sst0.memaddrs = ordinaryDomain := heff_st0.memaddrs.trans hsmc_ma
                        have hsst0_loc : sst0.locals = ma.locals := by rw [hsst0_eq]; exact hsmc_loc
                        have hsst0_l : sst0.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                          rw [hsst0_loc]; exact hma_l
                        have hsst0_c : sst0.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                          rw [hsst0_loc]; exact hma_c
                        have hsst0_dom16 : sst0.memaddrs (lw + 16#64) := by rw [hsst0_ma, ← hent_ma]; exact hdom_l16
                        have hev_st16_d : @evalHOLExact 64 F _ sst0.toExact (fun a => Classical.propDecidable (sst0.memaddrs a))
                            (.op .add [.var .local (ofString "l"), .const 16#64]) =
                            some (.val (.word (lw + 16#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsst0_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                        have hev_st16_v : @evalHOLExact 64 F _ sst0.toExact (fun a => Classical.propDecidable (sst0.memaddrs a))
                            (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
                            some (.val (.word (capw * 2#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsst0_c, valueIsWord, valueWord, panOpHOL]
                        have hst16_eq : evaluateHOLFiniteState sst0
                            (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                              (.panop .mul [.var .local (ofString "cap"), .const 2#64])) =
                            (none, { sst0 with memory := fun a => if a = lw + 16#64 then .word (capw * 2#64) else sst0.memory a }) := by
                          rw [evaluateHOLFiniteState_store, hev_st16_d, hev_st16_v]; dsimp only
                          simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsst0_dom16, FUPDATE]
                        obtain ⟨heff_st16, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsst0_ma hma_cont
                          (fun v hv => by rw [hev_st16_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                          (fun addr hdst _ => by
                            rw [hev_st16_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                            subst hd3
                            exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                        have hsg1_eq : sg1 = { sst0 with memory := fun a => if a = lw + 16#64 then .word (capw * 2#64) else sst0.memory a } := by
                          rw [hma_cont] at hst16_eq; exact (Prod.mk.inj hst16_eq).2
                        -- Now step `tailProg` (`[l+8] := n + 1; return [l+0] + n * esz`) on `si`!
                        have hsi_ma : si.memaddrs = ordinaryDomain := by
                          rw [← hsi_eq]; exact heff_st16.memaddrs.trans hsst0_ma
                        have hsi_l : si.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                          rw [← hsi_eq]; dsimp only
                          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq]; exact hsst0_l
                        have hsi_n : si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                          rw [← hsi_eq]; dsimp only
                          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_loc]; exact hma_n
                        have hsi_e : si.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
                          rw [← hsi_eq]; dsimp only
                          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_loc]; exact hma_e
                        have hsi_dom8 : si.memaddrs (lw + 8#64) := by rw [hsi_ma, ← hent_ma]; exact hdom_l8
                        have hsi_dom0 : si.memaddrs (lw + 0#64) := by rw [hsi_ma, ← hent_ma]; exact hdom_l0
                        dsimp only [tailProg] at hout_e2
                        rw [evaluateHOLFiniteState_seq_line780] at hout_e2
                        have hev_st8_d : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                            (.op .add [.var .local (ofString "l"), .const 8#64]) =
                            some (.val (.word (lw + 8#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsi_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                        have hev_st8_v : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                            (.op .add [.var .local (ofString "n"), .const 1#64]) =
                            some (.val (.word (nw + 1#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsi_n, valueIsWord, valueWord, wordOpHOL, wordOp]
                        have hst8_eq : evaluateHOLFiniteState si
                            (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                              (.op .add [.var .local (ofString "n"), .const 1#64])) =
                            (none, { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }) := by
                          rw [evaluateHOLFiniteState_store, hev_st8_d, hev_st8_v]; dsimp only
                          simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsi_dom8, FUPDATE]
                        rw [hst8_eq] at hout_e2
                        dsimp only at hout_e2
                        obtain ⟨heff_st8, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsi_ma hst8_eq
                          (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                          (fun addr hdst _ => by
                            rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                            subst hd3
                            exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                        let st8 : PanSemStateFiniteExact 64 F :=
                          { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }
                        have hne_0_16 : lw + 0#64 ≠ lw + 16#64 := by
                          intro h; have := congrArg BitVec.toNat h
                          have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                          omega
                        have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := by
                          intro h; have := congrArg BitVec.toNat h
                          have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                          omega
                        have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := by
                          intro h; have := congrArg BitVec.toNat h; omega
                        have hst8_m0 : st8.memory (lw + 0#64) = .word npw := by
                          dsimp [st8]; rw [if_neg hne_0_8, ← hsi_eq]; dsimp only
                          rw [hsg1_eq]; dsimp only; rw [if_neg hne_0_16, hsst0_eq]; simp
                        have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by
                          dsimp [st8]; simp
                        have hst8_m16 : st8.memory (lw + 16#64) = .word (capw * 2#64) := by
                          dsimp [st8]; rw [if_neg hne_16_8, ← hsi_eq]; dsimp only
                          rw [hsg1_eq]; simp
                        have hst8_dom0 : st8.memaddrs (lw + 0#64) := hsi_dom0
                        have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
                            (.op .add
                              [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                               .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
                            some (.val (.word (npw + nw * eszw))) := by
                          have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                          have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := hsi_l
                          have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := hsi_n
                          have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word eszw)) := hsi_e
                          simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
                            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                            List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                            memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
                          simp
                        rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2
                        dsimp only at hout_e2
                        rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])] at hout_e2
                        injection hout_e2 with hvb_eq hso2_eq
                        injection hvb_eq with hvb_ret
                        injection hvb_ret with hvb_val
                        subst hvb_val
                        let ew := npw + nw * eszw
                        have hsh_ew : (shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one &&
                            shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one) = true := by
                          simp [shapeOfHOLExact, shapeEqHOL]
                        dsimp only at hnt hres
                        rw [if_pos hsh_ew] at hnt hres
                        let mid := setVarHOLFinite x (.val (.word ew)) { sb with locals := s.locals }
                        -- Total `ByteRegionEffect ma mid Rg`:
                        have heff_si : M11.ByteRegionEffect ma si Rg := by
                          rw [← hsi_eq]
                          exact ((heff_mc.trans heff_st0).trans heff_st16).with_locals_clock _ sg1.clock
                        have heff_mid : M11.ByteRegionEffect ma mid Rg := by
                          have hmid_mem : mid = { st8 with locals := mid.locals, clock := mid.clock } := by
                            dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                          rw [hmid_mem]
                          exact (heff_si.trans heff_st8).with_locals_clock mid.locals mid.clock
                        have hmid_m0 : memW mid lw.toNat = npw.toNat := by
                          unfold memW; rw [← hl0_bv]
                          have hm_eq : mid.memory = st8.memory := by
                            dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                          rw [hm_eq, hst8_m0]
                        have hcap2_toNat : (capw * 2#64).toNat = 2 * capw.toNat := by
                          have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
                          have hc2_lt : capw.toNat * 2 < 2 ^ 64 := by
                            have : capw.toNat * 2 ≤ eszw.toNat * capw.toNat * 2 := by
                              have := Nat.mul_le_mul_right capw.toNat (show 1 ≤ eszw.toNat by omega)
                              omega
                            omega
                          rw [BitVec.toNat_mul, h2, Nat.mod_eq_of_lt hc2_lt]; omega
                        have hnp1_toNat : (nw + 1#64).toNat = nw.toNat + 1 := by
                          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                          have hn1_lt : nw.toNat + 1 < 2 ^ 64 := by omega
                          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hn1_lt]
                        have hmid_m8 : memW mid (lw.toNat + 8) = nw.toNat + 1 := by
                          unfold memW; rw [← hl8_bv]
                          have hm_eq : mid.memory = st8.memory := by
                            dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                          rw [hm_eq, hst8_m8]; exact hnp1_toNat
                        have hmid_m16 : memW mid (lw.toNat + 16) = 2 * capw.toNat := by
                          unfold memW; rw [← hl16_bv]
                          have hm_eq : mid.memory = st8.memory := by
                            dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                          rw [hm_eq, hst8_m16]; exact hcap2_toNat
                        have hcap_pos0 : 1 ≤ capw.toNat := by rw [hcapw_toNat]; exact hlst0.1
                        have hws_mid : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
                          bal_list_grow_worldStep hW hlw_nz_nat hesz (horig_nz hlw0) hcapw_toNat.symm
                            hma_AR hma_m hma_be hma_gl hnpw_eq_s hma_hp heff_mid
                            hmid_m0 (by rw [hmid_m8, hn_eq_cap]; omega) hmid_m16
                        have hW_mid : WorldOK mid := worldOK_of_step hW hws_mid
                        have horig_mid : ∀ S' Nd', WorldTypedWith mid S' Nd' →
                            LstOK mid lw.toNat ∧ BalListOrigin mid lw.toNat eszw.toNat := by
                          intro S' Nd' hWT_m
                          -- Wait: `balListOrigin_preserved_of_grow` took `hWT : WorldTypedWith s0 S Nd`!
                          -- Is `BalListOrigin mid lw.toNat eszw.toNat` independent of `(S', Nd')`?
                          -- LOOK AT `BalListOrigin`: `BalListOrigin mid l esz` depends ONLY on `mid` (`balRecords mid`, `memW mid`, `htabValues mid`) — NOT on `S'` or `Nd'`!!
                          -- And `LstOK mid lw.toNat` ALSO depends ONLY on `mid` (`1 ≤ memW mid (l+16) ∧ memW mid (l+8) ≤ memW mid (l+16)`)!
                          refine ⟨⟨by rw [hmid_m16]; omega, by rw [hmid_m8, hmid_m16, hn_eq_cap]; omega⟩, ?_⟩
                          exact balListOrigin_preserved_of_grow hW hlw_nz_nat hesz (horig_nz hlw0)
                            hma_AR hma_m hma_gl hnpw_eq_s hma_hp heff_mid S0 Nd0 hWT0
                        -- Check `ew` bounds & alignment:
                        have hne_mul_toNat : (nw * eszw).toNat = nw.toNat * eszw.toNat := by
                          rw [BitVec.toNat_mul, hn_eq_cap, Nat.mul_comm, Nat.mod_eq_of_lt hmul_ec_lt]
                        have hnpw_hi_lim : npw.toNat + 2 * eszw.toNat * capw.toNat ≤ heapLimit := by
                          rw [← hma_hp]; exact hma_AR.2.2.1
                        have hce2_eq : capw.toNat * eszw.toNat + eszw.toNat ≤ 2 * eszw.toNat * capw.toNat := by
                          have hc1 : 1 ≤ capw.toNat := hcap_pos0
                          nlinarith
                        have hew_toNat : ew.toNat = npw.toNat + nw.toNat * eszw.toNat := by
                          change (npw + nw * eszw).toNat = _
                          rw [BitVec.toNat_add, hne_mul_toNat, Nat.mod_eq_of_lt (by rw [hn_eq_cap]; omega)]
                        have hew8 : ew.toNat % 8 = 0 := by
                          rw [hew_toNat]
                          have hmul8 : nw.toNat * eszw.toNat % 8 = 0 := by
                            rcases hesz with h | h | h <;> (rw [h]; omega)
                          omega
                        have hew_sb : sourceBase ≤ ew.toNat := by
                          rw [hew_toNat, hnpw_eq_s]; have := hAs.2.1; omega
                        have hew_he : ew.toNat + eszw.toNat ≤ heapEnd := by
                          rw [hew_toNat, hn_eq_cap]; omega
                        have hew_lo : memW mid lw.toNat ≤ ew.toNat := by
                          rw [hmid_m0, hew_toNat]; omega
                        have hew_hi : ew.toNat + eszw.toNat ≤
                            memW mid lw.toNat + eszw.toNat * memW mid (lw.toNat + 16) := by
                          rw [hmid_m0, hmid_m16, hew_toNat, hn_eq_cap]; nlinarith
                        have heval_eq : evaluateHOLFiniteState s
                            (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont) =
                            ((evaluateHOLFiniteState mid cont).1,
                              { (evaluateHOLFiniteState mid cont).2 with
                                locals := HolFiniteMapExact.resVarEq
                                  (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
                          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
                          dsimp only; rw [hlk]; dsimp only
                          rw [if_neg hcz, hrun']; dsimp only
                          rw [if_pos hsh_ew]
                        refine ⟨ew, mid, hlw0, hws_mid, hW_mid, horig_mid, hew8, hew_sb, hew_he,
                          hew_lo, hew_hi,
                          by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
                          fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
                          by intro hto; rw [hto] at hnt; exact hnt rfl,
                          hres, by rw [heval_eq], by rw [heval_eq]⟩
            · -- NO-GROW BRANCH (`nw.toNat < capw.toNat`):
              have hn_lt_cap : nw.toNat < capw.toNat := by omega
              rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
              injection hite_out with _ hsi_eq
              subst hsi_eq
              -- Step `tailProg` (`[l+8] := n + 1; return [l+0] + n * esz`) directly on `e2`:
              let Rn : List Ivl := [(lw.toNat + 8, 8), (memW s lw.toNat, eszw.toNat * memW s (lw.toNat + 16))]
              have he2_ma : e2.memaddrs = ordinaryDomain := hent_ma
              have he2_dom8 : e2.memaddrs (lw + 8#64) := hdom_l8
              have he2_dom0 : e2.memaddrs (lw + 0#64) := hdom_l0
              dsimp only [tailProg] at hout_e2
              rw [evaluateHOLFiniteState_seq_line780] at hout_e2
              have hev_st8_d : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
                  (.op .add [.var .local (ofString "l"), .const 8#64]) =
                  some (.val (.word (lw + 8#64))) := by
                simp [evalHOLExact, evalListHOLExact, he2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
              have hev_st8_v : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
                  (.op .add [.var .local (ofString "n"), .const 1#64]) =
                  some (.val (.word (nw + 1#64))) := by
                simp [evalHOLExact, evalListHOLExact, he2_n, valueIsWord, valueWord, wordOpHOL, wordOp]
              have hst8_eq : evaluateHOLFiniteState e2
                  (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                    (.op .add [.var .local (ofString "n"), .const 1#64])) =
                  (none, { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }) := by
                rw [evaluateHOLFiniteState_store, hev_st8_d, hev_st8_v]; dsimp only
                simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, he2_dom8, FUPDATE]
              rw [hst8_eq] at hout_e2
              dsimp only at hout_e2
              obtain ⟨heff_st8, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rn) he2_ma hst8_eq
                (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                (fun addr hdst _ => by
                  rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                  subst hd3
                  exact ⟨(lw.toNat + 8, 8), by simp [Rn], by dsimp only; omega, by dsimp only; omega⟩)
              let st8 : PanSemStateFiniteExact 64 F :=
                { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }
              have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := by
                intro h; have := congrArg BitVec.toNat h
                have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                omega
              have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := by
                intro h; have := congrArg BitVec.toNat h; omega
              have hst8_m0 : st8.memory (lw + 0#64) = .word pw0 := by
                dsimp [st8]; rw [if_neg hne_0_8]; exact hm_l0
              have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by
                dsimp [st8]; simp
              have hst8_m16 : st8.memory (lw + 16#64) = .word capw := by
                dsimp [st8]; rw [if_neg hne_16_8]; exact hm_l16
              have hst8_dom0 : st8.memaddrs (lw + 0#64) := he2_dom0
              have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
                  (.op .add
                    [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                     .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
                  some (.val (.word (pw0 + nw * eszw))) := by
                have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := he2_l
                have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := he2_n
                have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word eszw)) := he2_e
                simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
                  valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                  List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                  memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
                simp
              rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2
              dsimp only at hout_e2
              rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])] at hout_e2
              injection hout_e2 with hvb_eq hso2_eq
              injection hvb_eq with hvb_ret
              injection hvb_ret with hvb_val
              subst hvb_val
              let ew := pw0 + nw * eszw
              have hsh_ew : (shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one &&
                  shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one) = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              dsimp only at hnt hres
              rw [if_pos hsh_ew] at hnt hres
              let mid := setVarHOLFinite x (.val (.word ew)) { sb with locals := s.locals }
              have heff_e2_mid : M11.ByteRegionEffect e2 mid Rn := by
                have hmid_mem : mid = { st8 with locals := mid.locals, clock := mid.clock } := by
                  dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                rw [hmid_mem]
                exact heff_st8.with_locals_clock mid.locals mid.clock
              have heff_s_e2 : M11.ByteRegionEffect s e2 Rn := by
                rw [he2_eq]
                exact (M11.ByteRegionEffect.refl s Rn).with_locals_clock e2.locals (s.clock - 1)
              have heff_mid : M11.ByteRegionEffect s mid Rn := heff_s_e2.trans heff_e2_mid
              have hnp1_toNat : (nw + 1#64).toNat = nw.toNat + 1 := by
                have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                have hn1_lt : nw.toNat + 1 < 2 ^ 64 := by omega
                rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hn1_lt]
              have hmid_m0 : memW mid lw.toNat = pw0.toNat := by
                unfold memW; rw [← hl0_bv]
                have hm_eq : mid.memory = st8.memory := by
                  dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                rw [hm_eq, hst8_m0]
              have hmid_m8 : memW mid (lw.toNat + 8) = nw.toNat + 1 := by
                unfold memW; rw [← hl8_bv]
                have hm_eq : mid.memory = st8.memory := by
                  dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                rw [hm_eq, hst8_m8]; exact hnp1_toNat
              have hmid_m16 : memW mid (lw.toNat + 16) = capw.toNat := by
                unfold memW; rw [← hl16_bv]
                have hm_eq : mid.memory = st8.memory := by
                  dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                rw [hm_eq, hst8_m16]
              have hslice_s : ∀ S Nd, WorldTypedWith s S Nd → LstOK s lw.toNat ∧ BalListSlice s lw.toNat eszw.toNat :=
                fun S Nd h => ⟨(horig_nz hlw0 S Nd h).1, balListOrigin_slice (horig_nz hlw0 S Nd h).2⟩
              have hws_nil : WorldStep (fun _ => []) [] stdKeep NoExtra s none mid :=
                bal_list_store_len_and_arr_worldStep hW hlw_nz_nat hesz hslice_s heff_mid
                  (by rw [← hcapw_toNat]; omega) hmid_m8
              have hws_mid : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
                worldStep_nil_to_hp hws_nil
              have hW_mid : WorldOK mid := worldOK_of_step hW hws_mid
              have horig_mid : ∀ S' Nd', WorldTypedWith mid S' Nd' →
                  LstOK mid lw.toNat ∧ BalListOrigin mid lw.toNat eszw.toNat := by
                intro _ _ _
                refine ⟨⟨by rw [hmid_m16, hcapw_toNat]; exact hlst0.1,
                  by rw [hmid_m8, hmid_m16]; omega⟩, ?_⟩
                exact balListOrigin_preserved_of_nogrow hW hlw_nz_nat hesz (horig_nz hlw0)
                  heff_mid S0 Nd0 hWT0
              have hne_mul_lt : nw.toNat * eszw.toNat < eszw.toNat * memW s (lw.toNat + 16) := by
                rw [Nat.mul_comm]; exact Nat.mul_lt_mul_of_pos_left (by rw [← hcapw_toNat]; exact hn_lt_cap) hesz_pos
              have hne_mul_toNat : (nw * eszw).toNat = nw.toNat * eszw.toNat := by
                rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
              have hew_hi_arr : pw0.toNat + nw.toNat * eszw.toNat + eszw.toNat ≤
                  memW s lw.toNat + eszw.toNat * memW s (lw.toNat + 16) := by
                rw [hpw0_toNat]
                have hle1 : nw.toNat + 1 ≤ memW s (lw.toNat + 16) := by rw [← hcapw_toNat]; omega
                have hmul1 : eszw.toNat * (nw.toNat + 1) ≤ eszw.toNat * memW s (lw.toNat + 16) :=
                  Nat.mul_le_mul_left _ hle1
                nlinarith
              have hew_toNat : ew.toNat = pw0.toNat + nw.toNat * eszw.toNat := by
                change (pw0 + nw * eszw).toNat = _
                rw [BitVec.toNat_add, hne_mul_toNat, Nat.mod_eq_of_lt (by rw [hpw0_toNat]; omega)]
              have hew8 : ew.toNat % 8 = 0 := by
                rw [hew_toNat, hpw0_toNat]
                have hp8 : memW s lw.toNat % 8 = 0 := hw_p.1
                have hmul8 : nw.toNat * eszw.toNat % 8 = 0 := by
                  rcases hesz with h | h | h <;> (rw [h]; omega)
                omega
              have hew_sb : sourceBase ≤ ew.toNat := by
                rw [hew_toNat, hpw0_toNat]; omega
              have hew_he : ew.toNat + eszw.toNat ≤ heapEnd := by
                rw [hew_toNat]; omega
              have hew_lo : memW mid lw.toNat ≤ ew.toNat := by
                rw [hmid_m0, hew_toNat]; omega
              have hew_hi : ew.toNat + eszw.toNat ≤
                  memW mid lw.toNat + eszw.toNat * memW mid (lw.toNat + 16) := by
                rw [hmid_m0, hmid_m16, hcapw_toNat, hew_toNat, hpw0_toNat]
                rw [hpw0_toNat] at hew_hi_arr; exact hew_hi_arr
              have heval_eq : evaluateHOLFiniteState s
                  (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont) =
                  ((evaluateHOLFiniteState mid cont).1,
                    { (evaluateHOLFiniteState mid cont).2 with
                      locals := HolFiniteMapExact.resVarEq
                        (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
                dsimp only; rw [hlk]; dsimp only
                rw [if_neg hcz, hrun']; dsimp only
                rw [if_pos hsh_ew]
              refine ⟨ew, mid, hlw0, hws_mid, hW_mid, horig_mid, hew8, hew_sb, hew_he,
                hew_lo, hew_hi,
                by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
                fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
                by intro hto; rw [hto] at hnt; exact hnt rfl,
                hres, by rw [heval_eq], by rw [heval_eq]⟩

private theorem bal_list_store_arr_worldStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l esz : Nat}
    (hW : WorldOK s)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (horig_all : ∀ S Nd, WorldTypedWith s S Nd → LstOK s l ∧ BalListOrigin s l esz)
    (heff : M11.ByteRegionEffect s post [(memW s l, esz * memW s (l + 16))]) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r post ∧
    WorldOK post ∧
    (∀ S Nd, WorldTypedWith post S Nd → LstOK post l ∧ BalListOrigin post l esz) := by
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨hlst, horig⟩ := horig_all S0 Nd0 hWT0
  obtain ⟨hl_fix, hp_fix, hdj, _, _, _⟩ :=
    bal_list_slice_props hWT0.2.2.1 hl_nz hesz hlst (balListOrigin_slice horig)
  have hl_hi : l + 24 ≤ 2 ^ 64 := by
    rcases hWT0.2.2.1.1 _ hl_fix with h0 | ⟨hal, _⟩
    · simp at h0
    · exact (ivl_allocated_bound hW.1.2 hal).2
  have hl8 : l % 8 = 0 := by
    rcases hWT0.2.2.1.1 _ hl_fix with h0 | ⟨_, hw⟩
    · simp at h0
    · exact hw.1
  have hu : M08IvlUnhit s post (l, 24) := by
    intro a ha8 ha1 ha2
    apply heff.cell_frame a
    intro i hi hc
    have hi_eq := List.mem_singleton.1 hi
    subst i
    have hp8 : memW s l % 8 = 0 := by
      rcases hWT0.2.2.1.1 _ hp_fix with h0 | ⟨_, hw⟩
      · have hp : 0 < esz * memW s (l + 16) := by
          have he : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
          exact Nat.mul_pos he (by have := hlst.1; omega)
        omega
      · exact hw.1
    exact not_cellHits_of_disj ha8 hp8 ⟨ha1, ha2⟩ hdj hc
  have hm8 : memW post (l + 8) = memW s (l + 8) :=
    memW_eq_of_ivlUnhit hu (by omega) hl_hi ⟨by omega, by omega⟩
  have hm16 : memW post (l + 16) = memW s (l + 16) :=
    memW_eq_of_ivlUnhit hu (by omega) hl_hi ⟨by omega, by omega⟩
  have heff' : M11.ByteRegionEffect s post
      [(l + 8, 8), (memW s l, esz * memW s (l + 16))] :=
    heff.mono (by
      intro i hi
      exact ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩)
  have hstep : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r post :=
    worldStep_nil_to_hp (bal_list_store_len_and_arr_worldStep hW hl_nz hesz
      (fun S Nd h => ⟨(horig_all S Nd h).1, balListOrigin_slice (horig_all S Nd h).2⟩)
      heff' hlst.2 hm8)
  refine ⟨hstep, worldOK_of_step hW hstep, fun _ _ _ => ⟨?_, ?_⟩⟩
  · exact ⟨by rw [hm16]; exact hlst.1, by rw [hm8, hm16]; exact hlst.2⟩
  · exact balListOrigin_preserved_of_nogrow hW hl_nz hesz horig_all heff' S0 Nd0 hWT0

/-! ## 4. `lst_upsert_idx` loop and `decCall` stepper -/

private def lstUpsertLoopBody : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal
        (.load .one (.op .add [.var .local (ofString "p"),
          .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
        (.var .local (ofString "idx")))
      (.return (.op .add [.var .local (ofString "p"),
        .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
      .skip)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))

private def lstUpsertLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) lstUpsertLoopBody

private theorem lst_upsert_loop_eval {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (lw nw pw eszw idxw : BitVec 64)
    (hcode0 : s0.code = originalRuntimeCode)
    (hma0 : s0.memaddrs = ordinaryDomain)
    (hesz : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40)
    (hlst : LstOK s0 lw.toNat)
    (hp_al : pw.toNat % 8 = 0 ∧ sourceBase ≤ pw.toNat ∧
      pw.toNat + eszw.toNat * memW s0 (lw.toNat + 16) ≤ heapEnd)
    (hn_eq : nw.toNat = memW s0 (lw.toNat + 8)) :
    ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F) (iw : BitVec 64),
      t.clock = k →
      t = { s0 with locals := t.locals, clock := k } →
      iw.toNat ≤ nw.toNat →
      t.locals.lookup (ofString "n") = some (.val (.word nw)) →
      t.locals.lookup (ofString "p") = some (.val (.word pw)) →
      t.locals.lookup (ofString "esz") = some (.val (.word eszw)) →
      t.locals.lookup (ofString "idx") = some (.val (.word idxw)) →
      t.locals.lookup (ofString "i") = some (.val (.word iw)) →
      (evaluateHOLFiniteState t lstUpsertLoop).1 ≠ some .timeOut →
        ((evaluateHOLFiniteState t lstUpsertLoop).1 = none →
          (evaluateHOLFiniteState t lstUpsertLoop).2 =
            { s0 with locals := (evaluateHOLFiniteState t lstUpsertLoop).2.locals,
                      clock := (evaluateHOLFiniteState t lstUpsertLoop).2.clock } ∧
          (∀ y, y ≠ ofString "i" →
            (evaluateHOLFiniteState t lstUpsertLoop).2.locals.lookup y = t.locals.lookup y)) ∧
        (∀ rv, (evaluateHOLFiniteState t lstUpsertLoop).1 = some (.returned rv) →
          ∃ ew : BitVec 64, rv = .val (.word ew) ∧
            ew.toNat % 8 = 0 ∧
            sourceBase ≤ ew.toNat ∧
            ew.toNat + eszw.toNat ≤ heapEnd ∧
            pw.toNat ≤ ew.toNat ∧
            ew.toNat + eszw.toNat ≤ pw.toNat + eszw.toNat * memW s0 (lw.toNat + 16) ∧
            (evaluateHOLFiniteState t lstUpsertLoop).2 =
              { s0 with locals := HolFiniteMapExact.empty,
                        clock := (evaluateHOLFiniteState t lstUpsertLoop).2.clock }) ∧
        (∀ r, (evaluateHOLFiniteState t lstUpsertLoop).1 = some r →
          (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hhe_263 : heapEnd < 2 ^ 63 := by decide
  have hhe_264 : heapEnd ≤ 2 ^ 64 := by decide
  have hesz_pos : 0 < eszw.toNat := by rcases hesz with h | h | h <;> omega
  have hcap_lt : memW s0 (lw.toNat + 16) < 2 ^ 63 := by
    have : 1 * memW s0 (lw.toNat + 16) ≤ eszw.toNat * memW s0 (lw.toNat + 16) :=
      Nat.mul_le_mul_right _ hesz_pos
    omega
  have hlst2 := hlst.2
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t iw hclk ht_eq hi_le_n h_n h_p h_esz h_idx h_i hnt
    have ht_ma : t.memaddrs = ordinaryDomain := by rw [ht_eq]; exact hma0
    dsimp only [lstUpsertLoop] at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hcond : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, h_i, h_n, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : iw.toNat < nw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hi_lt_n : iw.toNat < nw.toNat
    · rw [if_pos hi_lt_n] at hnt ⊢
      have h1nz : (1#64 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h1nz] at hnt ⊢
      by_cases hk0 : t.clock = 0
      · rw [if_pos hk0] at hnt; exact absurd rfl hnt
      · rw [if_neg hk0] at hnt ⊢
        let td := decClockHOLFinite t
        have htd_eq : td = { s0 with locals := t.locals, clock := k - 1 } := by
          change decClockHOLFinite t = _; rw [ht_eq]; rfl
        have htd_ma : td.memaddrs = ordinaryDomain := by rw [htd_eq]; exact hma0
        have hmul_ie : (iw * eszw).toNat = iw.toNat * eszw.toNat := by
          rw [BitVec.toNat_mul]
          have : iw.toNat * eszw.toNat ≤ eszw.toNat * memW s0 (lw.toNat + 16) := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
          exact Nat.mod_eq_of_lt (by omega)
        have haddr_i : (pw + iw * eszw).toNat = pw.toNat + iw.toNat * eszw.toNat := by
          rw [BitVec.toNat_add, hmul_ie]
          have : iw.toNat * eszw.toNat ≤ eszw.toNat * memW s0 (lw.toNat + 16) := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
          exact Nat.mod_eq_of_lt (by omega)
        have hmul8 : (iw.toNat * eszw.toNat) % 8 = 0 := by
          rcases hesz with h | h | h <;> (rw [h]; omega)
        have hal_i : (pw + iw * eszw).toNat % 8 = 0 := by
          rw [haddr_i]; have := hp_al.1; omega
        have hi_hi : pw.toNat + iw.toNat * eszw.toNat + eszw.toNat ≤
            pw.toNat + eszw.toNat * memW s0 (lw.toNat + 16) := by
          have h1 : (iw.toNat + 1) * eszw.toNat ≤ memW s0 (lw.toNat + 16) * eszw.toNat :=
            Nat.mul_le_mul_right _ (by omega)
          nlinarith
        have hdom_i : td.memaddrs (pw + iw * eszw) := by
          rw [htd_ma, Wave8Contracts.M08.ordinaryDomain_iff]
          exact ⟨hal_i, by rw [haddr_i]; omega, by rw [haddr_i]; omega⟩
        obtain ⟨cw, hcw⟩ : ∃ cw, td.memory (pw + iw * eszw) = .word cw := by
          cases td.memory (pw + iw * eszw) with | word cw => exact ⟨cw, rfl⟩
        have hl_p : td.locals.lookup (ofString "p") = some (.val (.word pw)) := h_p
        have hl_i : td.locals.lookup (ofString "i") = some (.val (.word iw)) := h_i
        have hl_e : td.locals.lookup (ofString "esz") = some (.val (.word eszw)) := h_esz
        have hl_x : td.locals.lookup (ofString "idx") = some (.val (.word idxw)) := h_idx
        have hz_ie : iw * eszw + 0 = iw * eszw := BitVec.add_zero _
        have hev_addr : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
            (.op .add [.var .local (ofString "p"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]) =
            some (.val (.word (pw + iw * eszw))) := by
          simp only [evalHOLExact, evalListHOLExact, hl_p, hl_i, hl_e,
            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, hz_ie]
        have hev_cmp : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
            (.cmp .equal (.load .one (.op .add [.var .local (ofString "p"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
              (.var .local (ofString "idx"))) =
            some (.val (.word (if cw = idxw then 1#64 else 0#64))) := by
          simp only [evalHOLExact, evalListHOLExact, hl_p, hl_i, hl_e, hl_x,
            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
            memLoadHOLExact, isWfShapeExactHOL, List.all, List.map, Option.map,
            Bool.and_self, List.foldr, hz_ie, hdom_i, hcw, ↓reduceIte,
            Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq]
          by_cases hci : cw = idxw <;> simp [hci]
        have hbody_unfold := evaluateHOLFiniteState_seq_line780 td
          (.ite (.cmp .equal
              (.load .one (.op .add [.var .local (ofString "p"),
                .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
              (.var .local (ofString "idx")))
            (.return (.op .add [.var .local (ofString "p"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
        by_cases hmatch : cw = idxw
        · have hite1 : evaluateHOLFiniteState td
              (.ite (.cmp .equal
                  (.load .one (.op .add [.var .local (ofString "p"),
                    .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                  (.var .local (ofString "idx")))
                (.return (.op .add [.var .local (ofString "p"),
                  .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                .skip) =
              (some (.returned (.val (.word (pw + iw * eszw)))), emptyLocalsHOLFinite td) := by
            rw [evaluateHOLFiniteState_ite, hev_cmp, if_pos hmatch]
            dsimp only
            have h0ne : (1#64 : BitVec 64) ≠ 0 := by decide
            rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)]
            rw [evaluateHOLFiniteState_return, hev_addr]; dsimp only
            rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])]
          have hbody_ret : evaluateHOLFiniteState td lstUpsertLoopBody =
              (some (.returned (.val (.word (pw + iw * eszw)))), emptyLocalsHOLFinite td) := by
            dsimp only [lstUpsertLoopBody]; rw [hbody_unfold, hite1]
          rw [show t.decClockHOLFinite = td from rfl, hbody_ret]
          dsimp only
          refine ⟨fun h => by simp at h, fun rv hrv => ?_, fun r hr hne => ?_⟩
          · injection hrv with hrv'; injection hrv' with hrv''; subst hrv''
            refine ⟨pw + iw * eszw, rfl, hal_i, by rw [haddr_i]; omega, by rw [haddr_i]; omega,
              by rw [haddr_i]; omega, by rw [haddr_i]; exact hi_hi, ?_⟩
            simp only [emptyLocalsHOLFinite]; rw [htd_eq]; rfl
          · injection hr with hr'; subst hr'; exact absurd rfl (hne _)
        · have hite0 : evaluateHOLFiniteState td
              (.ite (.cmp .equal
                  (.load .one (.op .add [.var .local (ofString "p"),
                    .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                  (.var .local (ofString "idx")))
                (.return (.op .add [.var .local (ofString "p"),
                  .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                .skip) = (none, td) := by
            rw [evaluateHOLFiniteState_ite, hev_cmp, if_neg hmatch]
            dsimp only
            rw [if_pos (by decide : (0#64 : BitVec 64) = 0)]
            exact evaluateHOLFiniteState_skip td
          have hasgn : evaluateHOLFiniteState td
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td) := by
            rw [evaluateHOLFiniteState_assign]
            have hz_1 : (1#64 : BitVec 64) + 0 = 1#64 := BitVec.add_zero _
            have hev_add : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
                (.op .add [.var .local (ofString "i"), .const 1#64]) =
                some (.val (.word (iw + 1#64))) := by
              simp only [evalHOLExact, evalListHOLExact, hl_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
                List.foldr, hz_1]
            rw [hev_add]; dsimp only
            have hval_i : isValidValueHOLFinite td .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
              simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hl_i, shapeEqHOL, shapeOfHOLExact]
            rw [if_pos hval_i]; rfl
          have hbody_step : evaluateHOLFiniteState td lstUpsertLoopBody =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td) := by
            dsimp only [lstUpsertLoopBody]; rw [hbody_unfold, hite0]; exact hasgn
          rw [show t.decClockHOLFinite = td from rfl, hbody_step] at hnt ⊢; dsimp only at hnt ⊢
          let t' : PanSemStateFiniteExact 64 F :=
            setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td
          have ht'_clk : t'.clock < k := by
            simp [t', setVarHOLFinite, td, decClockHOLFinite, hclk]; omega
          have ht'_eq : t' = { s0 with locals := t'.locals, clock := t'.clock } := by
            simp [t', setVarHOLFinite, htd_eq]
          have hiw1_le : (iw + 1#64).toNat ≤ nw.toNat := by
            rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 ≤ nw.toNat
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          have hrec := ih t'.clock ht'_clk t' (iw + 1#64) rfl ht'_eq hiw1_le
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "n" by decide, h_n])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "p" by decide, h_p])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "esz" by decide, h_esz])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "idx" by decide, h_idx])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hnt
          refine ⟨fun hnone => ?_, hrec.2.1, hrec.2.2⟩
          obtain ⟨heq_st, hloc_y⟩ := hrec.1 hnone
          refine ⟨heq_st, fun y hy => (hloc_y y hy).trans ?_⟩
          simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            hy, Ne.symm hy]
    · rw [if_neg hi_lt_n] at hnt ⊢
      rw [if_neg (by decide)] at hnt ⊢
      exact ⟨fun _ => ⟨by rw [← hclk] at ht_eq; exact ht_eq, fun _ _ => rfl⟩,
        fun _ h => by simp at h, fun _ h => by simp at h⟩

private theorem decCall_lst_upsert_idx_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (lExp eszExp idxExp : ExpHOL 64) (lw eszw idxw : BitVec 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (hev_l : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lExp =
      some (.val (.word lw)))
    (hev_e : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) eszExp =
      some (.val (.word eszw)))
    (hev_i : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) idxExp =
      some (.val (.word idxw)))
    (hesz : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40)
    (horig_nz : lw ≠ 0 → ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s lw.toNat ∧ BalListOrigin s lw.toNat eszw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont)).1) :
    ∃ (ew : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw ≠ 0 ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid ∧
      WorldOK mid ∧
      (∀ S' Nd', WorldTypedWith mid S' Nd' →
        LstOK mid lw.toNat ∧ BalListOrigin mid lw.toNat eszw.toNat) ∧
      ew.toNat % 8 = 0 ∧
      sourceBase ≤ ew.toNat ∧
      ew.toNat + eszw.toNat ≤ heapEnd ∧
      memW mid lw.toNat ≤ ew.toNat ∧
      ew.toNat + eszw.toNat ≤ memW mid lw.toNat + eszw.toNat * memW mid (lw.toNat + 16) ∧
      mid.locals.lookup x = some (.val (.word ew)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hG := hW.1.1
  have hAs := hW.1
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [lExp, eszExp, idxExp] = some [.val (.word lw), .val (.word eszw), .val (.word idxw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev_l, hev_e, hev_i]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "lst_upsert_idx")
    (ofString "l") (ofString "esz") (ofString "idx")
    (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) lw eszw idxw
    (by decide) (by decide) (by decide) (by rw [hG.code]; exact lookup_lst_upsert_idx_add)
  rw [hargs] at hnt hres; dsimp only at hnt hres
  rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := ((HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
      (ofString "esz", ValueHOL.val (.word eszw))).update
      (ofString "idx", ValueHOL.val (.word idxw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_eq : ent = { s with locals := cmap, clock := s.clock - 1 } := rfl
    have hent_ma : ent.memaddrs = ordinaryDomain := hG.memaddrs
    have hent_l : ent.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "idx" ≠ ofString "l" by decide, show ofString "esz" ≠ ofString "l" by decide]
    have hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "idx" ≠ ofString "esz" by decide]
    have hent_i : ent.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    by_cases hlw0 : lw = 0
    · have hnot8 : ¬ ent.memaddrs 8#64 := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff]
        have hsb : sourceBase = 2701131776 := rfl
        simp [hsb]
      have hbody_err : (evaluateHOLFiniteState ent
          (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 = some .error := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_upsert_idx,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
        have hl0 : ent.locals.lookup (ofString "l") = some (.val (.word 0#64)) := by
          subst hlw0; exact hent_l
        have hev8 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) = none := by
          simp [evalHOLExact, evalListHOLExact, hl0, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.foldr, hz_8, memLoadHOLExact, hnot8]
        rw [hev8]
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) with ⟨rb, sb⟩
      have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) = (rb, sb) := hrun
      rw [hrun] at hbody_err; rw [hrun'] at hres; dsimp only at hbody_err hres
      subst rb; exact absurd hres not_resumes_error
    · have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw0 (BitVec.eq_of_toNat_eq (by simpa using h))
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      obtain ⟨hlst0, horig0⟩ := horig_nz hlw0 S0 Nd0 hWT0
      obtain ⟨hl_fix0, hp_fix0, _, _, _, _⟩ :=
        bal_list_slice_props hWT0.2.2.1 hlw_nz_nat hesz hlst0 (balListOrigin_slice horig0)
      have hesz_pos : 0 < eszw.toNat := by rcases hesz with h | h | h <;> omega
      have hpos_arr : eszw.toNat * memW s (lw.toNat + 16) ≠ 0 :=
        ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst0.1; omega))
      rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      rcases hWT0.2.2.1.1 _ hp_fix0 with h0 | ⟨hal_p, hw_p⟩
      · exact absurd h0 hpos_arr
      have hhe_264 : heapEnd < 2 ^ 64 := by decide
      have hsb_ss : sourceBase ≤ scratchStart := by decide
      have hl_bnd : sourceBase ≤ lw.toNat ∧ lw.toNat + 24 ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l).1
        rcases hal_l with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hp_bnd : sourceBase ≤ memW s lw.toNat ∧
          memW s lw.toNat + eszw.toNat * memW s (lw.toNat + 16) ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_p).1
        rcases hal_p with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hcap_mul_le : 1 * memW s (lw.toNat + 16) ≤ eszw.toNat * memW s (lw.toNat + 16) :=
        Nat.mul_le_mul_right _ hesz_pos
      let nw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 8))
      let pw0 : BitVec 64 := BitVec.ofNat 64 (memW s lw.toNat)
      have hnw_toNat : nw.toNat = memW s (lw.toNat + 8) := by
        dsimp [nw]; rw [BitVec.toNat_ofNat]
        have := hlst0.2; exact Nat.mod_eq_of_lt (by omega)
      have hpw0_toNat : pw0.toNat = memW s lw.toNat := by
        dsimp [pw0]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hl0_bv : lw + 0#64 = BitVec.ofNat 64 lw.toNat := by simp
      have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rfl
      have hl8_toNat : (lw + 8#64).toNat = lw.toNat + 8 := by
        rw [hl8_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hdom_l0 : ent.memaddrs (lw + 0#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff]
        have : (lw + 0#64).toNat = lw.toNat := by simp
        rw [this]; exact ⟨hw_l.1, by omega, by omega⟩
      have hdom_l8 : ent.memaddrs (lw + 8#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff, hl8_toNat]
        exact ⟨by have := hw_l.1; omega, by omega, by omega⟩
      have hm_l0 : ent.memory (lw + 0#64) = .word pw0 := by
        change s.memory (lw + 0#64) = .word pw0
        rw [hl0_bv]; dsimp [pw0]; unfold memW
        rcases s.memory (BitVec.ofNat 64 lw.toNat) with ⟨w⟩; simp
      have hm_l8 : ent.memory (lw + 8#64) = .word nw := by
        change s.memory (lw + 8#64) = .word nw
        rw [hl8_bv]; dsimp [nw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 8)) with ⟨w⟩; simp
      -- Step `dec "n"`, `dec "p"`, `dec "i"` on `ent`:
      let s_n : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
      let s_p : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "p") (.val (.word pw0)) s_n
      let s_dec : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s_p
      let tailProg : ProgHOL 64 :=
        .seq lstUpsertLoop
          (.decCall (ofString "e") .one (ofString "lst_push")
            [.var .local (ofString "l"), .var .local (ofString "esz")]
            (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
              (.return (.var .local (ofString "e")))))
      have hbody_step : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) =
          (let out := evaluateHOLFiniteState s_dec tailProg;
           (out.1,
            { out.2 with
              locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq out.2.locals (ofString "i", s_p.locals.lookup (ofString "i")))
                  (ofString "p", s_n.locals.lookup (ofString "p")))
                (ofString "n", ent.locals.lookup (ofString "n")) })) := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_upsert_idx,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
        have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := BitVec.add_zero _
        have hev_n : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) = some (.val (.word nw)) := by
          simp only [evalHOLExact, evalListHOLExact, hent_l, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_8, memLoadHOLExact,
            isWfShapeExactHOL, hdom_l8, hm_l8, ↓reduceIte]
        rw [hev_n]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        have hs_n_def : setVarHOLFinite (ofString "n") (.val (.word nw)) ent = s_n := rfl
        rw [hs_n_def, evaluateHOLFiniteState_dec_total]; dsimp only
        have hl_sn : s_n.locals.lookup (ofString "l") = some (.val (.word lw)) := by
          simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "l" by decide, hent_l]
        have hev_p : @evalHOLExact 64 F _ s_n.toExact (fun a => Classical.propDecidable (s_n.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 0#64])) = some (.val (.word pw0)) := by
          have hd0 : s_n.memaddrs (lw + 0#64) := hdom_l0
          have hm0 : s_n.memory (lw + 0#64) = .word pw0 := hm_l0
          simp only [evalHOLExact, evalListHOLExact, hl_sn, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0, memLoadHOLExact,
            isWfShapeExactHOL, hd0, hm0, ↓reduceIte]
        rw [hev_p]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        have hs_p_def : setVarHOLFinite (ofString "p") (.val (.word pw0)) s_n = s_p := rfl
        rw [hs_p_def, evaluateHOLFiniteState_dec_total]; dsimp only
        have hev_i0 : @evalHOLExact 64 F _ s_p.toExact (fun a => Classical.propDecidable (s_p.memaddrs a))
            (.const 0#64) = some (.val (.word 0#64)) := rfl
        rw [hev_i0]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        rfl
      have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) =
          evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) := rfl
      have hnt_tail : (evaluateHOLFiniteState s_dec tailProg).1 ≠ some .timeOut := by
        intro hto
        have hfst : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 = some .timeOut := by
          rw [hrun', hbody_step]; dsimp only; exact hto
        rw [hfst] at hnt; exact hnt rfl
      have hnt_loop : (evaluateHOLFiniteState s_dec lstUpsertLoop).1 ≠ some .timeOut := by
        intro hto
        apply hnt_tail
        dsimp only [tailProg]; rw [evaluateHOLFiniteState_seq_line780]
        rcases hlp0 : evaluateHOLFiniteState s_dec lstUpsertLoop with ⟨rl0, sl0⟩
        rw [hlp0] at hto; dsimp only at hto; subst rl0; rfl
      have hs_dec_eq : s_dec = { s with locals := s_dec.locals, clock := s_dec.clock } := by
        simp [s_dec, s_p, s_n, setVarHOLFinite, hent_eq]
      have hloop := lst_upsert_loop_eval s lw nw pw0 eszw idxw hG.code hG.memaddrs hesz hlst0
        ⟨by simpa [hpw0_toNat] using hw_p.1,
         by simpa [hpw0_toNat] using hp_bnd.1,
         by simpa [hpw0_toNat] using hp_bnd.2⟩
        hnw_toNat s_dec.clock s_dec 0#64 rfl hs_dec_eq (by simp)
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide])
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide])
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "esz" by decide, show ofString "p" ≠ ofString "esz" by decide,
          show ofString "n" ≠ ofString "esz" by decide, hent_e])
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "idx" by decide, show ofString "p" ≠ ofString "idx" by decide,
          show ofString "n" ≠ ofString "idx" by decide, hent_i])
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        hnt_loop
      rcases hlp_ev : evaluateHOLFiniteState s_dec lstUpsertLoop with ⟨rl, sl⟩
      rw [hlp_ev] at hloop; dsimp only at hloop
      cases rl with
      | some rl' =>
        -- Either loop returned `ew`, or non-resumable error
        have htail_ev : evaluateHOLFiniteState s_dec tailProg = (some rl', sl) := by
          dsimp only [tailProg]; rw [evaluateHOLFiniteState_seq_line780, hlp_ev]
        by_cases hret : ∃ rv, rl' = .returned rv
        · rcases hret with ⟨rv, rfl⟩
          obtain ⟨ew, rfl, hew8, hew_sb, hew_he, hew_lo, hew_hi, hsl_eq⟩ := hloop.2.1 rv rfl
          let sl_rest : PanSemStateFiniteExact 64 F :=
            { sl with
              locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq sl.locals (ofString "i", s_p.locals.lookup (ofString "i")))
                  (ofString "p", s_n.locals.lookup (ofString "p")))
                (ofString "n", ent.locals.lookup (ofString "n")) }
          have hbody_ret : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
              (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) =
              (some (.returned (.val (.word ew))), sl_rest) := by
            rw [hrun', hbody_step]; dsimp only; rw [htail_ev]
          let mid := setVarHOLFinite x (.val (.word ew)) { s with clock := sl.clock }
          have hsl_rest_s : { sl_rest with locals := s.locals } = { s with clock := sl.clock } := by
            dsimp only [sl_rest]; rw [hsl_eq]
          have hmid_eq : setVarHOLFinite x (.val (.word ew)) { sl_rest with locals := s.locals } = mid := by
            rw [hsl_rest_s]
          have hsh_ew : (shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          have heval_eq : evaluateHOLFiniteState s
              (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont) =
              ((evaluateHOLFiniteState mid cont).1,
                { (evaluateHOLFiniteState mid cont).2 with
                  locals := HolFiniteMapExact.resVarEq
                    (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
            rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]; dsimp only
            rw [hlk]; dsimp only; rw [if_neg hcz, hbody_ret]; dsimp only
            rw [if_pos hsh_ew, hmid_eq]
          have hws_mid : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
            worldStep_refl (fun _ => []) ["heap_ptr"] hAs (by simp [mid, setVarHOLFinite])
          have hmid_memW : ∀ a, memW mid a = memW s a := fun _ => rfl
          refine ⟨ew, mid, hlw0, hws_mid, worldOK_of_step hW hws_mid,
            fun S' Nd' h => by
              have hs' : WorldTypedWith s S' Nd' :=
                (worldTypedWith_with_locals s (s.locals.update (x, .val (.word ew))) sl.clock S' Nd').1 h
              exact horig_nz hlw0 S' Nd' hs',
            hew8, hew_sb, hew_he,
            by rw [hmid_memW, ← hpw0_toNat]; exact hew_lo,
            by rw [hmid_memW, hmid_memW, ← hpw0_toNat]; exact hew_hi,
            by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
            by rw [hbody_ret] at hnt; dsimp only at hnt; rw [if_pos hsh_ew, hmid_eq] at hnt; exact hnt,
            by rw [hbody_ret] at hres; dsimp only at hres; rw [if_pos hsh_ew, hmid_eq] at hres; exact hres,
            by rw [heval_eq], by rw [heval_eq]⟩
        · have hnr := hloop.2.2 rl' rfl (fun rv h => hret ⟨rv, h⟩)
          have hbody_nr : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
              (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 = some rl' := by
            rw [hrun', hbody_step]; dsimp only; rw [htail_ev]
          rw [hbody_nr] at hres
          exfalso
          cases rl' with
          | timeOut => exact absurd (congrArg Prod.fst hlp_ev) hnt_loop
          | «break» | «continue» | error => exact not_resumes_error hres
          | finalFfi _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | exception e ev => exact hnr hres
          | returned rv => exact hret ⟨rv, rfl⟩
      | none =>
        -- Loop fell through without finding `idx`: runs `decCall "e" .one "lst_push" ...`
        obtain ⟨hsl_eq, hsl_loc⟩ := hloop.1 rfl
        have htail_ev : evaluateHOLFiniteState s_dec tailProg =
            evaluateHOLFiniteState sl
              (.decCall (ofString "e") .one (ofString "lst_push")
                [.var .local (ofString "l"), .var .local (ofString "esz")]
                (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
                  (.return (.var .local (ofString "e"))))) := by
          dsimp only [tailProg]; rw [evaluateHOLFiniteState_seq_line780, hlp_ev]
        have hsl_W : WorldOK sl := by
          rw [hsl_eq]
          exact (worldOK_with_locals s sl.locals sl.clock).2 hW
        have hsl_l : sl.locals.lookup (ofString "l") = some (.val (.word lw)) := by
          rw [hsl_loc _ (by decide)]
          simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "l" by decide, show ofString "p" ≠ ofString "l" by decide,
            show ofString "n" ≠ ofString "l" by decide, hent_l]
        have hsl_e : sl.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
          rw [hsl_loc _ (by decide)]
          simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "esz" by decide, show ofString "p" ≠ ofString "esz" by decide,
            show ofString "n" ≠ ofString "esz" by decide, hent_e]
        have hsl_idx : sl.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
          rw [hsl_loc _ (by decide)]
          simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "idx" by decide, show ofString "p" ≠ ofString "idx" by decide,
            show ofString "n" ≠ ofString "idx" by decide, hent_i]
        have horig_sl : lw ≠ 0 → ∀ S Nd, WorldTypedWith sl S Nd →
            LstOK sl lw.toNat ∧ BalListOrigin sl lw.toNat eszw.toNat := by
          intro hnz S Nd hWT_sl
          have hWT_s : WorldTypedWith s S Nd := by
            rw [hsl_eq] at hWT_sl
            exact (worldTypedWith_with_locals s sl.locals sl.clock S Nd).1 hWT_sl
          rw [hsl_eq]
          exact horig_nz hnz S Nd hWT_s
        have hbody_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 =
            (evaluateHOLFiniteState sl
              (.decCall (ofString "e") .one (ofString "lst_push")
                [.var .local (ofString "l"), .var .local (ofString "esz")]
                (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
                  (.return (.var .local (ofString "e")))))).1 := by
          rw [hrun', hbody_step]; dsimp only; rw [htail_ev]
        have hpush_nt : (evaluateHOLFiniteState sl
            (.decCall (ofString "e") .one (ofString "lst_push")
              [.var .local (ofString "l"), .var .local (ofString "esz")]
              (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
                (.return (.var .local (ofString "e")))))).1 ≠ some .timeOut := by
          rw [← htail_ev]; exact hnt_tail
        -- Check whether the body itself `Resumes` so we can step `decCall_lst_push_resumes`:
        rcases hbody_out : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) with ⟨rb, sb⟩
        rw [hbody_out] at hnt hres hbody_eq
        have hpush_res : Resumes (evaluateHOLFiniteState sl
            (.decCall (ofString "e") .one (ofString "lst_push")
              [.var .local (ofString "l"), .var .local (ofString "esz")]
              (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
                (.return (.var .local (ofString "e")))))).1 := by
          rw [← hbody_eq]
          cases rb with
          | none => exact absurd hres not_resumes_error
          | some rb' =>
            cases rb' with
            | timeOut => exact absurd rfl hnt
            | «break» | «continue» | error => exact absurd hres not_resumes_error
            | finalFfi _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
            | exception e ev =>
              exfalso
              rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
              · simp at h
              · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
                exact lst_upsert_idx_no_catchable_exn_add ent hG.code e ev hne
                  (by rw [← hrun', hbody_out])
            | returned vb => exact Or.inl ⟨vb, rfl⟩
        obtain ⟨ew, mid_p, _, hws_p, hW_p, horig_p, hew8, hew_sb, hew_he, hew_lo, hew_hi,
            hmid_e, hmid_other, hcont_nt, hcont_res, hpush_fst, hpush_snd⟩ :=
          decCall_lst_push_resumes sl (ofString "e")
            (.var .local (ofString "l")) (.var .local (ofString "esz")) lw eszw
            (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
              (.return (.var .local (ofString "e"))))
            hsl_W
            (by simp [evalHOLExact, hsl_l])
            (by simp [evalHOLExact, hsl_e])
            hesz horig_sl hpush_nt hpush_res
        -- Step `store e idx; return e` on `mid_p`:
        have hmid_idx : mid_p.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
          rw [hmid_other _ (by decide)]; exact hsl_idx
        have hdom_ew : mid_p.memaddrs ew := by
          rw [hW_p.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff]
          exact ⟨hew8, hew_sb, by have := hesz_pos; rcases hesz with h | h | h <;> omega⟩
        let mid_st : PanSemStateFiniteExact 64 F :=
          { mid_p with memory := fun a => if a = ew then .word idxw else mid_p.memory a }
        have hst_only : evaluateHOLFiniteState mid_p
            (.store (.var .local (ofString "e")) (.var .local (ofString "idx"))) =
            (none, mid_st) := by
          rw [evaluateHOLFiniteState_store]
          have hev1 : @evalHOLExact 64 F _ mid_p.toExact (fun a => Classical.propDecidable (mid_p.memaddrs a))
              (.var .local (ofString "e")) = some (.val (.word ew)) := by
            simp [evalHOLExact, hmid_e]
          have hev2 : @evalHOLExact 64 F _ mid_p.toExact (fun a => Classical.propDecidable (mid_p.memaddrs a))
              (.var .local (ofString "idx")) = some (.val (.word idxw)) := by
            simp [evalHOLExact, hmid_idx]
          rw [hev1, hev2]; simp only [flattenHOL]
          unfold panMemStoresHOL panMemStoreHOL
          rw [if_pos hdom_ew]; rfl
        have hst_ew : evaluateHOLFiniteState mid_p
            (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
              (.return (.var .local (ofString "e")))) =
            (some (.returned (.val (.word ew))), emptyLocalsHOLFinite mid_st) := by
          rw [evaluateHOLFiniteState_seq_line780, hst_only]; dsimp only
          rw [evaluateHOLFiniteState_return]
          have hev3 : @evalHOLExact 64 F _ mid_st.toExact (fun a => Classical.propDecidable (mid_st.memaddrs a))
              (.var .local (ofString "e")) = some (.val (.word ew)) := by
            simp [evalHOLExact, mid_st, hmid_e]
          rw [hev3]; dsimp only
          rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])]
        have hbre_st : ByteRegionEffect mid_p mid_st
            [(memW mid_p lw.toNat, eszw.toNat * memW mid_p (lw.toNat + 16))] := by
          refine (bre_of_store_multi hW_p.1.1.memaddrs (nw := 1) (by omega) hst_only
            (fun v hv => by
              have hev2 : @evalHOLExact 64 F _ mid_p.toExact (fun a => Classical.propDecidable (mid_p.memaddrs a))
                  (.var .local (ofString "idx")) = some (.val (.word idxw)) := by
                simp [evalHOLExact, hmid_idx]
              rw [hev2] at hv; injection hv with hv'; subst hv'; simp [flattenHOL])
            (fun addr hdst _ => ?_)).1
          have hev1 : @evalHOLExact 64 F _ mid_p.toExact (fun a => Classical.propDecidable (mid_p.memaddrs a))
              (.var .local (ofString "e")) = some (.val (.word ew)) := by
            simp [evalHOLExact, hmid_e]
          rw [hev1] at hdst; injection hdst with hd; injection hd with hd'; injection hd' with hd''; subst hd''
          refine ⟨by rcases hesz with h | h | h <;> omega,
            (memW mid_p lw.toNat, eszw.toNat * memW mid_p (lw.toNat + 16)), List.mem_singleton.2 rfl,
            hew_lo, by dsimp only; rcases hesz with h | h | h <;> omega⟩
        -- Preserve `memW _ lw.toNat` and `memW _ (lw.toNat + 16)` across `mid_p -> mid_st`:
        obtain ⟨Sp0, hWTp_ex⟩ := hW_p.2
        obtain ⟨Ndp0, hWTp⟩ := (worldTyped_iff_with mid_p Sp0).1 hWTp_ex
        obtain ⟨hlst_p, horig_p0⟩ := horig_p Sp0 Ndp0 hWTp
        obtain ⟨hl_fix_p, hp_fix_p, hdj_p, _, _, _⟩ :=
          bal_list_slice_props hWTp.2.2.1 hlw_nz_nat hesz hlst_p (balListOrigin_slice horig_p0)
        rcases hWTp.2.2.1.1 _ hl_fix_p with h0 | ⟨hal_lp, hw_lp⟩
        · simp at h0
        rcases hWTp.2.2.1.1 _ hp_fix_p with h0 | ⟨_, hw_pp⟩
        · exfalso; exact absurd h0 (ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst_p.1; omega)))
        have hu_hdr_p : M08IvlUnhit mid_p mid_st (lw.toNat, 24) := by
          intro a ha8 ha1 ha2
          apply hbre_st.cell_frame a
          intro i hi hc
          have hi_eq := List.mem_singleton.1 hi; subst i
          exact not_cellHits_of_disj ha8 hw_pp.1 ⟨ha1, ha2⟩ hdj_p hc
        have hl_hi_p : lw.toNat + 24 ≤ 2 ^ 64 := (ivl_allocated_bound hW_p.1.2 hal_lp).2
        have hm0_st : memW mid_st lw.toNat = memW mid_p lw.toNat :=
          memW_eq_of_ivlUnhit hu_hdr_p hw_lp.1 hl_hi_p ⟨by omega, by omega⟩
        have hm16_st : memW mid_st (lw.toNat + 16) = memW mid_p (lw.toNat + 16) :=
          memW_eq_of_ivlUnhit hu_hdr_p (by have := hw_lp.1; dsimp only at this; omega) hl_hi_p ⟨by omega, by omega⟩
        -- Finalize `mid` after `decCall` restores `s.locals` and binds `x := ew`:
        let mid : PanSemStateFiniteExact 64 F :=
          setVarHOLFinite x (.val (.word ew)) { sb with locals := s.locals }
        have hrb_eq : rb = some (.returned (.val (.word ew))) := by
          dsimp only at hbody_eq; rw [hbody_eq, hpush_fst, hst_ew]
        have hsb_eq : sb =
            { emptyLocalsHOLFinite mid_st with
              locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq
                    (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite mid_st).locals
                      (ofString "e", sl.locals.lookup (ofString "e")))
                    (ofString "i", s_p.locals.lookup (ofString "i")))
                  (ofString "p", s_n.locals.lookup (ofString "p")))
                (ofString "n", ent.locals.lookup (ofString "n")) } := by
          have hsnd := congrArg Prod.snd hbody_out
          rw [hrun', hbody_step] at hsnd; dsimp only at hsnd
          rw [htail_ev, hpush_snd, hst_ew] at hsnd
          exact hsnd.symm
        have hmid_from_st : mid = { mid_st with locals := s.locals.update (x, .val (.word ew)) } := by
          simp [mid, hsb_eq, setVarHOLFinite, emptyLocalsHOLFinite]
        have hbre_mid : ByteRegionEffect mid_p mid
            [(memW mid_p lw.toNat, eszw.toNat * memW mid_p (lw.toNat + 16))] := by
          rw [hmid_from_st]
          exact hbre_st.with_locals_clock (s.locals.update (x, .val (.word ew))) mid_st.clock
        obtain ⟨hws_st, hW_mid, horig_mid⟩ :=
          bal_list_store_arr_worldStep (r := none) hW_p hlw_nz_nat hesz horig_p hbre_mid
        have hws_s_sl : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none sl :=
          worldStep_refl (fun _ => []) ["heap_ptr"] hAs hsl_eq
        have hws_sl_mid : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra sl none mid :=
          worldStep_hp_trans hsl_W.1.2 hws_p hws_st
        have hws_total : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
          worldStep_hp_trans hAs.2 hws_s_sl hws_sl_mid
        have hsh_ew : (shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        subst rb
        dsimp only at hnt hres
        rw [if_pos hsh_ew] at hnt hres
        have heval_eq : evaluateHOLFiniteState s
            (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont) =
            ((evaluateHOLFiniteState mid cont).1,
              { (evaluateHOLFiniteState mid cont).2 with
                locals := HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]; dsimp only
          rw [hlk]; dsimp only; rw [if_neg hcz, hbody_out]; dsimp only
          rw [if_pos hsh_ew]
        have hm0_mid : memW mid lw.toNat = memW mid_p lw.toNat := by
          rw [hmid_from_st]; exact hm0_st
        have hm16_mid : memW mid (lw.toNat + 16) = memW mid_p (lw.toNat + 16) := by
          rw [hmid_from_st]; exact hm16_st
        refine ⟨ew, mid, hlw0, hws_total, hW_mid, horig_mid, hew8, hew_sb, hew_he,
          by rw [hm0_mid]; exact hew_lo,
          by rw [hm0_mid, hm16_mid]; exact hew_hi,
          by simp [hmid_from_st, HolFiniteMapExact.lookup_update, FUPDATE],
          fun y hy => by simp [hmid_from_st, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
          hnt, hres, by rw [heval_eq], by rw [heval_eq]⟩

private theorem mem_list_set_old_or_new {α : Type} (xs : List α) (i : Nat) (v a : α)
    (ha : a ∈ xs.set i v) : a ∈ xs ∨ a = v := by
  induction xs generalizing i with
  | nil => simp at ha
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem x ha)
    | succ i =>
      simp only [List.set_cons_succ, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inl (List.mem_cons_self)
      · rcases ih i ha with ha | ha
        · exact Or.inl (List.mem_cons_of_mem x ha)
        · exact Or.inr ha

private theorem htabSetValuesPost_mem {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t v a : Nat}
    (h : HtabSetValuesPost s post t v)
    (ha : a ∈ htabValues post t) : a ∈ htabValues s t ∨ a = v := by
  rcases h with h | ⟨i, hi, h⟩
  · rw [h] at ha
    simpa only [List.mem_append, List.mem_singleton] using ha
  · rw [h] at ha
    exact mem_list_set_old_or_new _ i v a ha

private theorem htabSetValuesPost_value_mem {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t v : Nat}
    (h : HtabSetValuesPost s post t v) :
    v ∈ htabValues post t := by
  rcases h with h | ⟨i, hi, h⟩
  · rw [h]; exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  · rw [h]; exact List.mem_set hi v

private theorem pairwise_flatMap_set_fresh {α β : Type}
    {R : β → β → Prop} (f : α → List β) (xs : List α) (i : Nat) (v : α)
    (hpw : (xs.flatMap f).Pairwise R)
    (hnew : (f v).Pairwise R)
    (hleft : ∀ a ∈ xs.flatMap f, ∀ b ∈ f v, R a b)
    (hright : ∀ a ∈ f v, ∀ b ∈ xs.flatMap f, R a b) :
    ((xs.set i v).flatMap f).Pairwise R := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons] at hpw hleft hright
    obtain ⟨hx, hxs, hcross⟩ := List.pairwise_append.1 hpw
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.flatMap_cons]
      exact List.pairwise_append.2 ⟨hnew, hxs,
        fun a ha b hb => hright a ha b (List.mem_append_right _ hb)⟩
    | succ i =>
      simp only [List.set_cons_succ, List.flatMap_cons]
      refine List.pairwise_append.2 ⟨hx, ih i hxs
        (fun a ha b hb => hleft a (List.mem_append_right _ ha) b hb)
        (fun a ha b hb => hright a ha b (List.mem_append_right _ hb)), ?_⟩
      intro a ha b hb
      obtain ⟨y, hy, hby⟩ := List.mem_flatMap.1 hb
      rcases mem_list_set_old_or_new xs i v y hy with hy | rfl
      · exact hcross a ha b (List.mem_flatMap.2 ⟨y, hy, hby⟩)
      · exact hleft a (List.mem_append_left _ ha) b hby

private theorem pairwise_htabSetValuesPost_flatMap {F α : Type}
    {s post : PanSemStateFiniteExact 64 F} {t v : Nat}
    {R : α → α → Prop} (f : Nat → List α)
    (h : HtabSetValuesPost s post t v)
    (hpw : ((htabValues s t).flatMap f).Pairwise R)
    (hnew : (f v).Pairwise R)
    (hleft : ∀ a ∈ (htabValues s t).flatMap f, ∀ b ∈ f v, R a b)
    (hright : ∀ a ∈ f v, ∀ b ∈ (htabValues s t).flatMap f, R a b) :
    ((htabValues post t).flatMap f).Pairwise R := by
  rcases h with h | ⟨i, hi, h⟩
  · rw [h, List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      List.pairwise_append.2 ⟨hpw, hnew, hleft⟩
  · rw [h]
    exact pairwise_flatMap_set_fresh f _ i v hpw hnew hleft hright

private theorem balRecords_eq_htabValues_add {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : globN s "bal_accounts" ≠ 0) :
    balRecords s = htabValues s (globN s "bal_accounts") := by
  simp only [balRecords, h, if_false, htabValues]

private theorem balRecords_set_values_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : Nat}
    (hroot : globN post "bal_accounts" = globN s "bal_accounts")
    (hnz : globN s "bal_accounts" ≠ 0)
    (h : HtabSetValuesPost s post (globN s "bal_accounts") v) :
    (balRecords post = balRecords s ++ [v] ∨
      ∃ i < (balRecords s).length, balRecords post = (balRecords s).set i v) ∧
    v ∈ balRecords post ∧
    (∀ ad ∈ balRecords post, ad ∈ balRecords s ∨ ad = v) := by
  have hnzp : globN post "bal_accounts" ≠ 0 := by rw [hroot]; exact hnz
  rw [balRecords_eq_htabValues_add hnzp, hroot, balRecords_eq_htabValues_add hnz]
  exact ⟨h, htabSetValuesPost_value_mem h, fun ad had => htabSetValuesPost_mem h had⟩

private theorem pairwise_balObjects_set_values_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : Nat}
    (hroot : globN post "bal_accounts" = globN s "bal_accounts")
    (hnz : globN s "bal_accounts" ≠ 0)
    (h : HtabSetValuesPost s post (globN s "bal_accounts") v)
    (objects : Nat → List Ivl)
    (hobjects : ∀ ad ∈ balRecords post,
      (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++
        lstObjects post (memW post (ad + 32)) 24 ++
        (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) = objects ad)
    (hpw : ((balRecords s).flatMap objects).Pairwise Disj)
    (hnew : (objects v).Pairwise Disj)
    (hleft : ∀ a ∈ (balRecords s).flatMap objects, ∀ b ∈ objects v, Disj a b)
    (hright : ∀ a ∈ objects v, ∀ b ∈ (balRecords s).flatMap objects, Disj a b) :
    (balObjects post).Pairwise Disj := by
  have hobj : balObjects post = (balRecords post).flatMap objects := by
    unfold balObjects
    exact List.flatMap_congr hobjects
  rw [hobj]
  have hnzp : globN post "bal_accounts" ≠ 0 := by rw [hroot]; exact hnz
  rw [balRecords_eq_htabValues_add hnzp, hroot]
  rw [balRecords_eq_htabValues_add hnz] at hpw hleft hright
  exact pairwise_htabSetValuesPost_flatMap objects h hpw hnew hleft hright

private theorem pairwise_filter_comm {α : Type}
    {R : α → α → Prop} {p : α → Bool} {xs : List α}
    (h : xs.Pairwise R) : (xs.filter p).Pairwise R :=
  h.sublist List.filter_sublist

private theorem filter_append_three {α : Type} (p : α → Bool) (a b c : List α) :
    (a ++ b ++ c).filter p = a.filter p ++ b.filter p ++ c.filter p := by
  rw [List.filter_append, List.filter_append]

private theorem fixedTyped_of_sublist_old_fresh_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {fresh : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post) (hF : FixedTyped s)
    (hsub : (fixedObjects post).Sublist (fixedObjects s ++ fresh))
    (hfresh : ∀ i ∈ fresh,
      Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧ WordsOK post i)
    (hpw : fresh.Pairwise Disj) :
    FixedTyped post ∧
    (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr")) := by
  have hclass : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o ∈ fresh := by
    intro o ho
    exact List.mem_append.1 (hsub.subset ho)
  constructor
  · constructor
    · intro i hi
      rcases hclass i hi with hold | hnew
      · rcases hF.1 i hold with hz | ⟨hal, hw⟩
        · exact Or.inl hz
        · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
      · obtain ⟨hin, hw⟩ := hfresh i hnew
        exact Or.inr ⟨Or.inl ⟨le_trans hAs.2.1 hin.1, hin.2⟩, hw⟩
    · apply list_sublist_pairwise hsub
      apply List.pairwise_append.2
      refine ⟨hF.2, hpw, ?_⟩
      intro a ha b hb
      rcases hF.1 a ha with hz | ⟨hal, _⟩
      · exact Or.inl hz
      · exact disj_flip (disj_allocated_fresh_heap hAs.2 hAp.2 hal (hfresh b hb).1)
  · intro o ho
    rcases hclass o ho with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inr (hfresh o hnew).1)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal
