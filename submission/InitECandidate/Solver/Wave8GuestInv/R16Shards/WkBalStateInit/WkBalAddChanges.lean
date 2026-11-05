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

private theorem bal_ensure_existing_tail {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f0 f1 : BitVec 64) (fresh : ProgHOL 64)
    (hW : WorldOK s)
    (hm : s.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word f0), .val (.word f1)]))
    (hf0 : f0 ≠ 0) :
    evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.rfield 1 (.var .local (ofString "m")))) .skip) fresh) =
      (some (.returned (.val (.word f1))), emptyLocalsHOLFinite s) ∧
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (some (.returned (.val (.word f1)))) (emptyLocalsHOLFinite s) := by
  have hf0_64 : f0 ≠ 0#64 := hf0
  have hcmp : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
      some (.val (.word 1#64)) := by
    simp [evalHOLExact, hm, Compiler.Encoders.Asm.wordCmpHOL, hf0_64]
  have hite : evaluateHOLFiniteState s
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.rfield 1 (.var .local (ofString "m")))) .skip) =
      (some (.returned (.val (.word f1))), emptyLocalsHOLFinite s) := by
    rw [evaluateHOLFiniteState_ite, hcmp]
    dsimp only
    rw [if_neg (by decide), evaluateHOLFiniteState_return]
    simp [evalHOLExact, hm, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  constructor
  · rw [evaluateHOLFiniteState_seq_line780, hite]
  · exact worldStep_refl (fun _ => []) ["heap_ptr"] hW.1 rfl

private theorem bal_lookup_value_record {F : Type}
    {s : PanSemStateFiniteExact 64 F} {tw f0 f1 : BitVec 64}
    (hroot : globN s "bal_accounts" = tw.toNat)
    (htw : tw ≠ 0) (hf0 : f0 ≠ 0)
    (hvalue : HtabWF s tw.toNat → f0 ≠ 0 → f1.toNat ∈ htabValues s tw.toNat)
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) :
    f1.toNat ∈ balRecords s := by
  have hnz : globN s "bal_accounts" ≠ 0 := by
    rw [hroot]
    exact fun h => htw (BitVec.eq_of_toNat_eq (by simpa using h))
  have htS : globN s "bal_accounts" ∈ S := by
    rcases hWT.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h | h
    · exact absurd h hnz
    · exact h
  have hwf : HtabWF s tw.toNat := by
    rw [← hroot]
    exact (hWT.1.2.1 _ htS).1
  rw [balRecords_eq_htabValues_add hnz, hroot]
  exact hvalue hwf hf0

private theorem seq_store_bal_record_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pw off vw : BitVec 64)
    (valExp : ExpHOL 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some (.val (.word vw))) :
    let mid : PanSemStateFiniteExact 64 F :=
      { s with memory := fun a => if a = pw + off then .word vw else s.memory a }
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const off]) valExp) cont) =
      evaluateHOLFiniteState mid cont ∧
    ArenaReady mid ∧
    memW mid (pw.toNat + off.toNat) = vw.toNat ∧
    (∀ k, k ≠ pw.toNat + off.toNat → k < 2 ^ 64 → memW mid k = memW s k) ∧
    FrameOutside s mid [] (pw.toNat, 40) := by
  dsimp only
  have hhplim := hAR.2.2.1
  have hlim : heapLimit < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have haddr : (pw + off).toNat = pw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hdom : s.memaddrs (pw + off) := by
    rw [hAR.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, haddr]
    exact ⟨by omega, by omega, by omega⟩
  have hdst : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "ad"), .const off]) =
      some (.val (.word (pw + off))) := by
    simp [evalHOLExact, evalListHOLExact, had, wordOpHOL, wordOp, valueIsWord, valueWord]
  have hstore : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "ad"), .const off]) valExp) =
      (none, { s with memory := fun a => if a = pw + off then .word vw else s.memory a }) := by
    rw [evaluateHOLFiniteState_store, hdst, hval]
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
  refine ⟨by rw [evaluateHOLFiniteState_seq_line780, hstore],
    ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, hAR.2⟩, ?_, ?_, ?_⟩
  · have hb : BitVec.ofNat 64 (pw.toNat + off.toNat) = pw + off := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), haddr]
    simp [memW, hb]
  · intro k hne hk
    have hb : BitVec.ofNat 64 k ≠ pw + off := by
      intro heq
      have he := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, haddr] at he
      exact hne he
    simp [memW, hb]
  · intro a _ hno
    have hne : a ≠ pw + off := by
      rintro rfl
      exact hno ⟨by dsimp only; omega, by dsimp only; omega⟩
    simp [hne]

private theorem bal_ensure_missing_tail {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f1 : BitVec 64) (fresh : ProgHOL 64)
    (hm : s.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word 0#64), .val (.word f1)])) :
    evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.rfield 1 (.var .local (ofString "m")))) .skip) fresh) =
      evaluateHOLFiniteState s fresh := by
  have hcmp : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
      some (.val (.word 0#64)) := by
    simp [evalHOLExact, hm, Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp]
  simp [evaluateHOLFiniteState_skip]

private theorem bal_ensure_insert_return {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw addrw adw : BitVec 64)
    (hAR : ArenaReady s)
    (hroot : s.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)))
    (haddr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)))
    (had : s.locals.lookup (ofString "ad") = some (.val (.word adw)))
    (htnz : tw.toNat ≠ 0)
    (hWF : HtabWF s tw.toNat)
    (hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.var .global (ofString "bal_accounts"), .var .local (ofString "addr"),
          .var .local (ofString "ad")])
        (.return (.var .local (ofString "ad"))))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.var .global (ofString "bal_accounts"), .var .local (ofString "addr"),
          .var .local (ofString "ad")])
        (.return (.var .local (ofString "ad"))))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      SoloHtabSet.HtabExitAt tw.toNat s mid ∧
      HtabSetValuesPost s mid tw.toNat adw.toNat ∧
      mid.be = s.be ∧ mid.locals = s.locals ∧
      adw.toNat ∈ balRecords mid ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .global (ofString "bal_accounts"), .var .local (ofString "addr"),
            .var .local (ofString "ad")])
          (.return (.var .local (ofString "ad")))) =
        (some (.returned (.val (.word adw))), emptyLocalsHOLFinite mid) := by
  obtain ⟨mid, hexit, hvalues, hbe, hlocals, hsp, hfmp, hnt', hres', heval⟩ :=
    seq_call_htab_set_void_resumes s
      (.var .global (ofString "bal_accounts")) (.var .local (ofString "addr"))
      (.var .local (ofString "ad")) (.return (.var .local (ofString "ad")))
      tw addrw adw
      (by simpa [evalAt, evalHOLExact] using hroot)
      (by simpa [evalAt, evalHOLExact] using haddr)
      (by simpa [evalAt, evalHOLExact] using had)
      hAR hWF hal hnt hres
  have hroots : globN s "bal_accounts" = tw.toNat := by simp [globN, hroot]
  have hrootm : globN mid "bal_accounts" = tw.toNat := by
    rw [globN_eq_of_lookup (hexit.2.2.2.2.2.2.2 (ofString "bal_accounts") (by decide))]
    exact hroots
  have hmem : adw.toNat ∈ balRecords mid := by
    rw [balRecords_eq_htabValues_add (by rw [hrootm]; exact htnz), hrootm]
    exact htabSetValuesPost_value_mem hvalues
  refine ⟨mid, hexit, hvalues, hbe, hlocals, hmem, ?_⟩
  rw [heval, evaluateHOLFiniteState_return]
  simp [evalHOLExact, hlocals, had, shapeOfHOLExact, sizeOfShapeWithContextHOL]

private theorem seq_htab_new_store_bal_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "t"))) cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "t"))) cont))).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧ mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      HtabWF mid tw.toNat ∧ hdr mid tw.toNat 3 = 0 ∧ hdr mid tw.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = tw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 40 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      (∀ y, y ≠ ofString "t" → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new")
          [.const 32#64, .const 8#64])
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "t"))) cont)) = evaluateHOLFiniteState mid cont := by
  obtain ⟨tw, m1, htlo, hthi, hA1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hkey1,
    hfp1, hfr1, hl1, hg1, hnt1, hres1, heq1⟩ :=
    seq_call_htab_new_resumes s .local (ofString "t") 32#64 8#64 _ hAR
      (by decide) (by decide) (fun h => by cases h) hnt hres
  obtain ⟨ht, hloc, hgl⟩ := hl1 rfl
  have had1 : m1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc _ (by decide)).trans had
  have hp_hi : pw.toNat + 40 ≤ globN m1 "heap_ptr" := by omega
  obtain ⟨heq2, hA2, hword, hother, hfr2⟩ :=
    seq_store_bal_record_slot m1 pw off tw (.var .local (ofString "t")) cont
      hA1 had1 hlo hp_hi hp8 hoff8 hoff ht
  let mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word tw else m1.memory a }
  have haddr : (pw + off).toNat = pw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := hA1.2.2.1
      have hlim : heapLimit < 2 ^ 64 := by decide
      omega)]
  have hu : ∀ i ∈ htabFootprint m1 tw.toNat, M08IvlUnhit m1 mid i := by
    intro i hi a _ ha _
    have hin := (hfp1 i hi).2
    have hne : a ≠ pw + off := by
      rintro rfl
      rw [haddr] at ha
      dsimp only [Inside] at hin
      omega
    simp [mid, hne]
  obtain ⟨hwf2, hfp2, hhdr2⟩ := htabWF_transfer_unhit hA1 hA2 hwf1 hu
    (fun i hi => (hfp1 i hi).1)
  have hfr : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnf
    exact (hfr2 a (fun _ h => by cases h) (hno _ (by simp))).trans
      (hfr1 a (fun j hj => hno j (by
        rcases List.mem_singleton.1 hj with rfl
        exact List.mem_cons_self)) hnf)
  rw [heq2] at hnt1 hres1
  refine ⟨tw, mid, htlo, hthi, hA2, hbe1, hsp1, hwf2,
    (hhdr2 3 (by omega)).trans hcnt1, (hhdr2 0 (by omega)).trans hkey1,
    fun i hi => by rw [hfp2] at hi; exact hfp1 i hi,
    hword, ?_, hfr, ht, hloc, hgl, hnt1, hres1, heq1.trans heq2⟩
  intro off' hoff'_hi hoff'_ne
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hk64 : pw.toNat + off' < 2 ^ 64 := by have := hAR.2.2.1; omega
  rw [hother (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      rcases List.mem_singleton.1 hj with rfl
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem decCall_htab_new_store_bal_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "t"))) cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "t"))) cont))).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧ mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      HtabWF mid tw.toNat ∧ hdr mid tw.toNat 3 = 0 ∧ hdr mid tw.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = tw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 40 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      (∀ y, y ≠ ofString "t" → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "t"))) cont))).1 = (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "t"))) cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals
            (ofString "t", s.locals.lookup (ofString "t")) } := by
  obtain ⟨tw, m1, htlo, hthi, hA1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hkey1,
    hfp1, hfr1, ht, hloc, hgl, hnt1, hres1, heq1_fst, heq1_snd⟩ :=
    decCall_htab_new_resumes s (ofString "t") 32#64 8#64 _ hAR
      (by decide) (by decide) hnt hres
  have had1 : m1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc _ (by decide)).trans had
  have hp_hi : pw.toNat + 40 ≤ globN m1 "heap_ptr" := by omega
  obtain ⟨heq2, hA2, hword, hother, hfr2⟩ :=
    seq_store_bal_record_slot m1 pw off tw (.var .local (ofString "t")) cont
      hA1 had1 hlo hp_hi hp8 hoff8 hoff ht
  let mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word tw else m1.memory a }
  have haddr : (pw + off).toNat = pw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := hA1.2.2.1
      have hlim : heapLimit < 2 ^ 64 := by decide
      omega)]
  have hu : ∀ i ∈ htabFootprint m1 tw.toNat, M08IvlUnhit m1 mid i := by
    intro i hi a _ ha _
    have hin := (hfp1 i hi).2
    have hne : a ≠ pw + off := by
      rintro rfl
      rw [haddr] at ha
      dsimp only [Inside] at hin
      omega
    simp [mid, hne]
  obtain ⟨hwf2, hfp2, hhdr2⟩ := htabWF_transfer_unhit hA1 hA2 hwf1 hu
    (fun i hi => (hfp1 i hi).1)
  have hfr : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnf
    exact (hfr2 a (fun _ h => by cases h) (hno _ (by simp))).trans
      (hfr1 a (fun j hj => hno j (by
        rcases List.mem_singleton.1 hj with rfl
        exact List.mem_cons_self)) hnf)
  rw [heq2] at hnt1 hres1 heq1_fst heq1_snd
  refine ⟨tw, mid, htlo, hthi, hA2, hbe1, hsp1, hwf2,
    (hhdr2 3 (by omega)).trans hcnt1, (hhdr2 0 (by omega)).trans hkey1,
    fun i hi => by rw [hfp2] at hi; exact hfp1 i hi,
    hword, ?_, hfr, ht, hloc, hgl, hnt1, hres1, heq1_fst, heq1_snd⟩
  intro off' hoff'_hi hoff'_ne
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hk64 : pw.toNat + off' < 2 ^ 64 := by have := hAR.2.2.1; omega
  rw [hother (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      rcases List.mem_singleton.1 hj with rfl
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem decCall_lst_new_store_bal_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off eszw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hesz_pos : 1 ≤ eszw.toNat)
    (hmul_lt : eszw.toNat * capw.toNat < 2 ^ 64)
    (hmul_al : (eszw.toNat * capw.toNat) % 8 = 0)
    (hcap_pos : 1 ≤ capw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "l") .one (ofString "lst_new") [.const eszw, .const capw]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "l"))) cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "l") .one (ofString "lst_new") [.const eszw, .const capw]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "l"))) cont))).1) :
    ∃ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" ∧
      lw.toNat % 8 = 0 ∧ lw.toNat ≠ 0 ∧
      globN mid "heap_ptr" = lw.toNat + 24 + eszw.toNat * capw.toNat ∧
      globN s "heap_ptr" < globN mid "heap_ptr" ∧
      ArenaReady mid ∧ mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      LstOK mid lw.toNat ∧
      lstObjects mid lw.toNat eszw.toNat =
        [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] ∧
      Disj (lw.toNat, 24) (lw.toNat + 24, eszw.toNat * capw.toNat) ∧
      (∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
        Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = lw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 40 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "l") = some (.val (.word lw)) ∧
      (∀ y, y ≠ ofString "l" → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "l") .one (ofString "lst_new") [.const eszw, .const capw]
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "l"))) cont))).1 = (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "l") .one (ofString "lst_new") [.const eszw, .const capw]
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "l"))) cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals
            (ofString "l", s.locals.lookup (ofString "l")) } := by
  obtain ⟨lw, m1, hlw_eq, hlw8, hlw_nz, hm0, hm8, hm16, hhp_m1, hhp_lt,
    hA1, hbe1, hsp1, hfmp1, hlst1, hobjs1, hdisj1, hobjs_p1, hfr1,
    hl, hloc, hgl, hnt1, hres1, heq1_fst, heq1_snd⟩ :=
    decCall_lst_new_resumes s (ofString "l") eszw capw _ hAR
      hesz_pos hmul_lt hmul_al hcap_pos hnt hres
  have had1 : m1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc _ (by decide)).trans had
  have hp_hi : pw.toNat + 40 ≤ globN m1 "heap_ptr" := by omega
  obtain ⟨heq2, hA2, hword, hother, hfr2⟩ :=
    seq_store_bal_record_slot m1 pw off lw (.var .local (ofString "l")) cont
      hA1 had1 hlo hp_hi hp8 hoff8 hoff hl
  let mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word lw else m1.memory a }
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hlw24_lt : lw.toNat + 24 < 2 ^ 64 := by have := hA1.2.2.1; omega
  have hm0_mid : memW mid lw.toNat = lw.toNat + 24 := by
    rw [hother lw.toNat (by omega) (by omega)]; exact hm0
  have hm8_mid : memW mid (lw.toNat + 8) = 0 := by
    rw [hother (lw.toNat + 8) (by omega) (by omega)]; exact hm8
  have hm16_mid : memW mid (lw.toNat + 16) = capw.toNat := by
    rw [hother (lw.toNat + 16) (by omega) (by omega)]; exact hm16
  have hlst_mid : LstOK mid lw.toNat := ⟨by rw [hm16_mid]; exact hcap_pos, by rw [hm8_mid, hm16_mid]; omega⟩
  have hmul_pos : 0 < eszw.toNat * capw.toNat := Nat.mul_pos (by omega) (by omega)
  have hobjs_mid : lstObjects mid lw.toNat eszw.toNat =
      [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] := by
    unfold lstObjects
    rw [if_neg hlw_nz, hm0_mid, hm16_mid, if_neg (by omega)]
  have hobjs_p_mid : ∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
      Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr") := by
    intro i hi
    rw [hobjs_mid, ← hobjs1] at hi
    obtain ⟨hal, hw, hin⟩ := hobjs_p1 i hi
    exact ⟨hal, wordsOK_transfer hA1.1 hA2.1 hw, hin⟩
  have hfr : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnf
    exact (hfr2 a (fun _ h => by cases h) (hno _ (by simp))).trans
      (hfr1 a (fun j hj => hno j (by
        rcases List.mem_singleton.1 hj with rfl
        exact List.mem_cons_self)) hnf)
  rw [heq2] at hnt1 hres1 heq1_fst heq1_snd
  refine ⟨lw, mid, hlw_eq, hlw8, hlw_nz, hhp_m1, hhp_lt, hA2, hbe1, hsp1,
    hlst_mid, hobjs_mid, hdisj1, hobjs_p_mid, hword, ?_, hfr, hl, hloc, hgl,
    hnt1, hres1, heq1_fst, heq1_snd⟩
  intro off' hoff'_hi hoff'_ne
  have hk64 : pw.toNat + off' < 2 ^ 64 := by have := hAR.2.2.1; omega
  rw [hother (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      rcases List.mem_singleton.1 hj with rfl
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem seq_lst_new_store_bal_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off eszw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hesz_pos : 1 ≤ eszw.toNat)
    (hmul_lt : eszw.toNat * capw.toNat < 2 ^ 64)
    (hmul_al : (eszw.toNat * capw.toNat) % 8 = 0)
    (hcap_pos : 1 ≤ capw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new")
        [.const eszw, .const capw])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "l"))) cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new")
        [.const eszw, .const capw])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "l"))) cont))).1) :
    ∃ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" ∧
      lw.toNat % 8 = 0 ∧ lw.toNat ≠ 0 ∧
      globN mid "heap_ptr" = lw.toNat + 24 + eszw.toNat * capw.toNat ∧
      globN s "heap_ptr" < globN mid "heap_ptr" ∧
      ArenaReady mid ∧ mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      LstOK mid lw.toNat ∧
      lstObjects mid lw.toNat eszw.toNat =
        [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] ∧
      Disj (lw.toNat, 24) (lw.toNat + 24, eszw.toNat * capw.toNat) ∧
      (∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
        Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = lw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 40 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "l") = some (.val (.word lw)) ∧
      (∀ y, y ≠ ofString "l" → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new")
          [.const eszw, .const capw])
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "l"))) cont)) = evaluateHOLFiniteState mid cont := by
  obtain ⟨lw, m1, hlw_eq, hlw8, hlw_nz, hm0, hm8, hm16, hhp_m1, hhp_lt,
    hA1, hbe1, hsp1, hfmp1, hlst1, hobjs1, hdisj1, hobjs_p1, hfr1,
    hl, hloc, hgl, hnt1, hres1, heq1⟩ :=
    seq_call_lst_new_local_resumes s (ofString "l") eszw capw _ hAR
      hesz_pos hmul_lt hmul_al hcap_pos hnt hres
  have had1 : m1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc _ (by decide)).trans had
  have hp_hi : pw.toNat + 40 ≤ globN m1 "heap_ptr" := by omega
  obtain ⟨heq2, hA2, hword, hother, hfr2⟩ :=
    seq_store_bal_record_slot m1 pw off lw (.var .local (ofString "l")) cont
      hA1 had1 hlo hp_hi hp8 hoff8 hoff hl
  let mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word lw else m1.memory a }
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hm0_mid : memW mid lw.toNat = lw.toNat + 24 := by
    rw [hother lw.toNat (by omega) (by have := hA1.2.2.1; omega)]; exact hm0
  have hm8_mid : memW mid (lw.toNat + 8) = 0 := by
    rw [hother (lw.toNat + 8) (by omega) (by have := hA1.2.2.1; omega)]; exact hm8
  have hm16_mid : memW mid (lw.toNat + 16) = capw.toNat := by
    rw [hother (lw.toNat + 16) (by omega) (by have := hA1.2.2.1; omega)]; exact hm16
  have hlst_mid : LstOK mid lw.toNat := ⟨by rw [hm16_mid]; exact hcap_pos, by rw [hm8_mid, hm16_mid]; omega⟩
  have hmul_pos : 0 < eszw.toNat * capw.toNat := Nat.mul_pos (by omega) (by omega)
  have hobjs_mid : lstObjects mid lw.toNat eszw.toNat =
      [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] := by
    unfold lstObjects
    rw [if_neg hlw_nz, hm0_mid, hm16_mid, if_neg (by omega)]
  have hobjs_p_mid : ∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
      Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr") := by
    intro i hi
    rw [hobjs_mid, ← hobjs1] at hi
    obtain ⟨hal, hw, hin⟩ := hobjs_p1 i hi
    exact ⟨hal, wordsOK_transfer hA1.1 hA2.1 hw, hin⟩
  have hfr : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnf
    exact (hfr2 a (fun _ h => by cases h) (hno _ (by simp))).trans
      (hfr1 a (fun j hj => hno j (by
        rcases List.mem_singleton.1 hj with rfl
        exact List.mem_cons_self)) hnf)
  rw [heq2] at hnt1 hres1
  refine ⟨lw, mid, hlw_eq, hlw8, hlw_nz, hhp_m1, hhp_lt, hA2, hbe1, hsp1,
    hlst_mid, hobjs_mid, hdisj1, hobjs_p_mid, hword, ?_, hfr, hl, hloc, hgl,
    hnt1, hres1, heq1.trans heq2⟩
  intro off' hoff'_hi hoff'_ne
  have hk64 : pw.toNat + off' < 2 ^ 64 := by have := hAR.2.2.1; omega
  rw [hother (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      rcases List.mem_singleton.1 hj with rfl
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem mem_worldRoleSlots_recRole {F : Type} (s : PanSemStateFiniteExact 64 F)
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

private theorem slot_ne_of_diff_nonshared_role {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hroles : RolesOK s S (worldRoleSlots s) (journalRoleSlots s))
    {t1 t2 : Nat} {r1 r2 : String}
    (h1 : (t1, r1) ∈ worldRoleSlots s) (h2 : (t2, r2) ∈ worldRoleSlots s)
    (hne_r : r1 ≠ r2) : t1 ≠ t2 := by
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

private theorem bal_accounts_role_props {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) (hnz : globN s "bal_accounts" ≠ 0) :
    let t0 := globN s "bal_accounts"
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  dsimp only
  set t0 := globN s "bal_accounts"
  have ht0_S : t0 ∈ S := by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hm
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht0_wrs : (t0, "bal_accounts") ∈ worldRoleSlots s := by
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [t0, hnz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_append_right _ (by simp [t0])
  refine ⟨ht0_S, ?_, ?_, ?_, ?_⟩
  · intro hbs h_eq
    have hw_wrs : (memW s (globN s "bs" + 32), "bs+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "bs" 32 "bs+32" hbs (by rw [h_eq]; exact hnz)
      apply List.mem_append_left; apply List.mem_append_right
      simp [recRoles, hbs]
    exact slot_ne_of_diff_nonshared_role hroles hw_wrs ht0_wrs (by decide) h_eq
  · intro hts h_eq
    have hw_wrs : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts (by rw [h_eq]; exact hnz)
      apply List.mem_append_right
      simp [recRoles, hts]
    exact slot_ne_of_diff_nonshared_role hroles hw_wrs ht0_wrs (by decide) h_eq
  · intro ad had h_eq
    have had_wrs : (memW s ad, "bal.stor") ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [h_eq, hnz]⟩
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had, by simp⟩)
    exact slot_ne_of_diff_nonshared_role hroles had_wrs ht0_wrs (by decide) h_eq
  · intro hws h_eq
    have hw_wrs : (memW s (globN s "ws" + 32), "ws+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ws" 32 "ws+32" hws (by rw [h_eq]; exact hnz)
      apply List.mem_append_left; apply List.mem_append_left
      simp [recRoles, hws]
    exact slot_ne_of_diff_nonshared_role hroles hw_wrs ht0_wrs (by decide) h_eq

private theorem old_balAccount_congr_of_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i)
    (ht0_not_ad : ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    {ad : Nat} (had : ad ∈ balRecords s) :
    ((ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
      lstObjects post (memW post (ad + 24)) 16 ++
      lstObjects post (memW post (ad + 32)) 24 ++
      (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
    (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
      lstObjects s (memW s (ad + 24)) 16 ++
      lstObjects s (memW s (ad + 32)) 24 ++
      (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)) ∧
    memW post ad = memW s ad ∧
    memW post (ad + 8) = memW s (ad + 8) ∧
    htabValues post (memW post ad) = htabValues s (memW s ad) ∧
    (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
    (∀ l ∈ htabValues post (memW post ad), LstOK post l) := by
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have had_bal : (ad, 40) ∈ balObjects s := by
    unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
  · simp at h0
  have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hA hal_ad).2
  have had8 : ad % 8 = 0 := hw_ad.1
  have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
      exact Wave8Contracts.M08.memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
  have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
  have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
    Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 (ht0_not_ad ad had))
  have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
      memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
    intro l hl_bal
    rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
    · simp at h0
    have hhi_l := (Wave8Contracts.M08.ivl_allocated_bound hA hal_l).2
    have hl8 : l % 8 = 0 := hw_l.1
    have hul := hu_bal _ hl_bal (by simp)
    refine ⟨?_, ?_, ?_⟩
    · simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    · exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    · exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
  have hklst : ∀ k ∈ ([16, 24, 32] : List Nat),
      memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
      memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
      memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16) := by
    intro k hk
    by_cases hk0 : memW s (ad + k) = 0
    · simp [hk0, hm0.1, hm0.2.1, hm0.2.2]
    · apply hlst_eq
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hk0]
  have hllst : ∀ l ∈ htabValues s (memW s ad),
      memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
    intro l hl
    by_cases hl0 : l = 0
    · subst hl0; simp [hm0.1, hm0.2.1, hm0.2.2]
    · apply hlst_eq
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      apply List.mem_cons_of_mem
      apply List.mem_append.2; right
      exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hl0]⟩
  have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
  have h8 := hoff_eq 8 (by simp)
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
  refine ⟨?_, h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
  · rw [htail, h16, h24, h32]
    simp [lstObjects, hk16_0, hk16_16, hk24_0, hk24_16, hk32_0, hk32_16]
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

private theorem frameOutside_keep_absorb_fresh {F : Type}
    {a b c : PanSemStateFiniteExact 64 F} {sp pw : Nat}
    (hpw_in : pw = globN a "heap_ptr" ∧ pw + 40 ≤ globN b "heap_ptr")
    (hhb : globN b "heap_ptr" ≤ globN c "heap_ptr")
    (h1 : FrameOutside a b [(sp, 0)] (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr"))
    (h2 : FrameOutside b c [(sp, 0), (pw, 40)] (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr")) :
    FrameOutside a c [(sp, 0)] (globN a "heap_ptr", globN c "heap_ptr" - globN a "heap_ptr") := by
  intro x hno hnf
  have hnf1 : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnf ⟨c1, by dsimp only; omega⟩
  have hnf2 : ¬ CellHits x.toNat (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnf ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hno2 : ∀ j ∈ ([(sp, 0), (pw, 40)] : List Ivl), ¬ CellHits x.toNat j := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hno _ (by simp)
    · intro ⟨c1, c2⟩; dsimp only at c1 c2
      exact hnf ⟨by dsimp only; omega, by dsimp only; omega⟩
  exact (h2 x hno2 hnf2).trans (h1 x hno hnf1)

private theorem ivlUnhit_of_fresh_sub {F : Type}
    {a b c : PanSemStateFiniteExact 64 F} {sp pw : Nat} {i : Ivl}
    (hbA : ArenaOK b) (hcA : ArenaOK c)
    (hi_in : Inside i (globN a "heap_ptr") (globN b "heap_ptr"))
    (hhb : globN b "heap_ptr" ≤ globN c "heap_ptr")
    (hsp8 : sp % 8 = 0)
    (hpw_hi : pw + 40 ≤ globN a "heap_ptr") (hpw8 : pw % 8 = 0)
    (hfr : FrameOutside b c [(sp, 0), (pw, 40)] (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr")) :
    M08IvlUnhit b c i := by
  intro x hx8 hx1 hx2
  apply hfr x
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact Wave8Contracts.M08.not_cellHits_of_disj hx8 hsp8 ⟨hx1, hx2⟩ (Or.inr (Or.inl rfl))
    · exact Wave8Contracts.M08.not_cellHits_of_disj hx8 hpw8 ⟨hx1, hx2⟩
        (Or.inr (Or.inr (Or.inr (by have := hi_in.1; omega))))
  · exact Wave8Contracts.M08.not_cellHits_of_disj hx8 hbA.2.2.2.2.2.1 ⟨hx1, hx2⟩
      (Or.inr (Or.inr (Or.inl (by have := hi_in.2; dsimp; omega))))

private theorem lstOK_objects_transfer_unhit {F : Type}
    {s0 b c : PanSemStateFiniteExact 64 F} {lw esz cap : Nat}
    (hb : ArenaReady b) (hc : ArenaReady c)
    (hlw8 : lw % 8 = 0) (hlw_nz : lw ≠ 0) (hcap : 1 ≤ cap) (hesz : 1 ≤ esz)
    (hlw_hi : lw + 24 ≤ globN b "heap_ptr")
    (hu : M08IvlUnhit b c (lw, 24))
    (hlst_b : LstOK b lw)
    (hobjs_b : lstObjects b lw esz = [(lw, 24), (lw + 24, esz * cap)])
    (hp_b : ∀ i ∈ lstObjects b lw esz, Inside i (globN s0 "heap_ptr") (globN b "heap_ptr") ∧ WordsOK b i)
    (hs0_lo : sourceBase ≤ globN s0 "heap_ptr")
    (hhb : globN b "heap_ptr" ≤ globN c "heap_ptr") :
    LstOK c lw ∧
    lstObjects c lw esz = [(lw, 24), (lw + 24, esz * cap)] ∧
    (∀ i ∈ lstObjects c lw esz, Allocated c i ∧ WordsOK c i ∧
      Inside i (globN s0 "heap_ptr") (globN b "heap_ptr")) := by
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hb_lim := hb.2.2.1
  have hm0 : memW c lw = memW b lw := by
    simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hu hlw8 (by omega) ⟨by omega, by omega⟩
  have hm8 : memW c (lw + 8) = memW b (lw + 8) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu (by omega) (by omega) ⟨by omega, by omega⟩
  have hm16 : memW c (lw + 16) = memW b (lw + 16) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu (by omega) (by omega) ⟨by omega, by omega⟩
  have hlst_c : LstOK c lw := by
    unfold LstOK at hlst_b ⊢; rw [hm8, hm16]; exact hlst_b
  have hobjs_c : lstObjects c lw esz = [(lw, 24), (lw + 24, esz * cap)] := by
    have heq : lstObjects c lw esz = lstObjects b lw esz := by
      unfold lstObjects; rw [hm0, hm16]
    exact heq.trans hobjs_b
  refine ⟨hlst_c, hobjs_c, fun i hi => ?_⟩
  rw [hobjs_c, ← hobjs_b] at hi
  obtain ⟨hin, hw⟩ := hp_b i hi
  exact ⟨Or.inl ⟨le_trans hs0_lo hin.1, le_trans hin.2 hhb⟩, wordsOK_transfer hb.1 hc.1 hw, hin⟩

private def balEnsureAllocProg : ProgHOL 64 :=
  .decCall (ofString "ad") .one (ofString "alloc") [.const 40#64]
    (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const 0#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 32#64, .const 8#64])
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const 8#64]) (.var .local (ofString "t")))
      (.decCall (ofString "l") .one (ofString "lst_new") [.const 40#64, .const 4#64]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const 16#64]) (.var .local (ofString "l")))
        (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new") [.const 16#64, .const 4#64])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const 24#64]) (.var .local (ofString "l")))
        (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new") [.const 24#64, .const 2#64])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const 32#64]) (.var .local (ofString "l")))
        (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .global (ofString "bal_accounts"), .var .local (ofString "addr"), .var .local (ofString "ad")])
          (.return (.var .local (ofString "ad"))))))))))))))

private theorem balEnsureAlloc_eval {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw addrw : BitVec 64)
    (hAR : ArenaReady s)
    (hroot : s.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)))
    (haddr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)))
    (htnz : tw.toNat ≠ 0)
    (hWF_tw : HtabWF s tw.toNat)
    (hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hnt : (evaluateHOLFiniteState s balEnsureAllocProg).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s balEnsureAllocProg).1) :
    ∃ (pw t0w t8w l16w l24w l32w : BitVec 64) (s1 s5 mid : PanSemStateFiniteExact 64 F),
      pw.toNat = globN s "heap_ptr" ∧
      pw.toNat % 8 = 0 ∧ pw.toNat ≠ 0 ∧
      pw.toNat + 40 ≤ t0w.toNat ∧
      t0w.toNat + 88 ≤ globN s1 "heap_ptr" ∧
      globN s1 "heap_ptr" ≤ t8w.toNat ∧
      t8w.toNat + 88 ≤ l16w.toNat ∧
      l16w.toNat + 24 + 160 = l24w.toNat ∧
      l24w.toNat + 24 + 64 = l32w.toNat ∧
      l32w.toNat + 24 + 48 = globN s5 "heap_ptr" ∧
      ArenaReady s5 ∧ s5.be = s.be ∧
      globN s5 "scratch_ptr" = globN s "scratch_ptr" ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = s5.globals.lookup k) ∧
      FrameOutside s s5 [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN s5 "heap_ptr" - globN s "heap_ptr") ∧
      HtabWF s5 t0w.toNat ∧ hdr s5 t0w.toNat 3 = 0 ∧ hdr s5 t0w.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr")) ∧
      HtabWF s5 t8w.toNat ∧ hdr s5 t8w.toNat 3 = 0 ∧ hdr s5 t8w.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat) ∧
      (∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
        t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j) ∧
      memW s5 pw.toNat = t0w.toNat ∧
      memW s5 (pw.toNat + 8) = t8w.toNat ∧
      memW s5 (pw.toNat + 16) = l16w.toNat ∧
      memW s5 (pw.toNat + 24) = l24w.toNat ∧
      memW s5 (pw.toNat + 32) = l32w.toNat ∧
      LstOK s5 l16w.toNat ∧ lstObjects s5 l16w.toNat 40 = [(l16w.toNat, 24), (l16w.toNat + 24, 160)] ∧
      LstOK s5 l24w.toNat ∧ lstObjects s5 l24w.toNat 16 = [(l24w.toNat, 24), (l24w.toNat + 24, 64)] ∧
      LstOK s5 l32w.toNat ∧ lstObjects s5 l32w.toNat 24 = [(l32w.toNat, 24), (l32w.toNat + 24, 48)] ∧
      SoloHtabSet.HtabExitAt tw.toNat s5 mid ∧
      HtabSetValuesPost s5 mid tw.toNat pw.toNat ∧
      mid.be = s5.be ∧ pw.toNat ∈ balRecords mid ∧
      (evaluateHOLFiniteState s balEnsureAllocProg).1 = some (.returned (.val (.word pw))) ∧
      ∃ L_out, (evaluateHOLFiniteState s balEnsureAllocProg).2 =
        { mid with locals := L_out } := by
  unfold balEnsureAllocProg at hnt hres ⊢
  have hsp8 : (globN s "scratch_ptr") % 8 = 0 := hAR.2.2.2.2.2.2.2.2.1
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have hsb_pos : 0 < sourceBase := by decide
  obtain ⟨pw, qw, s0, hpw_eq, hqw_eq, hqw_lim, hpw_le_qw, hpw8, _, hhp_s0, hsp_s0, _,
    hA0, hmem0, _, hbe0, _, had0, hloc0, hgl0, hnt0, hres0, heq0_fst, heq0_snd⟩ :=
    decCall_alloc_resumes s (ofString "ad") (.const 40#64) 40#64 _ hAR
      (by simp [evalHOLExact]) hnt hres
  have hhp_s0' : globN s0 "heap_ptr" = pw.toNat + 40 := by
    rw [hhp_s0, hqw_eq]
    rfl
  have hpw_lo : sourceBase ≤ pw.toNat := by omega
  have hpw_nz : pw.toNat ≠ 0 := by omega
  have hfr_s_s0 : FrameOutside s s0 [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN s0 "heap_ptr" - globN s "heap_ptr") :=
    fun a _ _ => by rw [hmem0]
  obtain ⟨t0w, s1, ht0_lo, ht0_hi, hA1, hbe1, hsp1, hwf_t0_1, hcnt_t0_1, hkey_t0_1,
    hfp_t0_1, hm0_1, _, hfr01, _, hloc1, hgl1, hnt1, hres1, heq1_fst, heq1_snd⟩ :=
    decCall_htab_new_store_bal_slot s0 pw 0#64 _ hA0 had0 hpw_lo (by omega) hpw8
      (by decide) (by decide) hnt0 hres0
  have had1 : s1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc1 _ (by decide)).trans had0
  have hsp1' : globN s1 "scratch_ptr" = globN s "scratch_ptr" := hsp1.trans hsp_s0
  obtain ⟨t8w, s2, ht8_lo, ht8_hi, hA2, hbe2, hsp2, hwf_t8_2, hcnt_t8_2, hkey_t8_2,
    hfp_t8_2, hm8_2, hoth2, hfr12, _, hloc2, hgl2, hnt2, hres2, heq2⟩ :=
    seq_htab_new_store_bal_slot s1 pw 8#64 _ hA1 had1 hpw_lo (by omega) hpw8
      (by decide) (by decide) hnt1 hres1
  have had2 : s2.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc2 _ (by decide)).trans had1
  have hsp2' : globN s2 "scratch_ptr" = globN s "scratch_ptr" := hsp2.trans hsp1'
  obtain ⟨l16w, s3, hl16_eq, hl16_8, hl16_nz, hhp_s3, hlt_23, hA3, hbe3, hsp3,
    hlst16_3, hobjs16_3, _, hp16_3, hm16_3, hoth3, hfr23, _, hloc3, hgl3, hnt3, hres3,
    heq3_fst, heq3_snd⟩ :=
    decCall_lst_new_store_bal_slot s2 pw 16#64 40#64 4#64 _ hA2 had2 hpw_lo (by omega) hpw8
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hnt2 hres2
  have had3 : s3.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc3 _ (by decide)).trans had2
  have hsp3' : globN s3 "scratch_ptr" = globN s "scratch_ptr" := hsp3.trans hsp2'
  obtain ⟨l24w, s4, hl24_eq, hl24_8, hl24_nz, hhp_s4, hlt_34, hA4, hbe4, hsp4,
    hlst24_4, hobjs24_4, _, hp24_4, hm24_4, hoth4, hfr34, _, hloc4, hgl4, hnt4, hres4, heq4⟩ :=
    seq_lst_new_store_bal_slot s3 pw 24#64 16#64 4#64 _ hA3 had3 hpw_lo (by omega) hpw8
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hnt3 hres3
  have had4 : s4.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc4 _ (by decide)).trans had3
  have hsp4' : globN s4 "scratch_ptr" = globN s "scratch_ptr" := hsp4.trans hsp3'
  obtain ⟨l32w, s5, hl32_eq, hl32_8, hl32_nz, hhp_s5, hlt_45, hA5, hbe5, hsp5,
    hlst32_5, hobjs32_5, _, hp32_5, hm32_5, hoth5, hfr45, _, hloc5, hgl5, hnt5, hres5, heq5⟩ :=
    seq_lst_new_store_bal_slot s4 pw 32#64 24#64 2#64 _ hA4 had4 hpw_lo (by omega) hpw8
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hnt4 hres4
  have had5 : s5.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc5 _ (by decide)).trans had4
  have haddr5 : s5.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
    rw [hloc5 _ (by decide), hloc4 _ (by decide), hloc3 _ (by decide),
        hloc2 _ (by decide), hloc1 _ (by decide), hloc0 _ (by decide)]
    exact haddr
  have hsp5' : globN s5 "scratch_ptr" = globN s "scratch_ptr" := hsp5.trans hsp4'
  have hgl_s5 : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = s5.globals.lookup k :=
    fun k hk => (hgl0 k hk).trans ((hgl1 k hk).trans ((hgl2 k hk).trans
      ((hgl3 k hk).trans ((hgl4 k hk).trans (hgl5 k hk)))))
  have hbe_s5 : s5.be = s.be := hbe5.trans (hbe4.trans (hbe3.trans (hbe2.trans (hbe1.trans hbe0))))
  -- Arithmetic on fresh bounds
  have hc16 : (40#64 : BitVec 64).toNat * (4#64 : BitVec 64).toNat = 160 := rfl
  have hc24 : (16#64 : BitVec 64).toNat * (4#64 : BitVec 64).toNat = 64 := rfl
  have hc32 : (24#64 : BitVec 64).toNat * (2#64 : BitVec 64).toNat = 48 := rfl
  have hesz40 : (40#64 : BitVec 64).toNat = 40 := rfl
  have hesz16 : (16#64 : BitVec 64).toNat = 16 := rfl
  have hesz24 : (24#64 : BitVec 64).toNat = 24 := rfl
  rw [hc16] at hhp_s3 hobjs16_3
  rw [hc24] at hhp_s4 hobjs24_4
  rw [hc32] at hhp_s5 hobjs32_5
  rw [hesz40] at hobjs16_3 hp16_3
  rw [hesz16] at hobjs24_4 hp24_4
  rw [hesz24] at hobjs32_5 hp32_5
  have ho0 : (0#64 : BitVec 64).toNat = 0 := rfl
  have ho8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have ho16 : (16#64 : BitVec 64).toNat = 16 := rfl
  have ho24 : (24#64 : BitVec 64).toNat = 24 := rfl
  have ho32 : (32#64 : BitVec 64).toNat = 32 := rfl
  rw [ho0, Nat.add_zero] at hm0_1
  rw [ho8] at hm8_2 hoth2
  rw [ho16] at hm16_3 hoth3
  rw [ho24] at hm24_4 hoth4
  rw [ho32] at hm32_5 hoth5
  -- Compose FrameOutside s1..s5 with [(sp, 0), (pw, 40)] and absorb into FrameOutside s..s5
  rw [hsp_s0] at hfr01
  rw [hsp1'] at hfr12
  rw [hsp2'] at hfr23
  rw [hsp3'] at hfr34
  rw [hsp4'] at hfr45
  have hfr_s_s1 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s0 hfr01
  have hfr_s_s2 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s1 hfr12
  have hfr_s_s3 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s2 hfr23
  have hfr_s_s4 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s3 hfr34
  have hfr_s_s5 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s4 hfr45
  -- Transfer tw HtabWF from s to s5
  have hu_tw_s5 : ∀ i ∈ htabFootprint s tw.toNat, M08IvlUnhit s s5 i := fun i hi =>
    ivlUnhit_of_allocated_heap_sp0 hAR.2 hA5.2 (hal_tw i hi)
      (fun j hj => by rcases List.mem_singleton.1 hj with rfl; exact ⟨_, rfl, hsp8⟩)
      hfr_s_s5
  have hag_s_s5 : AllocatorGrows s s5 := ⟨by omega, by rw [hsp5']⟩
  obtain ⟨hwf_tw_5, hfp_tw_eq, _⟩ := htabWF_transfer_unhit hAR hA5 hWF_tw hu_tw_s5
    (fun i hi => hag_s_s5.allocated (hal_tw i hi))
  have hal_tw_5 : ∀ i ∈ htabFootprint s5 tw.toNat, Allocated s5 i := by
    rw [hfp_tw_eq]; exact fun i hi => hag_s_s5.allocated (hal_tw i hi)
  have hroot5 : s5.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)) :=
    (hgl_s5 _ (by decide)).symm.trans hroot
  -- Execute final htab_set + return
  obtain ⟨mid, hexit, hvalues, hbe_mid, _, hmem_rec, heval_ins⟩ :=
    bal_ensure_insert_return s5 tw addrw pw hA5 hroot5 haddr5 had5 htnz hwf_tw_5 hal_tw_5 hnt5 hres5
  -- Compose sub-frames across intermediate steps (for preserving t0w, t8w, l16w, l24w, pw slots)
  have hfr_1_5 : FrameOutside s1 s5 [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s1 "heap_ptr", globN s5 "heap_ptr" - globN s1 "heap_ptr") := by
    intro x hno hnf
    have hnf12 : ¬ CellHits x.toNat (globN s1 "heap_ptr", globN s2 "heap_ptr" - globN s1 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨c1, by dsimp at c1 c2 ⊢; omega⟩
    have hnf23 : ¬ CellHits x.toNat (globN s2 "heap_ptr", globN s3 "heap_ptr" - globN s2 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    have hnf34 : ¬ CellHits x.toNat (globN s3 "heap_ptr", globN s4 "heap_ptr" - globN s3 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    have hnf45 : ¬ CellHits x.toNat (globN s4 "heap_ptr", globN s5 "heap_ptr" - globN s4 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    exact (hfr45 x hno hnf45).trans ((hfr34 x hno hnf34).trans
      ((hfr23 x hno hnf23).trans (hfr12 x hno hnf12)))
  have hfr_2_5 : FrameOutside s2 s5 [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s2 "heap_ptr", globN s5 "heap_ptr" - globN s2 "heap_ptr") := by
    intro x hno hnf
    have hnf23 : ¬ CellHits x.toNat (globN s2 "heap_ptr", globN s3 "heap_ptr" - globN s2 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨c1, by dsimp at c1 c2 ⊢; omega⟩
    have hnf34 : ¬ CellHits x.toNat (globN s3 "heap_ptr", globN s4 "heap_ptr" - globN s3 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    have hnf45 : ¬ CellHits x.toNat (globN s4 "heap_ptr", globN s5 "heap_ptr" - globN s4 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    exact (hfr45 x hno hnf45).trans ((hfr34 x hno hnf34).trans (hfr23 x hno hnf23))
  have hfr_3_5 : FrameOutside s3 s5 [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s3 "heap_ptr", globN s5 "heap_ptr" - globN s3 "heap_ptr") := by
    intro x hno hnf
    have hnf34 : ¬ CellHits x.toNat (globN s3 "heap_ptr", globN s4 "heap_ptr" - globN s3 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨c1, by dsimp at c1 c2 ⊢; omega⟩
    have hnf45 : ¬ CellHits x.toNat (globN s4 "heap_ptr", globN s5 "heap_ptr" - globN s4 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    exact (hfr45 x hno hnf45).trans (hfr34 x hno hnf34)
  -- Transfer t0w from s1 to s5
  have hu_t0 : ∀ i ∈ htabFootprint s1 t0w.toNat, M08IvlUnhit s1 s5 i := fun i hi =>
    ivlUnhit_of_fresh_sub (a := s0) hA1.2 hA5.2 (hfp_t0_1 i hi).2 (by omega) hsp8 (by omega) hpw8 hfr_1_5
  have hag_1_5 : AllocatorGrows s1 s5 := ⟨by omega, by rw [hsp5', hsp1']⟩
  obtain ⟨hwf_t0_5, hfp_t0_eq, hhdr_t0_5⟩ := htabWF_transfer_unhit hA1 hA5 hwf_t0_1 hu_t0
    (fun i hi => hag_1_5.allocated (hfp_t0_1 i hi).1)
  have hcnt_t0_5 : hdr s5 t0w.toNat 3 = 0 := (hhdr_t0_5 3 (by omega)).trans hcnt_t0_1
  have hkey_t0_5 : hdr s5 t0w.toNat 0 = 32 := (hhdr_t0_5 0 (by omega)).trans hkey_t0_1
  have hfp_t0_5 : ∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr") := by
    rw [hfp_t0_eq]
    intro i hi
    obtain ⟨hal, hin⟩ := hfp_t0_1 i hi
    exact ⟨hag_1_5.allocated hal, ⟨by have := hin.1; omega, hin.2⟩⟩
  -- Transfer t8w from s2 to s5
  have hu_t8 : ∀ i ∈ htabFootprint s2 t8w.toNat, M08IvlUnhit s2 s5 i := fun i hi =>
    ivlUnhit_of_fresh_sub (a := s1) hA2.2 hA5.2 (hfp_t8_2 i hi).2 (by omega) hsp8 (by omega) hpw8 hfr_2_5
  have hag_2_5 : AllocatorGrows s2 s5 := ⟨by omega, by rw [hsp5', hsp2']⟩
  obtain ⟨hwf_t8_5, hfp_t8_eq, hhdr_t8_5⟩ := htabWF_transfer_unhit hA2 hA5 hwf_t8_2 hu_t8
    (fun i hi => hag_2_5.allocated (hfp_t8_2 i hi).1)
  have hcnt_t8_5 : hdr s5 t8w.toNat 3 = 0 := (hhdr_t8_5 3 (by omega)).trans hcnt_t8_2
  have hkey_t8_5 : hdr s5 t8w.toNat 0 = 32 := (hhdr_t8_5 0 (by omega)).trans hkey_t8_2
  have hfp_t8_5 : ∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat := by
    rw [hfp_t8_eq]
    intro i hi
    obtain ⟨hal, hin⟩ := hfp_t8_2 i hi
    exact ⟨hag_2_5.allocated hal, ⟨hin.1, by have := hin.2; omega⟩⟩
  have hpw_tabs : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j := by
    intro t ht u hu hne i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
    · exact absurd rfl hne
    · exact disj_fresh_sub (hfp_t0_5 i hi).2 (hfp_t8_5 j hj).2 le_rfl
    · exact disj_flip (disj_fresh_sub (hfp_t0_5 j hj).2 (hfp_t8_5 i hi).2 le_rfl)
    · exact absurd rfl hne
  -- Transfer l16w from s3 to s5, and l24w from s4 to s5
  have hu_l16 : M08IvlUnhit s3 s5 (l16w.toNat, 24) :=
    ivlUnhit_of_fresh_sub (a := s2) hA3.2 hA5.2 ⟨by omega, by omega⟩ (by omega) hsp8 (by omega) hpw8 hfr_3_5
  obtain ⟨hlst16_5, hobjs16_5, _⟩ := lstOK_objects_transfer_unhit (s0 := s2) (lw := l16w.toNat) (esz := 40) (cap := 4)
    hA3 hA5 hl16_8 hl16_nz (by decide) (by decide) (by omega) hu_l16 hlst16_3 hobjs16_3
    (fun i hi => ⟨(hp16_3 i hi).2.2, (hp16_3 i hi).2.1⟩) hA2.2.1 (by omega)
  have hu_l24 : M08IvlUnhit s4 s5 (l24w.toNat, 24) :=
    ivlUnhit_of_fresh_sub (a := s3) hA4.2 hA5.2 ⟨by omega, by omega⟩ (by omega) hsp8 (by omega) hpw8 hfr45
  obtain ⟨hlst24_5, hobjs24_5, _⟩ := lstOK_objects_transfer_unhit (s0 := s3) (lw := l24w.toNat) (esz := 16) (cap := 4)
    hA4 hA5 hl24_8 hl24_nz (by decide) (by decide) (by omega) hu_l24 hlst24_4 hobjs24_4
    (fun i hi => ⟨(hp24_4 i hi).2.2, (hp24_4 i hi).2.1⟩) hA3.2.1 (by omega)
  -- Slot values at pw + 0, 8, 16, 24, 32 in s5
  have hm0_5 : memW s5 pw.toNat = t0w.toNat := by
    have h0 := (hoth5 0 (by omega) (by omega)).trans ((hoth4 0 (by omega) (by omega)).trans
      ((hoth3 0 (by omega) (by omega)).trans (hoth2 0 (by omega) (by omega))))
    simpa using h0.trans hm0_1
  have hm8_5 : memW s5 (pw.toNat + 8) = t8w.toNat :=
    ((hoth5 8 (by omega) (by omega)).trans ((hoth4 8 (by omega) (by omega)).trans
      (hoth3 8 (by omega) (by omega)))).trans hm8_2
  have hm16_5 : memW s5 (pw.toNat + 16) = l16w.toNat :=
    ((hoth5 16 (by omega) (by omega)).trans (hoth4 16 (by omega) (by omega))).trans hm16_3
  have hm24_5 : memW s5 (pw.toNat + 24) = l24w.toNat :=
    (hoth5 24 (by omega) (by omega)).trans hm24_4
  -- Chain evaluation
  have hev_fst : (evaluateHOLFiniteState s balEnsureAllocProg).1 =
      some (.returned (.val (.word pw))) := by
    unfold balEnsureAllocProg
    rw [heq0_fst, heq1_fst, heq2, heq3_fst, heq4, heq5, heval_ins]
  have hev_snd : ∃ L_out, (evaluateHOLFiniteState s balEnsureAllocProg).2 =
      { mid with locals := L_out } := by
    let L_final :=
      HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq (mid.emptyLocalsHOLFinite).locals
            (ofString "l", s2.locals.lookup (ofString "l")))
          (ofString "t", s0.locals.lookup (ofString "t")))
        (ofString "ad", s.locals.lookup (ofString "ad"))
    refine ⟨L_final, ?_⟩
    unfold balEnsureAllocProg
    rw [heq0_snd, heq1_snd, heq2, heq3_snd, heq4, heq5, heval_ins]
    rfl
  refine ⟨pw, t0w, t8w, l16w, l24w, l32w, s1, s5, mid,
    hpw_eq, hpw8, hpw_nz,
    by omega, ht0_hi, ht8_lo, by omega, by omega, by omega, hhp_s5.symm,
    hA5, hbe_s5, hsp5', hgl_s5, hfr_s_s5,
    hwf_t0_5, hcnt_t0_5, hkey_t0_5, hfp_t0_5,
    hwf_t8_5, hcnt_t8_5, hkey_t8_5, hfp_t8_5, hpw_tabs,
    hm0_5, hm8_5, hm16_5, hm24_5, hm32_5,
    hlst16_5, by simpa using hobjs16_5, hlst24_5, by simpa using hobjs24_5, hlst32_5, hobjs32_5,
    hexit, hvalues, hbe_mid, hmem_rec, hev_fst, hev_snd⟩

private theorem disj_fresh_of_zero_or_allocated_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
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

private theorem m08_ivlUnhit_of_frameOutside_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    M08IvlUnhit s post i := by
  intro a ha8 h1 h2
  apply hfr a
  · intro j hj hcj
    exact absurd hcj (Wave8Contracts.M08.not_cellHits_of_disj ha8 (hk_al j hj) ⟨h1, h2⟩ (hk j hj))
  · intro hcf
    exact absurd hcf (Wave8Contracts.M08.not_cellHits_of_disj ha8 hf_al ⟨h1, h2⟩ hf)

private theorem fixedTyped_of_balObjects_set_values_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : Nat} {fresh : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post) (hF : FixedTyped s)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s post)
    (hbo_eq : blockOutObjects post = blockOutObjects s)
    (hnz : globN s "bal_accounts" ≠ 0)
    (hval : HtabSetValuesPost s post (globN s "bal_accounts") v)
    (hold_obj : ∀ ad ∈ balRecords s,
      (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++
        lstObjects post (memW post (ad + 32)) 24 ++
        (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
      (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
        lstObjects s (memW s (ad + 24)) 16 ++
        lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40))
    (hv_obj : (v, 40) :: lstObjects post (memW post (v + 16)) 40 ++
        lstObjects post (memW post (v + 24)) 16 ++
        lstObjects post (memW post (v + 32)) 24 ++
        (htabValues post (memW post v)).flatMap (fun l => lstObjects post l 40) = fresh)
    (hfresh : ∀ i ∈ fresh,
      Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧ WordsOK post i)
    (hpw_fresh : fresh.Pairwise Disj) :
    FixedTyped post ∧
    (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr")) := by
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  obtain ⟨_, _, hbal_mem⟩ := balRecords_set_values_add hba_g hnz hval
  have hbal_class : ∀ i ∈ balObjects post, i ∈ balObjects s ∨ i ∈ fresh := by
    intro i hi
    unfold balObjects at hi
    obtain ⟨ad, had, hi_ad⟩ := List.mem_flatMap.1 hi
    rcases hbal_mem ad had with had_s | rfl
    · left
      rw [hold_obj ad had_s] at hi_ad
      unfold balObjects
      exact List.mem_flatMap.2 ⟨ad, had_s, hi_ad⟩
    · right
      rwa [hv_obj] at hi_ad
  have hprefix_eq :
      (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) ++
        [(if globN post "journal_cap" = 0 then 0 else globN post "journal", 32 * globN post "journal_cap")] ++
        blockOutObjects post =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s := by
    have hgb : (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
      apply List.map_congr_left
      intro gn hgn
      rw [hgs.1 gn hgn]
    rw [hgb, hgs.2.2.1, hgs.2.2.2.1, hbo_eq]
  have hfix_class : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o ∈ fresh := by
    intro o ho
    unfold fixedObjects at ho
    rw [hprefix_eq] at ho
    rcases List.mem_append.1 ho with hpre | hbal
    · left; unfold fixedObjects; exact List.mem_append_left _ hpre
    · rcases hbal_class o hbal with hb_s | hfr
      · left; unfold fixedObjects; exact List.mem_append_right _ hb_s
      · exact Or.inr hfr
  let objects : Nat → List Ivl := fun ad =>
    if ad = v then fresh
    else (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
      lstObjects s (memW s (ad + 24)) 16 ++
      lstObjects s (memW s (ad + 32)) 24 ++
      (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)
  have hv_not_old : v ∉ balRecords s := by
    intro hv_s
    have hv_bal : (v, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨v, hv_s, by simp⟩
    have hv_fix : (v, 40) ∈ fixedObjects s := by
      unfold fixedObjects; exact List.mem_append_right _ hv_bal
    rcases hF.1 _ hv_fix with h0 | ⟨hal_v, _⟩
    · simp at h0
    · have hv_fr : (v, 40) ∈ fresh := by rw [← hv_obj]; simp
      have hd := Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_v (hfresh _ hv_fr).1
      rcases hd with h | h | h | h <;> dsimp at h <;> omega
  have hold_eq_objects : (balRecords s).flatMap objects = balObjects s := by
    unfold balObjects
    apply List.flatMap_congr
    intro ad had
    have hne : ad ≠ v := fun heq => hv_not_old (heq ▸ had)
    simp [objects, hne]
  have hpost_objects : ∀ ad ∈ balRecords post,
      (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++
        lstObjects post (memW post (ad + 32)) 24 ++
        (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) = objects ad := by
    intro ad had
    rcases hbal_mem ad had with had_s | rfl
    · have hne : ad ≠ v := fun heq => hv_not_old (heq ▸ had_s)
      simp only [objects, if_neg hne]
      exact hold_obj ad had_s
    · simp only [objects, if_true]
      exact hv_obj
  obtain ⟨hpw_pre, hpw_bal_s, hcross_pre_bal⟩ := by
    have h := hF.2
    unfold fixedObjects at h
    exact List.pairwise_append.1 h
  have hpw_bal_post : (balObjects post).Pairwise Disj := by
    apply pairwise_balObjects_set_values_add hba_g hnz hval objects hpost_objects
    · rw [hold_eq_objects]; exact hpw_bal_s
    · simp only [objects, if_true]; exact hpw_fresh
    · intro a ha b hb
      rw [hold_eq_objects] at ha
      simp only [objects, if_true] at hb
      have ha_fix : a ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_right _ ha
      rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
      · exact Or.inl hz
      · exact disj_flip (disj_allocated_fresh_heap hAs.2 hAp.2 hal_a (hfresh b hb).1)
    · intro a ha b hb
      simp only [objects, if_true] at ha
      rw [hold_eq_objects] at hb
      have hb_fix : b ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_right _ hb
      rcases hF.1 b hb_fix with hz | ⟨hal_b, _⟩
      · exact Or.inr (Or.inl hz)
      · exact disj_allocated_fresh_heap hAs.2 hAp.2 hal_b (hfresh a ha).1
  refine ⟨⟨?_, ?_⟩, fun o ho => ?_⟩
  · intro i hi
    rcases hfix_class i hi with hold | hnew
    · rcases hF.1 i hold with hz | ⟨hal, hw⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
    · obtain ⟨hin, hw⟩ := hfresh i hnew
      exact Or.inr ⟨Or.inl ⟨le_trans hAs.2.1 hin.1, hin.2⟩, hw⟩
  · unfold fixedObjects
    rw [hprefix_eq]
    refine List.pairwise_append.2 ⟨hpw_pre, hpw_bal_post, fun a ha b hb => ?_⟩
    rcases hbal_class b hb with hb_s | hb_fr
    · exact hcross_pre_bal a ha b hb_s
    · have ha_fix : a ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_left _ ha
      rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
      · exact Or.inl hz
      · exact disj_flip (disj_allocated_fresh_heap hAs.2 hAp.2 hal_a (hfresh b hb_fr).1)
  · rcases hfix_class o ho with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inr (hfresh o hnew).1)

private theorem rolesOK_balEnsureAlloc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {v t0 t8 : Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s post)
    (hnz : globN s "bal_accounts" ≠ 0)
    (hval : HtabSetValuesPost s post (globN s "bal_accounts") v)
    (hu_other : ∀ u ∈ S, u ≠ globN s "bal_accounts" → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72))
    (hold_slots : ∀ ad ∈ balRecords s, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8))
    (hv_slots : memW post v = t0 ∧ memW post (v + 8) = t8)
    (ht0_nz : t0 ≠ 0) (ht8_nz : t8 ≠ 0) (ht08_ne : t0 ≠ t8)
    (hhdr_t0 : hdr post t0 0 = 32) (hhdr_t8 : hdr post t8 0 = 32)
    (hhdr0_S : ∀ t ∈ S, hdr post t 0 = hdr s t 0)
    (hT_disj_S : ∀ t ∈ ([t0, t8] : List Nat), t ∉ S)
    (hjr_eq : journalRoleSlots post = journalRoleSlots s) :
    RolesOK post (S ++ [t0, t8]) (worldRoleSlots post) (journalRoleSlots post) := by
  have hws_g := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbia_g := hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g := hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  obtain ⟨_, hno_bs32, hno_ts32, _, _⟩ := bal_accounts_role_props hT hnz
  have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · have hw16 := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ws" 40 (by decide) hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ws" 40 (by decide) hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
      simp only [hws_g] at hw16 hw32 ⊢
      simp [h, hw16, hw32]
  have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
    unfold recRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · simp only [hbs_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r0⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨by omega, by omega⟩
      have hw := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "bs" 80 (by decide) hbs_g h (hu_bs h) hk.1 hk.2
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
      intro ⟨k, r0⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨by omega, by omega⟩
      have hw := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ts" 72 (by decide) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw; simp [hw]
  have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "bs" 80 (by decide) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_bs32 h))]
  have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ts" 72 (by decide) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_ts32 h))]
  let nonbal_raw :=
    recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
      [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
        (globN s "bal_idx_stor", "bal_idx_stor")] ++
      nestRoles s "bs" "bs.inner" ++ nestRoles s "ts" "ts.inner"
  let bal_fn_s : Nat → List (Nat × String) := fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]
  let bal_fn_p : Nat → List (Nat × String) := fun ad => [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]
  have hold_fn : ∀ ad ∈ balRecords s, bal_fn_p ad = bal_fn_s ad := by
    intro ad had
    obtain ⟨e0, e8⟩ := hold_slots ad had
    simp [bal_fn_p, bal_fn_s, e0, e8]
  have hv_fn_f : (bal_fn_p v).filter (fun a => a.1 != 0) = [(t0, "bal.stor"), (t8, "bal.reads")] := by
    simp [bal_fn_p, hv_slots.1, hv_slots.2, ht0_nz, ht8_nz]
  obtain ⟨hrecs_or, _, _⟩ := balRecords_set_values_add hba_g hnz hval
  rw [hjr_eq]
  refine rolesOK_adjoin_fresh_slots hT.2.2.2.2.2.2.2.2.2.2.2 hhdr0_S ?_ hT_disj_S
  have hwrs_s_eq : worldRoleSlots s =
      (nonbal_raw ++ (balRecords s).flatMap bal_fn_s).filter (fun a => a.1 != 0) := rfl
  have hwrs_p_eq : worldRoleSlots post =
      (nonbal_raw ++ (balRecords post).flatMap bal_fn_p).filter (fun a => a.1 != 0) := by
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts]
  rcases hrecs_or with h_app | ⟨idx, hidx_lt, h_set⟩
  · -- Append case
    have hfm_app : (balRecords post).flatMap bal_fn_p =
        (balRecords s).flatMap bal_fn_s ++ bal_fn_p v := by
      rw [h_app, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.flatMap_congr hold_fn]
    refine ⟨worldRoleSlots s, [(t0, "bal.stor"), (t8, "bal.reads")], [], ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwrs_p_eq, hfm_app, ← List.append_assoc, List.filter_append, hv_fn_f, List.append_nil, ← hwrs_s_eq]
    · intro a ha; rw [List.append_nil] at ha; exact ha
    · rw [List.append_nil]; exact hT.2.2.2.2.2.2.2.2.2.2.2.2.1
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨by simp, hhdr_t0.trans (show 32 = roleKeyLen "bal.stor" by decide)⟩
      · exact ⟨by simp, hhdr_t8.trans (show 32 = roleKeyLen "bal.reads" by decide)⟩
    · simp [ht08_ne]
  · -- Overwrite case (`balRecords post = (balRecords s).set idx v`)
    let pre_ads := (balRecords s).take idx
    let suf_ads := (balRecords s).drop (idx + 1)
    have hsplit_s : balRecords s = pre_ads ++ (balRecords s)[idx] :: suf_ads := by
      have h1 := (List.take_append_drop idx (balRecords s)).symm
      have h2 : (balRecords s).drop idx = (balRecords s)[idx] :: (balRecords s).drop (idx + 1) :=
        List.drop_eq_getElem_cons hidx_lt
      rw [h2] at h1
      exact h1
    have hsplit_set : (balRecords s).set idx v = pre_ads ++ v :: suf_ads := by
      rw [List.set_eq_take_append_cons_drop, if_pos hidx_lt]
    have hpre_sub : ∀ ad ∈ pre_ads, ad ∈ balRecords s := fun ad had => List.mem_of_mem_take had
    have hsuf_sub : ∀ ad ∈ suf_ads, ad ∈ balRecords s := fun ad had => List.mem_of_mem_drop had
    have hfm_set : (balRecords post).flatMap bal_fn_p =
        pre_ads.flatMap bal_fn_s ++ bal_fn_p v ++ suf_ads.flatMap bal_fn_s := by
      rw [h_set, hsplit_set, List.flatMap_append, List.flatMap_cons, ← List.append_assoc]
      rw [List.flatMap_congr (fun ad had => hold_fn ad (hpre_sub ad had)),
          List.flatMap_congr (fun ad had => hold_fn ad (hsuf_sub ad had))]
    let pre_sl := (nonbal_raw ++ pre_ads.flatMap bal_fn_s).filter (fun a => a.1 != 0)
    let suf_sl := (suf_ads.flatMap bal_fn_s).filter (fun a => a.1 != 0)
    have hsub_s : (pre_sl ++ suf_sl).Sublist (worldRoleSlots s) := by
      rw [hwrs_s_eq, hsplit_s, List.flatMap_append, List.flatMap_cons]
      simp only [pre_sl, suf_sl, ← List.filter_append]
      rw [← List.append_assoc]
      apply List.Sublist.filter
      apply List.Sublist.append_left
      exact List.Sublist.append (List.nil_sublist _) (List.Sublist.refl _)
    refine ⟨pre_sl, [(t0, "bal.stor"), (t8, "bal.reads")], suf_sl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwrs_p_eq, hfm_set]
      have hassoc : nonbal_raw ++ (pre_ads.flatMap bal_fn_s ++ bal_fn_p v ++ suf_ads.flatMap bal_fn_s) =
          (nonbal_raw ++ pre_ads.flatMap bal_fn_s) ++ bal_fn_p v ++ suf_ads.flatMap bal_fn_s := by
        simp [List.append_assoc]
      rw [hassoc, filter_append_three, hv_fn_f]
    · intro a ha; exact hsub_s.subset ha
    · exact hT.2.2.2.2.2.2.2.2.2.2.2.2.1.sublist hsub_s
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨by simp, hhdr_t0.trans (show 32 = roleKeyLen "bal.stor" by decide)⟩
      · exact ⟨by simp, hhdr_t8.trans (show 32 = roleKeyLen "bal.reads" by decide)⟩
    · simp [ht08_ne]

private theorem balEnsureAlloc_worldStep_finish {F : Type}
    {s s1 s5 mid : PanSemStateFiniteExact 64 F}
    {tw pw t0w t8w l16w l24w l32w : BitVec 64}
    {S Nd : List Nat}
    (hAR : ArenaReady s) (hAm : ArenaReady mid)
    (hag : AllocatorGrows s mid)
    (hT : TablesTyped s S) (hF : FixedTyped s) (hTr : TriesTypedWith s S Nd)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s mid)
    (ht_eq : tw.toNat = globN s "bal_accounts")
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hba_S : tw.toNat ∈ S)
    (hhp_05 : globN s "heap_ptr" ≤ globN s5 "heap_ptr")
    (hhp_5m : globN s5 "heap_ptr" ≤ globN mid "heap_ptr")
    (hpw_eq : pw.toNat = globN s "heap_ptr")
    (hpw_t0 : pw.toNat + 40 ≤ t0w.toNat)
    (ht0_s1 : t0w.toNat + 88 ≤ globN s1 "heap_ptr")
    (hs1_t8 : globN s1 "heap_ptr" ≤ t8w.toNat)
    (ht8_l16 : t8w.toNat + 88 ≤ l16w.toNat)
    (hl16_l24 : l16w.toNat + 24 + 160 = l24w.toNat)
    (hl24_l32 : l24w.toNat + 24 + 64 = l32w.toNat)
    (hl32_s5 : l32w.toNat + 24 + 48 = globN s5 "heap_ptr")
    (hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr"))
    (hfp_tw_5 : htabFootprint s5 tw.toNat = htabFootprint s tw.toNat)
    (hhdr0_tw_m : hdr mid tw.toNat 0 = hdr s tw.toNat 0)
    (hwf_tw_m : HtabWF mid tw.toNat)
    (hfp_tw_m : ∀ i ∈ htabFootprint mid tw.toNat, Allocated mid i ∧
      ((∃ j ∈ htabFootprint s5 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s5 "heap_ptr") (globN s5 "heap_ptr" + (globN mid "heap_ptr" - globN s5 "heap_ptr"))))
    (hvalues_0m : HtabSetValuesPost s mid (globN s "bal_accounts") pw.toNat)
    (hwf_t0_m : HtabWF mid t0w.toNat)
    (hwf_t8_m : HtabWF mid t8w.toNat)
    (hfp_t0_m : htabFootprint mid t0w.toNat = htabFootprint s5 t0w.toNat)
    (hfp_t8_m : htabFootprint mid t8w.toNat = htabFootprint s5 t8w.toNat)
    (hfp_t0_5 : ∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr"))
    (hfp_t8_5 : ∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat)
    (hpw_tabs_5 : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j)
    (hkey_t0_m : hdr mid t0w.toNat 0 = 32)
    (hkey_t8_m : hdr mid t8w.toNat 0 = 32)
    (hvals_t0_m : htabValues mid t0w.toNat = [])
    (hm0_m : memW mid pw.toNat = t0w.toNat)
    (hm8_m : memW mid (pw.toNat + 8) = t8w.toNat)
    (hm16_m : memW mid (pw.toNat + 16) = l16w.toNat)
    (hm24_m : memW mid (pw.toNat + 24) = l24w.toNat)
    (hm32_m : memW mid (pw.toNat + 32) = l32w.toNat)
    (hlst16_m : LstOK mid l16w.toNat)
    (hobjs16_m : lstObjects mid l16w.toNat 40 = [(l16w.toNat, 24), (l16w.toNat + 24, 160)])
    (hlst24_m : LstOK mid l24w.toNat)
    (hobjs24_m : lstObjects mid l24w.toNat 16 = [(l24w.toNat, 24), (l24w.toNat + 24, 64)])
    (hlst32_m : LstOK mid l32w.toNat)
    (hobjs32_m : lstObjects mid l32w.toNat 24 = [(l32w.toNat, 24), (l32w.toNat + 24, 48)])
    (hmem_rec : pw.toNat ∈ balRecords mid)
    (hno_bs32 : globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ globN s "bal_accounts")
    (hno_ts32 : globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ globN s "bal_accounts")
    (hno_ws32 : globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ globN s "bal_accounts")
    (hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s mid (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s mid (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s mid (globN s "ts", 72))
    (hu_other : ∀ u ∈ S, u ≠ tw.toNat → ∀ i ∈ htabFootprint s u, M08IvlUnhit s mid i)
    (hu_other_ba : ∀ u ∈ S, u ≠ globN s "bal_accounts" → ∀ i ∈ htabFootprint s u, M08IvlUnhit s mid i)
    (hother_fp : ∀ u ∈ S, u ≠ tw.toNat →
      (∀ k, k < 11 → hdr mid u k = hdr s u k) ∧ htabFootprint mid u = htabFootprint s u)
    (hbo_part : blockOutObjects mid = blockOutObjects s ∧
      (globN mid "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
        memW mid (globN mid "bo" + k) ≠ 0 → LstOK mid (memW mid (globN mid "bo" + k))))
    (hold_acc : ∀ ad ∈ balRecords s,
      ((ad, 40) :: lstObjects mid (memW mid (ad + 16)) 40 ++
        lstObjects mid (memW mid (ad + 24)) 16 ++
        lstObjects mid (memW mid (ad + 32)) 24 ++
        (htabValues mid (memW mid ad)).flatMap (fun l => lstObjects mid l 40) =
      (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
        lstObjects s (memW s (ad + 24)) 16 ++
        lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)) ∧
      memW mid ad = memW s ad ∧
      memW mid (ad + 8) = memW s (ad + 8) ∧
      htabValues mid (memW mid ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK mid (memW mid (ad + k))) ∧
      (∀ l ∈ htabValues mid (memW mid ad), LstOK mid l))
    (hF_mid : FixedTyped mid)
    (hfix_from : ∀ o ∈ fixedObjects mid, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN mid "heap_ptr"))
    (hjr_eq : journalRoleSlots mid = journalRoleSlots s)
    (hJ_mid : JournalTyped mid (S ++ [t0w.toNat, t8w.toNat]))
    (hnd_alloc : ∀ o ∈ nodeExtents s Nd, o = (0, 0) ∨ Allocated s o)
    (hNH_mid : NodeHeap mid Nd)
    (hnd_eq : nodeExtents mid Nd = nodeExtents s Nd) :
    ∃ S' Nd',
      (∀ t ∈ S, t ∈ S') ∧
      WorldTypedWith mid S' Nd' ∧
      OwnedGrows s mid (worldOwned s S Nd) (worldOwned mid S' Nd') ∧
      FrameOutside s mid (worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) ∧
      pw.toNat ∈ balRecords mid := by
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have hsb_pos : 0 < sourceBase := by decide
  have hm_hi : globN mid "heap_ptr" ≤ heapLimit := hAm.2.2.1
  have hsub : ∀ t ∈ S, t ∈ S ++ [t0w.toNat, t8w.toNat] :=
    fun t ht => List.mem_append_left _ ht
  let fresh_pw : List Ivl :=
    [(pw.toNat, 40), (l16w.toNat, 24), (l16w.toNat + 24, 160),
      (l24w.toNat, 24), (l24w.toNat + 24, 64), (l32w.toNat, 24), (l32w.toNat + 24, 48)]
  have hpw_obj_eq :
      (pw.toNat, 40) :: lstObjects mid (memW mid (pw.toNat + 16)) 40 ++
        lstObjects mid (memW mid (pw.toNat + 24)) 16 ++
        lstObjects mid (memW mid (pw.toNat + 32)) 24 ++
        (htabValues mid (memW mid pw.toNat)).flatMap (fun l => lstObjects mid l 40) = fresh_pw := by
    rw [hm0_m, hm16_m, hm24_m, hm32_m, hvals_t0_m, hobjs16_m, hobjs24_m, hobjs32_m]
    rfl
  have hfresh_pw_in5 : ∀ i ∈ fresh_pw, Inside i (globN s "heap_ptr") (globN s5 "heap_ptr") := by
    intro i hi
    simp only [fresh_pw, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by dsimp; omega, by dsimp; omega⟩
  have ht0_nz : t0w.toNat ≠ 0 := by omega
  have ht8_nz : t8w.toNat ≠ 0 := by omega
  have ht08_ne : t0w.toNat ≠ t8w.toNat := by omega
  have hT_nd : ([t0w.toNat, t8w.toNat] : List Nat).Nodup := by simp [ht08_ne]
  have hT_wf : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), HtabWF mid t ∧
      ∀ i ∈ htabFootprint mid t, Allocated mid i ∧
        Inside i (globN s "heap_ptr") (globN mid "heap_ptr") ∧
        (∀ j ∈ fixedObjects mid, Disj i j) := by
    intro t ht
    have hdisj_fresh_pw : ∀ i : Ivl,
        (Inside i (pw.toNat + 40) (globN s1 "heap_ptr") ∨ Inside i (globN s1 "heap_ptr") l16w.toNat) →
        ∀ j ∈ fresh_pw, Disj i j := by
      intro i hi_in j hj
      simp only [fresh_pw, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hi_in with ⟨hi1_lo, hi1_hi⟩ | ⟨hi2_lo, hi2_hi⟩ <;>
        (rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
    have hfix_mid_class : ∀ j ∈ fixedObjects mid, j ∈ fixedObjects s ∨ j ∈ fresh_pw := by
      intro j hj
      unfold fixedObjects at hj
      have hgb : (globalBuffers.map fun gn => (globN mid gn.1, if globN mid gn.1 = 0 then 0 else gn.2)) =
          (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
        apply List.map_congr_left; intro gn hgn; rw [hgs.1 gn hgn]
      rw [hgb, hgs.2.2.1, hgs.2.2.2.1, hbo_part.1] at hj
      rcases List.mem_append.1 hj with hpre | hbal
      · left; unfold fixedObjects; exact List.mem_append_left _ hpre
      · unfold balObjects at hbal
        obtain ⟨ad, had, hj_ad⟩ := List.mem_flatMap.1 hbal
        obtain ⟨_, _, hbal_mem⟩ := balRecords_set_values_add
          (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) hba_nz hvalues_0m
        rcases hbal_mem ad had with had_s | rfl
        · left
          rw [(hold_acc ad had_s).1] at hj_ad
          unfold fixedObjects
          exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had_s, hj_ad⟩)
        · right; rwa [hpw_obj_eq] at hj_ad
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨hwf_t0_m, fun i hi => ?_⟩
      rw [hfp_t0_m] at hi
      have hin5 := (hfp_t0_5 i hi).2
      have hin0m : Inside i (globN s "heap_ptr") (globN mid "heap_ptr") :=
        ⟨by have := hin5.1; omega, by have := hin5.2; omega⟩
      refine ⟨Or.inl ⟨by have := hin0m.1; omega, by have := hin0m.2; omega⟩, hin0m, fun j hj => ?_⟩
      rcases hfix_mid_class j hj with hj_s | hj_fr
      · rcases hF.1 j hj_s with hz | ⟨hal_j, _⟩
        · exact Or.inr (Or.inl hz)
        · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_j hin0m
      · exact hdisj_fresh_pw i (Or.inl hin5) j hj_fr
    · refine ⟨hwf_t8_m, fun i hi => ?_⟩
      rw [hfp_t8_m] at hi
      have hin5 := (hfp_t8_5 i hi).2
      have hin0m : Inside i (globN s "heap_ptr") (globN mid "heap_ptr") :=
        ⟨by have := hin5.1; omega, by have := hin5.2; omega⟩
      refine ⟨Or.inl ⟨by have := hin0m.1; omega, by have := hin0m.2; omega⟩, hin0m, fun j hj => ?_⟩
      rcases hfix_mid_class j hj with hj_s | hj_fr
      · rcases hF.1 j hj_s with hz | ⟨hal_j, _⟩
        · exact Or.inr (Or.inl hz)
        · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_j hin0m
      · exact hdisj_fresh_pw i (Or.inr hin5) j hj_fr
  have hT_disj_S : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), t ∉ S := by
    intro t ht htS
    have ht_in := ((hT_wf t ht).2 (t, 88) (by simp [htabFootprint])).2.1
    have hal_s := ((hT.2.1 t htS).2 (t, 88) (by simp [htabFootprint])).1
    have hd := Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_s ht_in
    rcases hd with h | h | h | h <;> dsimp at h <;> omega
  have hT_pw_new : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat), t ≠ u →
      ∀ i ∈ htabFootprint mid t, ∀ j ∈ htabFootprint mid u, Disj i j := by
    intro t ht u hu hne i hi j hj
    have hfp_eq : ∀ x ∈ ([t0w.toNat, t8w.toNat] : List Nat), htabFootprint mid x = htabFootprint s5 x := by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl; exact hfp_t0_m; exact hfp_t8_m
    rw [hfp_eq t ht] at hi; rw [hfp_eq u hu] at hj
    exact hpw_tabs_5 t ht u hu hne i hi j hj
  have htw_disj : ∀ i ∈ htabFootprint mid tw.toNat,
      (∀ u ∈ S, u ≠ tw.toNat → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects mid, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) ∧
      (∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ j ∈ htabFootprint mid t, Disj i j) := by
    intro i hi
    rcases (hfp_tw_m i hi).2 with ⟨k, hk5, hin⟩ | hfresh5m
    · rw [hfp_tw_5] at hk5
      refine ⟨fun u hu hne j hj =>
          Wave8Contracts.M08.disj_of_inside_left hin (hT.2.2.1 tw.toNat hba_S u hu hne.symm k hk5 j hj),
        fun j hj => ?_,
        fun o ho => Wave8Contracts.M08.disj_of_inside_left hin (disj_flip ((hTr.2.1 o ho).1 tw.toNat hba_S k hk5)),
        fun t ht j hj => Wave8Contracts.M08.disj_of_inside_left hin
          (disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
            (((hT.2.1 tw.toNat hba_S).2 k hk5).1) (((hT_wf t ht).2 j hj).2.1)))⟩
      rcases hfix_from j hj with hj_s | rfl | hj_fr
      · exact Wave8Contracts.M08.disj_of_inside_left hin (((hT.2.1 tw.toNat hba_S).2 k hk5).2 j hj_s)
      · exact Or.inr (Or.inl rfl)
      · exact Wave8Contracts.M08.disj_of_inside_left hin
          (disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
            (((hT.2.1 tw.toNat hba_S).2 k hk5).1) hj_fr))
    · have hfresh5m' : Inside i (globN s5 "heap_ptr") (globN mid "heap_ptr") :=
        ⟨hfresh5m.1, by have := hfresh5m.2; omega⟩
      have hfresh0m : Inside i (globN s "heap_ptr") (globN mid "heap_ptr") :=
        ⟨le_trans hhp_05 hfresh5m'.1, hfresh5m'.2⟩
      refine ⟨fun u hu _ j hj => Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
          (((hT.2.1 u hu).2 j hj).1) hfresh0m,
        fun j hj => ?_,
        fun o ho => ?_,
        fun t ht j hj => ?_⟩
      · unfold fixedObjects at hj
        have hgb : (globalBuffers.map fun gn => (globN mid gn.1, if globN mid gn.1 = 0 then 0 else gn.2)) =
            (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
          apply List.map_congr_left; intro gn hgn; rw [hgs.1 gn hgn]
        rw [hgb, hgs.2.2.1, hgs.2.2.2.1, hbo_part.1] at hj
        rcases List.mem_append.1 hj with hpre | hbal
        · have hj_s : j ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_left _ hpre
          rcases hF.1 j hj_s with hz | ⟨hal_j, _⟩
          · exact Or.inr (Or.inl hz)
          · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_j hfresh0m
        · unfold balObjects at hbal
          obtain ⟨ad, had, hj_ad⟩ := List.mem_flatMap.1 hbal
          obtain ⟨_, _, hbal_mem⟩ := balRecords_set_values_add
            (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) hba_nz hvalues_0m
          rcases hbal_mem ad had with had_s | rfl
          · rw [(hold_acc ad had_s).1] at hj_ad
            have hj_s : j ∈ fixedObjects s := by
              unfold fixedObjects
              exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had_s, hj_ad⟩)
            rcases hF.1 j hj_s with hz | ⟨hal_j, _⟩
            · exact Or.inr (Or.inl hz)
            · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_j hfresh0m
          · rw [hpw_obj_eq] at hj_ad
            have hj5 := (hfresh_pw_in5 j hj_ad).2
            exact Or.inr (Or.inr (Or.inr (by have := hfresh5m'.1; omega)))
      · rcases hnd_alloc o ho with rfl | hal_o
        · exact Or.inr (Or.inl rfl)
        · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_o hfresh0m
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · rw [hfp_t0_m] at hj
          have hj5 := (hfp_t0_5 j hj).2.2
          exact Or.inr (Or.inr (Or.inr (by have := hfresh5m'.1; omega)))
        · rw [hfp_t8_m] at hj
          have hj5 := (hfp_t8_5 j hj).2.2
          exact Or.inr (Or.inr (Or.inr (by have := hfresh5m'.1; omega)))
  have hhdr0_S : ∀ t ∈ S, hdr mid t 0 = hdr s t 0 := by
    intro t ht
    by_cases htw : t = tw.toNat
    · subst htw; exact hhdr0_tw_m
    · exact (hother_fp t ht htw).1 0 (by omega)
  have hroles_mid : RolesOK mid (S ++ [t0w.toNat, t8w.toNat]) (worldRoleSlots mid) (journalRoleSlots mid) :=
    rolesOK_balEnsureAlloc hAR.2 hT hF hgs hba_nz hvalues_0m hu_other_ba hu_ws hu_bs hu_ts
      (fun ad had => ⟨(hold_acc ad had).2.1, (hold_acc ad had).2.2.1⟩)
      ⟨hm0_m, hm8_m⟩ ht0_nz ht8_nz ht08_ne hkey_t0_m hkey_t8_m hhdr0_S hT_disj_S hjr_eq
  have hroot_S : ∀ {v}, RootIn S v → RootIn (S ++ [t0w.toNat, t8w.toNat]) v := by
    rintro v (rfl | hv); exact Or.inl rfl; exact Or.inr (hsub v hv)
  have hT_mid : TablesTyped mid (S ++ [t0w.toNat, t8w.toNat]) := by
    obtain ⟨hndS, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, _⟩ := hT
    have ews := hgs.1 ("ws", 40) (by simp [globalBuffers])
    have ebs := hgs.1 ("bs", 80) (by simp [globalBuffers])
    have ets := hgs.1 ("ts", 72) (by simp [globalBuffers])
    refine ⟨List.nodup_append.2 ⟨hndS, hT_nd, fun u hu v hv heq => by subst heq; exact hT_disj_S u hv hu⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, hroles_mid⟩
    · intro u hu
      rcases List.mem_append.1 hu with huS | huN
      · by_cases hu_tw : u = tw.toNat
        · subst hu_tw
          exact ⟨hwf_tw_m, fun i hi => ⟨(hfp_tw_m i hi).1, (htw_disj i hi).2.1⟩⟩
        · rw [(hother_fp u huS hu_tw).2]
          refine ⟨Wave8Contracts.M08.htabWF_congr_unhit hAR.1 hAm.1 (htwf u huS).1 (hu_other u huS hu_tw),
            fun i hi => ⟨hag.allocated ((htwf u huS).2 i hi).1, fun j hj => ?_⟩⟩
          rcases hfix_from j hj with hj_s | rfl | hj_fr
          · exact ((htwf u huS).2 i hi).2 j hj_s
          · exact Or.inr (Or.inl rfl)
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
              (((htwf u huS).2 i hi).1) hj_fr)
      · exact ⟨(hT_wf u huN).1, fun i hi => ⟨((hT_wf u huN).2 i hi).1, ((hT_wf u huN).2 i hi).2.2⟩⟩
    · intro u hu v hv hne i hi j hj
      rcases List.mem_append.1 hu with huS | huN <;> rcases List.mem_append.1 hv with hvS | hvN
      · by_cases hu_tw : u = tw.toNat
        · subst hu_tw
          rw [(hother_fp v hvS hne.symm).2] at hj
          exact (htw_disj i hi).1 v hvS hne.symm j hj
        · by_cases hv_tw : v = tw.toNat
          · subst hv_tw
            rw [(hother_fp u huS hu_tw).2] at hi
            exact disj_flip ((htw_disj j hj).1 u huS hu_tw i hi)
          · rw [(hother_fp u huS hu_tw).2] at hi; rw [(hother_fp v hvS hv_tw).2] at hj
            exact htpw u huS v hvS hne i hi j hj
      · by_cases hu_tw : u = tw.toNat
        · subst hu_tw
          exact (htw_disj i hi).2.2.2 v hvN j hj
        · rw [(hother_fp u huS hu_tw).2] at hi
          exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
            (((htwf u huS).2 i hi).1) (((hT_wf v hvN).2 j hj).2.1))
      · by_cases hv_tw : v = tw.toNat
        · subst hv_tw
          exact disj_flip ((htw_disj j hj).2.2.2 u huN i hi)
        · rw [(hother_fp v hvS hv_tw).2] at hj
          exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
            (((htwf v hvS).2 j hj).1) (((hT_wf u huN).2 i hi).2.1)
      · exact hT_pw_new u huN v hvN hne i hi j hj
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ws" 40 (by decide) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hroot_S (hwsR k hk hnz)
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "bs" 80 (by decide) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hroot_S (hbsR k hk hnz)
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ts" 72 (by decide) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact hroot_S (htsR k hk hnz)
    · intro g hg_mem; rw [hgs.2.1 g hg_mem]; exact hroot_S (hgR g hg_mem)
    · intro hnz hm
      rw [ebs] at hnz
      have ew := Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "bs" 80 (by decide) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hm ⊢
      rcases List.mem_append.1 hm with hmS | hmN
      · exact Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmS).1
          (hu_other_ba _ hmS (hno_bs32 hnz)) hsub (hbsN hnz hmS)
      · rcases hbsR 32 (by simp [bsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0 ▸ hmN) (fun h0N => htab_nonzero_of_wf (hT_wf 0 h0N).1 rfl)
        · exact absurd hmS (hT_disj_S _ hmN)
    · intro hnz hm
      rw [ets] at hnz
      have ew := Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ts" 72 (by decide) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hm ⊢
      rcases List.mem_append.1 hm with hmS | hmN
      · exact Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmS).1
          (hu_other_ba _ hmS (hno_ts32 hnz)) hsub (htsN hnz hmS)
      · rcases htsR 32 (by simp [tsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0 ▸ hmN) (fun h0N => htab_nonzero_of_wf (hT_wf 0 h0N).1 rfl)
        · exact absurd hmS (hT_disj_S _ hmN)
    · intro ad had
      obtain ⟨_, _, hbal_mem⟩ := balRecords_set_values_add
        (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) hba_nz hvalues_0m
      rcases hbal_mem ad had with had_s | rfl
      · obtain ⟨_, e0, e8, _, hkl, hll⟩ := hold_acc ad had_s
        exact ⟨e0 ▸ hsub _ (hbalT ad had_s).1, e8 ▸ hsub _ (hbalT ad had_s).2.1, hkl, hll⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hm0_m]; exact List.mem_append_right _ (by simp)
        · rw [hm8_m]; exact List.mem_append_right _ (by simp)
        · intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl
          · rw [hm16_m]; exact hlst16_m
          · rw [hm24_m]; exact hlst24_m
          · rw [hm32_m]; exact hlst32_m
        · intro l hl
          rw [hm0_m, hvals_t0_m] at hl
          cases hl
  have hTr_mid : TriesTypedWith mid (S ++ [t0w.toNat, t8w.toNat]) Nd := by
    have ews := hgs.1 ("ws", 40) (by simp [globalBuffers])
    refine ⟨hNH_mid, ?_, ?_⟩
    · intro o ho
      rw [hnd_eq] at ho
      refine ⟨fun u hu i hi => ?_, fun j hj => ?_⟩
      · rcases List.mem_append.1 hu with huS | huN
        · by_cases hu_tw : u = tw.toNat
          · subst hu_tw; exact disj_flip ((htw_disj i hi).2.2.1 o ho)
          · rw [(hother_fp u huS hu_tw).2] at hi
            exact (hTr.2.1 o ho).1 u huS i hi
        · rcases hnd_alloc o ho with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
              hal_o (((hT_wf u huN).2 i hi).2.1))
      · rcases hfix_from j hj with hj_s | rfl | hj_fr
        · exact (hTr.2.1 o ho).2 j hj_s
        · exact Or.inr (Or.inl rfl)
        · rcases hnd_alloc o ho with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_o hj_fr)
    · intro hws_nz
      rw [ews] at hws_nz
      have e24 := Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ws" 40 (by decide) ews hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ws" 40 (by decide) ews hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun hm i hi => ?_⟩
      rcases List.mem_append.1 hm with hmS | hmN
      · have hne32 : memW s (globN s "ws" + 32) ≠ tw.toNat := by
          rw [ht_eq]; exact hno_ws32 hws_nz
        have hu32 := hu_other _ hmS hne32
        have hwf32 := (hT.2.1 _ hmS).1
        have hvals_eq := Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
        obtain ⟨hhdr32, _⟩ := hother_fp _ hmS hne32
        rw [hhdr32 3 (by omega)] at hi
        have hget : (htabValues mid (memW s (globN s "ws" + 32)))[i]? =
            (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
        simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
          Option.map_some, Option.some.injEq] at hget
        rw [hget]; exact hr32 hmS i hi
      · rcases hT.2.2.2.1 32 (by simp [wsTableSlots]) hws_nz with h0 | hmS
        · exact absurd (h0 ▸ hmN) (fun h0N => htab_nonzero_of_wf (hT_wf 0 h0N).1 rfl)
        · exact absurd hmS (hT_disj_S _ hmN)
  refine ⟨S ++ [t0w.toNat, t8w.toNat], Nd, hsub, ⟨hT_mid, hJ_mid, hF_mid, hTr_mid⟩, ?_, ?_, hmem_rec⟩
  · intro o ho
    unfold worldOwned M13.worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · rw [List.flatMap_append] at ho_tab
        rcases List.mem_append.1 ho_tab with ho_S | ho_N
        · obtain ⟨u, huS, hi⟩ := List.mem_flatMap.1 ho_S
          by_cases hu_tw : u = tw.toNat
          · subst hu_tw
            rcases (hfp_tw_m o hi).2 with ⟨j, hj5, hin⟩ | hfresh5m
            · rw [hfp_tw_5] at hj5
              refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
              unfold worldOwned M13.worldOwned
              exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨tw.toNat, hba_S, hj5⟩))
            · exact Or.inr (Or.inr ⟨le_trans hhp_05 hfresh5m.1, by have := hfresh5m.2; omega⟩)
          · rw [(hother_fp u huS hu_tw).2] at hi
            refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
            unfold worldOwned M13.worldOwned
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, huS, hi⟩))
        · obtain ⟨t, htN, hi⟩ := List.mem_flatMap.1 ho_N
          exact Or.inr (Or.inr ((hT_wf t htN).2 o hi).2.1)
      · rcases hfix_from o ho_fix with ho_s | rfl | ho_fr
        · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_right _ ho_s)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ho_fr)
    · rw [hnd_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_right _ ho_nd
  · intro a hkeep hnot_hf
    apply hfr_0m a
    · intro j hj hcj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact hkeep (freeGap s)
          (List.mem_append_right _ (List.mem_singleton.2 rfl))
          (cellHits_sp0_imp_freeGap hAR.2 hcj)
      · apply hkeep j
        · apply List.mem_append_left; apply List.mem_append_left
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨tw.toNat, hba_S, hj_fp⟩))
        · exact hcj
    · intro ⟨c1, c2⟩
      apply hnot_hf
      dsimp only at c1 c2
      unfold heapFree M13.heapFree CellHits
      dsimp only
      omega

private theorem balEnsureAlloc_worldStep_core {F : Type}
    {s s1 s5 mid : PanSemStateFiniteExact 64 F}
    {tw pw t0w t8w l16w l24w l32w : BitVec 64}
    {S Nd : List Nat}
    (hAR : ArenaReady s) (hA5 : ArenaReady s5) (hAm : ArenaReady mid)
    (hWT : WorldTypedWith s S Nd)
    (ht_eq : tw.toNat = globN s "bal_accounts")
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hgk : GlobalsKept ["heap_ptr"] s mid)
    (hsp_mid : globN mid "scratch_ptr" = globN s "scratch_ptr")
    (hhp_05 : globN s "heap_ptr" ≤ globN s5 "heap_ptr")
    (hhp_5m : globN s5 "heap_ptr" ≤ globN mid "heap_ptr")
    (hbe_0m : mid.be = s.be)
    (hpw_eq : pw.toNat = globN s "heap_ptr")
    (hpw8 : pw.toNat % 8 = 0)
    (hpw_t0 : pw.toNat + 40 ≤ t0w.toNat)
    (ht0_s1 : t0w.toNat + 88 ≤ globN s1 "heap_ptr")
    (hs1_t8 : globN s1 "heap_ptr" ≤ t8w.toNat)
    (ht8_l16 : t8w.toNat + 88 ≤ l16w.toNat)
    (hl16_l24 : l16w.toNat + 24 + 160 = l24w.toNat)
    (hl24_l32 : l24w.toNat + 24 + 64 = l32w.toNat)
    (hl32_s5 : l32w.toNat + 24 + 48 = globN s5 "heap_ptr")
    (hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr"))
    (hfp_tw_5 : htabFootprint s5 tw.toNat = htabFootprint s tw.toNat)
    (hhdr0_tw_m : hdr mid tw.toNat 0 = hdr s tw.toNat 0)
    (hwf_tw_m : HtabWF mid tw.toNat)
    (hfp_tw_m : ∀ i ∈ htabFootprint mid tw.toNat, Allocated mid i ∧
      ((∃ j ∈ htabFootprint s5 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s5 "heap_ptr") (globN s5 "heap_ptr" + (globN mid "heap_ptr" - globN s5 "heap_ptr"))))
    (hvalues_0m : HtabSetValuesPost s mid (globN s "bal_accounts") pw.toNat)
    (hwf_t0_m : HtabWF mid t0w.toNat)
    (hwf_t8_m : HtabWF mid t8w.toNat)
    (hfp_t0_m : htabFootprint mid t0w.toNat = htabFootprint s5 t0w.toNat)
    (hfp_t8_m : htabFootprint mid t8w.toNat = htabFootprint s5 t8w.toNat)
    (hfp_t0_5 : ∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr"))
    (hfp_t8_5 : ∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat)
    (hpw_tabs_5 : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j)
    (hkey_t0_m : hdr mid t0w.toNat 0 = 32)
    (hkey_t8_m : hdr mid t8w.toNat 0 = 32)
    (hvals_t0_m : htabValues mid t0w.toNat = [])
    (hm0_m : memW mid pw.toNat = t0w.toNat)
    (hm8_m : memW mid (pw.toNat + 8) = t8w.toNat)
    (hm16_m : memW mid (pw.toNat + 16) = l16w.toNat)
    (hm24_m : memW mid (pw.toNat + 24) = l24w.toNat)
    (hm32_m : memW mid (pw.toNat + 32) = l32w.toNat)
    (hlst16_m : LstOK mid l16w.toNat)
    (hobjs16_m : lstObjects mid l16w.toNat 40 = [(l16w.toNat, 24), (l16w.toNat + 24, 160)])
    (hlst24_m : LstOK mid l24w.toNat)
    (hobjs24_m : lstObjects mid l24w.toNat 16 = [(l24w.toNat, 24), (l24w.toNat + 24, 64)])
    (hlst32_m : LstOK mid l32w.toNat)
    (hobjs32_m : lstObjects mid l32w.toNat 24 = [(l32w.toNat, 24), (l32w.toNat + 24, 48)])
    (hm0_8_16 : memW mid 0 = memW s 0 ∧ memW mid 8 = memW s 8 ∧ memW mid 16 = memW s 16)
    (hmem_rec : pw.toNat ∈ balRecords mid) :
    ∃ S' Nd',
      (∀ t ∈ S, t ∈ S') ∧
      WorldTypedWith mid S' Nd' ∧
      OwnedGrows s mid (worldOwned s S Nd) (worldOwned mid S' Nd') ∧
      FrameOutside s mid (worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) ∧
      pw.toNat ∈ balRecords mid := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hsp8 : (globN s "scratch_ptr") % 8 = 0 := hAR.2.2.2.2.2.2.2.2.1
  have hhp_0m : globN s "heap_ptr" ≤ globN mid "heap_ptr" := le_trans hhp_05 hhp_5m
  have hag : AllocatorGrows s mid := ⟨hhp_0m, by omega⟩
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s mid :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hgk (fun name h => Or.inl (by simpa using h))
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have hsb_pos : 0 < sourceBase := by decide
  have hba_S : tw.toNat ∈ S := by
    rw [ht_eq]
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hba_nz
    · exact hm
  have hWF_tw : HtabWF s tw.toNat := (hT.2.1 _ hba_S).1
  have hk_al_0m : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hsp8
    · exact (hWF_tw.1 j hj_fp).2.1
  have hl32_8 : l32w.toNat % 8 = 0 := by
    have h := hA5.2.2.2.2.2.2.1; omega
  have hl24_8 : l24w.toNat % 8 = 0 := by omega
  have hl16_8 : l16w.toNat % 8 = 0 := by omega
  let fresh_pw : List Ivl :=
    [(pw.toNat, 40), (l16w.toNat, 24), (l16w.toNat + 24, 160),
      (l24w.toNat, 24), (l24w.toNat + 24, 64), (l32w.toNat, 24), (l32w.toNat + 24, 48)]
  have hpw_obj_eq :
      (pw.toNat, 40) :: lstObjects mid (memW mid (pw.toNat + 16)) 40 ++
        lstObjects mid (memW mid (pw.toNat + 24)) 16 ++
        lstObjects mid (memW mid (pw.toNat + 32)) 24 ++
        (htabValues mid (memW mid pw.toNat)).flatMap (fun l => lstObjects mid l 40) = fresh_pw := by
    rw [hm0_m, hm16_m, hm24_m, hm32_m, hvals_t0_m, hobjs16_m, hobjs24_m, hobjs32_m]
    rfl
  have hfresh_pw_props : ∀ i ∈ fresh_pw,
      Inside i (globN s "heap_ptr") (globN s5 "heap_ptr") ∧ WordsOK mid i := by
    intro i hi
    simp only [fresh_pw, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact ⟨⟨by dsimp; omega, by dsimp; omega⟩,
        Wave8Contracts.M08.wordsOK_fresh_heap hAm.1 (by omega) (by decide) (by omega)
          (by have := hA5.2.2.1; omega)⟩
  have hpw_fresh_pw : fresh_pw.Pairwise Disj := by
    simp only [fresh_pw, List.pairwise_cons, List.Pairwise.nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true, imp_false, not_true_eq_false]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, fun _ h => False.elim h⟩
    all_goals exact Or.inr (Or.inr (Or.inl (by omega)))
  have hu_fix : ∀ i ∈ fixedObjects s, M08IvlUnhit s mid i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact disj_flip (((hT.2.1 _ hba_S).2 j hj_fp).2 i hi)
    · rcases hF.1 i hi with hz | ⟨hal, _⟩
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inl hz)
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr hal)
  obtain ⟨_, hno_bs32, hno_ts32, hno_ad0, hno_ws32⟩ := bal_accounts_role_props hT hba_nz
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s mid (globN s "ws", 40) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s mid (globN s "bs", 80) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s mid (globN s "ts", 72) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s mid (globN s "bo", 88) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_jr : globN s "journal_cap" ≠ 0 → M08IvlUnhit s mid (globN s "journal", 32 * globN s "journal_cap") := fun h => by
    have hm : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      simp [h]
    exact hu_fix _ hm
  have hu_other : ∀ u ∈ S, u ≠ tw.toNat → ∀ i ∈ htabFootprint s u, M08IvlUnhit s mid i := by
    intro u hu hne i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact hT.2.2.1 u hu tw.toNat hba_S hne i hi j hj_fp
    · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr ((hT.2.1 u hu).2 i hi).1)
  have hu_other_ba : ∀ u ∈ S, u ≠ globN s "bal_accounts" → ∀ i ∈ htabFootprint s u, M08IvlUnhit s mid i := by
    rw [← ht_eq]; exact hu_other
  have hother_fp : ∀ u ∈ S, u ≠ tw.toNat →
      (∀ k, k < 11 → hdr mid u k = hdr s u k) ∧ htabFootprint mid u = htabFootprint s u := by
    intro u hu hne
    have hwf := (hT.2.1 u hu).1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have hu8 : u % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have h264' : heapEnd ≤ 2 ^ 64 := by decide
    have hhi : u + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit hu8 hhi (hu_other u hu hne _ ht_fp)
  have hbo_g : globN mid "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW mid (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    simpa [hbo_g] using Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "bo" 88 (by decide) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit hAR.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0_8_16.1, hm0_8_16.2.2])
    (fun _ _ => by simp [hm0_8_16.1, hm0_8_16.2.2])
    (fun h h40 => hu_fix (memW s (globN s "bo" + 40), 24) (by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right
      simp [blockOutObjects, h, h40]))
    (fun h h72 => hu_fix (memW s (globN s "bo" + 72), 24) (by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right
      simp [blockOutObjects, h, h72]))
  have hold_acc := fun ad (had : ad ∈ balRecords s) =>
    old_balAccount_congr_of_unhit hAR.2 hT hF hu_other_ba hno_ad0
      (fun i hi _ => hu_fix i (by unfold fixedObjects; exact List.mem_append_right _ hi))
      hm0_8_16 had
  obtain ⟨hF_mid, hfix_from⟩ := fixedTyped_of_balObjects_set_values_add
    hAR hAm hag hF hgs hbo_part.1 hba_nz hvalues_0m
    (fun ad had => (hold_acc ad had).1)
    hpw_obj_eq
    (fun i hi => ⟨⟨(hfresh_pw_props i hi).1.1, le_trans (hfresh_pw_props i hi).1.2 hhp_5m⟩, (hfresh_pw_props i hi).2⟩)
    hpw_fresh_pw
  have hsub : ∀ t ∈ S, t ∈ S ++ [t0w.toNat, t8w.toNat] :=
    fun t ht => List.mem_append_left _ ht
  obtain ⟨hjr_eq, hJ_mid⟩ := Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAR.1 hAm.1 hAR.2 hag hsub hJ hF hgs hu_ts hu_jr
  have hnd_alloc : ∀ o ∈ nodeExtents s Nd, o = (0, 0) ∨ Allocated s o := by
    intro o ho
    obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hno with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr hal
      · exact Or.inl rfl
  have hu_nd : ∀ o ∈ nodeExtents s Nd, M08IvlUnhit s mid o := by
    intro o ho
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact (hTr.2.1 o ho).1 tw.toNat hba_S j hj_fp
    · rcases hnd_alloc o ho with rfl | hal
      · exact Or.inl rfl
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr hal)
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s mid (nodeIvl s n) := by
    intro n hn
    exact hu_nd _ (List.mem_flatMap.2 ⟨n, hn, by simp⟩)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB mid (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hnz k hk
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hnz
    · have h264 : heapLimit < 2 ^ 64 := by decide
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by
        have := hin_p.2; dsimp at this; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        have hal8 : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
        change (BitVec.ofNat 64 ((BitVec.ofNat 64 (memW s (n + 32) + k)).toNat / 2 ^ ((64 : Nat) / 8).log2 *
          2 ^ ((64 : Nat) / 8).log2)).toNat = (memW s (n + 32) + k) / 8 * 8
        rw [hal8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
          Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ 8) ha_lt)]
      have hp_mem : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        have hp_eq : nodePath s n = (memW s (n + 32), memW s (n + 40)) := by simp [nodePath, h12, hnz]
        rw [← hp_eq]
        exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      have hmem := hfr_0m c
        (fun j hj hcj => by
          obtain ⟨c1, c2⟩ := hcj
          rw [hc_nat] at c1 c2
          rcases List.mem_cons.1 hj with rfl | hj_fp
          · dsimp at c1 c2; omega
          · have hj_al := ((hT.2.1 _ hba_S).1.1 j hj_fp).2
            have hj1 := hj_al.1; have hj2 := hj_al.2.1
            have hdj := (hTr.2.1 _ hp_mem).1 tw.toNat hba_S j hj_fp
            rcases hdj with d | d | d | d <;> (try dsimp at c1 c2) <;> (try dsimp at d) <;> omega)
        (fun ⟨c1, c2⟩ => by
          dsimp at c1 c2; rw [hc_nat] at c1 c2
          have hp_hp8 : (globN s "heap_ptr") % 8 = 0 := hAR.2.2.2.2.2.2.1
          have hm_hp8 : (globN mid "heap_ptr") % 8 = 0 := hAm.2.2.2.2.2.2.1
          have hdj := disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr hal_p)
          rcases hdj with d | d | d | d <;> (try dsimp at d) <;> omega)
      unfold memB
      change (match mid.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v mid.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hbe_0m]
  obtain ⟨hNH_mid, hnd_eq⟩ := Wave8Contracts.M08.nodeHeap_congr_bytes
    hAR.1 hAm.1 hag hTr.1 hu_nd_rec hu_nd_byte
  exact balEnsureAlloc_worldStep_finish hAR hAm hag hT hF hTr hgs ht_eq hba_nz hba_S
    hhp_05 hhp_5m hpw_eq hpw_t0 ht0_s1 hs1_t8 ht8_l16 hl16_l24 hl24_l32 hl32_s5
    hfr_0m hfp_tw_5 hhdr0_tw_m hwf_tw_m hfp_tw_m hvalues_0m
    hwf_t0_m hwf_t8_m hfp_t0_m hfp_t8_m hfp_t0_5 hfp_t8_5 hpw_tabs_5
    hkey_t0_m hkey_t8_m hvals_t0_m hm0_m hm8_m hm16_m hm24_m hm32_m
    hlst16_m hobjs16_m hlst24_m hobjs24_m hlst32_m hobjs32_m hmem_rec
    hno_bs32 hno_ts32 hno_ws32 hu_ws hu_bs hu_ts hu_other hu_other_ba hother_fp
    hbo_part hold_acc hF_mid hfix_from hjr_eq hJ_mid hnd_alloc hNH_mid hnd_eq

private theorem balEnsureAlloc_recordsKept {F : Type}
    {s mid : PanSemStateFiniteExact 64 F} {tw : BitVec 64} {S0 : List Nat} {Nd0 : List Nat}
    (hAR : ArenaReady s) (hAm : ArenaReady mid) (hW0 : WorldTypedWith s S0 Nd0)
    (ht_eq : tw.toNat = globN s "bal_accounts")
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s mid)
    (hhp_0m : globN s "heap_ptr" ≤ globN mid "heap_ptr")
    (hWF_tw : HtabWF s tw.toNat)
    (hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr")) :
    RecordsKept (fun _ => []) stdKeep s mid := by
  have hk_al_0m : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hAR.2.2.2.2.2.2.2.2.1
    · exact (hWF_tw.1 j hj_fp).2.1
  have hu_fixed_0m : ∀ i ∈ fixedObjects s, M08IvlUnhit s mid i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · have hba_S0 : tw.toNat ∈ S0 := by
          rw [ht_eq]
          rcases hW0.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hba_nz
          · exact hm
        exact disj_flip (((hW0.1.2.1 _ hba_S0).2 j hj_fp).2 i hi)
    · rcases hW0.2.2.1.1 i hi with hz | ⟨hal, _⟩
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inl hz)
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr hal)
  intro rec hrec hnz k hk _
  have hrec_tr : rec.1 ∈ ["ws", "bs", "ts", "bo"] ∧
      ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
    simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · refine ⟨by simp, 40, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 80, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 72, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 88, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  obtain ⟨_, sz, htr, hk8, hksz⟩ := hrec_tr
  have hg_eq : globN mid rec.1 = globN s rec.1 :=
    hgs.1 (rec.1, sz) (Wave8Contracts.M08.typedRecord_mem_globalBuffers htr)
  have hfix_rec : (globN s rec.1, sz) ∈ fixedObjects s := by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s htr
    simpa [hnz] using hm
  have hu_rec : M08IvlUnhit s mid (globN s rec.1, sz) := hu_fixed_0m _ hfix_rec
  simpa [hg_eq] using Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hW0.2.2.1 rec.1 sz htr hg_eq hnz hu_rec hk8 hksz

private theorem balEnsureAlloc_lst_mid {F : Type}
    {s5 mid : PanSemStateFiniteExact 64 F} (lw esz cap : Nat)
    (h5_hi : globN s5 "heap_ptr" ≤ heapLimit)
    (h8 : lw % 8 = 0) (hnz : lw ≠ 0) (hhi_lw : lw + 24 + esz * cap ≤ globN s5 "heap_ptr")
    (hu_lw : M08IvlUnhit s5 mid (lw, 24))
    (hok5 : LstOK s5 lw) (hobj5 : lstObjects s5 lw esz = [(lw, 24), (lw + 24, esz * cap)]) :
    LstOK mid lw ∧ lstObjects mid lw esz = [(lw, 24), (lw + 24, esz * cap)] := by
  have h264 : heapLimit < 2 ^ 64 := by decide
  have e0 : memW mid lw = memW s5 lw := by
    simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_lw h8 (by omega) ⟨by omega, by omega⟩
  have e8 : memW mid (lw + 8) = memW s5 (lw + 8) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_lw (by omega) (by omega) ⟨by omega, by omega⟩
  have e16 : memW mid (lw + 16) = memW s5 (lw + 16) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_lw (by omega) (by omega) ⟨by omega, by omega⟩
  refine ⟨?_, ?_⟩
  · unfold LstOK at hok5 ⊢; rw [e8, e16]; exact hok5
  · have heq : lstObjects mid lw esz = lstObjects s5 lw esz := by
      unfold lstObjects; rw [e0, e16]
    exact heq.trans hobj5

private theorem balEnsureAlloc_low_words {F : Type}
    {s mid : PanSemStateFiniteExact 64 F} {tw : BitVec 64}
    (hAR : ArenaReady s)
    (hWF_tw : HtabWF s tw.toNat)
    (hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr")) :
    memW mid 0 = memW s 0 ∧ memW mid 8 = memW s 8 ∧ memW mid 16 = memW s 16 := by
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have hsb24 : 24 < sourceBase := by decide
  have hsc_lo : sourceBase ≤ scratchStart := by decide
  have hk_al_0m : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hAR.2.2.2.2.2.2.2.2.1
    · exact (hWF_tw.1 j hj_fp).2.1
  have hu_low : M08IvlUnhit s mid (0, 24) := by
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · have hj_lo : sourceBase ≤ j.1 := by
          rcases hal_tw j hj_fp with hh | hh
          · exact hh.1
          · exact le_trans (le_trans hsc_lo hAR.2.2.2.1) (le_trans hAR.2.2.2.2.1 hh.1)
        exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
    · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  exact
    ⟨by simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_low (by omega) (by decide) ⟨by omega, by omega⟩,
     Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_low (by omega) (by decide) ⟨by omega, by omega⟩,
     Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_low (by omega) (by decide) ⟨by omega, by omega⟩⟩

private theorem balEnsureAlloc_pw_slots_mid {F : Type}
    {s5 mid : PanSemStateFiniteExact 64 F} {pw t0w t8w l16w l24w l32w : BitVec 64}
    (h5_hi : globN s5 "heap_ptr" ≤ heapLimit)
    (hpw8 : pw.toNat % 8 = 0) (hpw_hi : pw.toNat + 40 ≤ globN s5 "heap_ptr")
    (hu_pw_5m : M08IvlUnhit s5 mid (pw.toNat, 40))
    (hm0_5 : memW s5 pw.toNat = t0w.toNat) (hm8_5 : memW s5 (pw.toNat + 8) = t8w.toNat)
    (hm16_5 : memW s5 (pw.toNat + 16) = l16w.toNat) (hm24_5 : memW s5 (pw.toNat + 24) = l24w.toNat)
    (hm32_5 : memW s5 (pw.toNat + 32) = l32w.toNat) :
    memW mid pw.toNat = t0w.toNat ∧
    memW mid (pw.toNat + 8) = t8w.toNat ∧
    memW mid (pw.toNat + 16) = l16w.toNat ∧
    memW mid (pw.toNat + 24) = l24w.toNat ∧
    memW mid (pw.toNat + 32) = l32w.toNat := by
  have h264 : heapLimit < 2 ^ 64 := by decide
  exact ⟨(by simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m hpw8 (by omega) ⟨by omega, by omega⟩ :
      memW mid pw.toNat = memW s5 pw.toNat).trans hm0_5,
    (Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m (by omega) (by omega) ⟨by omega, by omega⟩).trans hm8_5,
    (Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m (by omega) (by omega) ⟨by omega, by omega⟩).trans hm16_5,
    (Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m (by omega) (by omega) ⟨by omega, by omega⟩).trans hm24_5,
    (Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m (by omega) (by omega) ⟨by omega, by omega⟩).trans hm32_5⟩

private theorem balEnsureAlloc_transfer {F : Type}
    {s s1 s5 mid : PanSemStateFiniteExact 64 F}
    {tw pw t0w t8w l16w l24w l32w : BitVec 64} {S0 Nd0 : List Nat}
    (hAR : ArenaReady s) (hA5 : ArenaReady s5) (hAm : ArenaReady mid)
    (hW0 : WorldTypedWith s S0 Nd0)
    (ht_eq : tw.toNat = globN s "bal_accounts")
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hWF_tw : HtabWF s tw.toNat)
    (hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hpw_eq : pw.toNat = globN s "heap_ptr") (hpw8 : pw.toNat % 8 = 0)
    (hpw_t0 : pw.toNat + 40 ≤ t0w.toNat) (ht0_s1 : t0w.toNat + 88 ≤ globN s1 "heap_ptr")
    (hs1_t8 : globN s1 "heap_ptr" ≤ t8w.toNat) (ht8_l16 : t8w.toNat + 88 ≤ l16w.toNat)
    (hl16_l24 : l16w.toNat + 24 + 160 = l24w.toNat)
    (hl24_l32 : l24w.toNat + 24 + 64 = l32w.toNat)
    (hl32_s5 : l32w.toNat + 24 + 48 = globN s5 "heap_ptr")
    (hbe5 : s5.be = s.be) (hsp5 : globN s5 "scratch_ptr" = globN s "scratch_ptr")
    (hgl5 : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = s5.globals.lookup k)
    (hfr_05 : FrameOutside s s5 [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN s5 "heap_ptr" - globN s "heap_ptr"))
    (hwf_t0_5 : HtabWF s5 t0w.toNat) (hcnt_t0_5 : hdr s5 t0w.toNat 3 = 0)
    (hkey_t0_5 : hdr s5 t0w.toNat 0 = 32)
    (hfp_t0_5 : ∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr"))
    (hwf_t8_5 : HtabWF s5 t8w.toNat)
    (hkey_t8_5 : hdr s5 t8w.toNat 0 = 32)
    (hfp_t8_5 : ∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat)
    (hpw_tabs_5 : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j)
    (hm0_5 : memW s5 pw.toNat = t0w.toNat) (hm8_5 : memW s5 (pw.toNat + 8) = t8w.toNat)
    (hm16_5 : memW s5 (pw.toNat + 16) = l16w.toNat) (hm24_5 : memW s5 (pw.toNat + 24) = l24w.toNat)
    (hm32_5 : memW s5 (pw.toNat + 32) = l32w.toNat)
    (hlst16_5 : LstOK s5 l16w.toNat) (hobjs16_5 : lstObjects s5 l16w.toNat 40 = [(l16w.toNat, 24), (l16w.toNat + 24, 160)])
    (hlst24_5 : LstOK s5 l24w.toNat) (hobjs24_5 : lstObjects s5 l24w.toNat 16 = [(l24w.toNat, 24), (l24w.toNat + 24, 64)])
    (hlst32_5 : LstOK s5 l32w.toNat) (hobjs32_5 : lstObjects s5 l32w.toNat 24 = [(l32w.toNat, 24), (l32w.toNat + 24, 48)])
    (hexit : SoloHtabSet.HtabExitAt tw.toNat s5 mid)
    (hvalues_5m : HtabSetValuesPost s5 mid tw.toNat pw.toNat)
    (hbe_mid : mid.be = s5.be) (hmem_rec : pw.toNat ∈ balRecords mid) :
    globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep
      (fun _ _ post _ _ => pw.toNat ∈ balRecords post) s
      (some (.returned (.val (.word pw)))) mid := by
  obtain ⟨hAm_exit, hwf_tw_m, hhdr0_tw_5m, _, hhp_5m, hfp_tw_m, hfr_5m, hgl_5m⟩ := hexit
  have hsp8 : (globN s "scratch_ptr") % 8 = 0 := hAR.2.2.2.2.2.2.2.2.1
  have hhp_05 : globN s "heap_ptr" ≤ globN s5 "heap_ptr" := by omega
  have hhp_0m : globN s "heap_ptr" ≤ globN mid "heap_ptr" := le_trans hhp_05 hhp_5m
  have hgk : GlobalsKept ["heap_ptr"] s mid := by
    intro k hk
    have hk' : k ≠ ofString "heap_ptr" := fun heq => hk (by simp [heq])
    exact (hgl5 k hk').trans (hgl_5m k hk)
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s mid :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hgk (fun name h => Or.inl (by simpa using h))
  have hsp_mid : globN mid "scratch_ptr" = globN s "scratch_ptr" :=
    Wave8Contracts.M08.globN_eq_of_lookup (hgk (ofString "scratch_ptr") (by decide))
  have hfmp_s5 : globN s5 "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    Wave8Contracts.M08.globN_eq_of_lookup (hgl5 (ofString "frame_mem_ptr") (by decide))
  have hbe_0m : mid.be = s.be := hbe_mid.trans hbe5
  have hu_tw_05 : ∀ i ∈ htabFootprint s tw.toNat, M08IvlUnhit s s5 i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_05
    · intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact hsp8
    · exact hAR.2.2.2.2.2.2.1
    · intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact Or.inr (Or.inl rfl)
    · exact disj_fresh_of_zero_or_allocated_add hAR.2 hA5.2 hhp_05 (Or.inr (hal_tw i hi))
  obtain ⟨hwf_tw_5, hfp_tw_5, hhdr_tw_05⟩ :=
    htabWF_transfer_unhit hAR hA5 hWF_tw hu_tw_05
      (fun i hi => AllocatorGrows.allocated (show AllocatorGrows s s5 from ⟨hhp_05, by omega⟩) (hal_tw i hi))
  have hhdr0_tw_m : hdr mid tw.toNat 0 = hdr s tw.toNat 0 :=
    hhdr0_tw_5m.trans (hhdr_tw_05 0 (by omega))
  have hvals_tw_05 : htabValues s5 tw.toNat = htabValues s tw.toNat :=
    Wave8Contracts.M08.htabValues_eq_of_unhit hWF_tw hu_tw_05
  have hvalues_0m : HtabSetValuesPost s mid (globN s "bal_accounts") pw.toNat := by
    unfold HtabSetValuesPost at hvalues_5m ⊢
    rw [← ht_eq, ← hvals_tw_05]
    exact hvalues_5m
  have hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hkeep hfresh
    have h1 := hfr_5m a (fun j hj => by
      rw [hfp_tw_5] at hj
      exact hkeep j (List.mem_cons_of_mem _ hj))
      (fun ⟨hc1, hc2⟩ => hfresh ⟨by dsimp at hc1 ⊢; omega, by dsimp at hc2 ⊢; omega⟩)
    have h2 := hfr_05 a (fun j hj => by
      simp only [List.mem_singleton] at hj; subst hj
      exact hkeep _ List.mem_cons_self)
      (fun ⟨hc1, hc2⟩ => hfresh ⟨by dsimp at hc1 ⊢; omega, by dsimp at hc2 ⊢; omega⟩)
    exact h1.trans h2
  have hk_al_0m : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hsp8
    · exact (hWF_tw.1 j hj_fp).2.1
  have hu_5m_of_fresh05 : ∀ {i : Ivl},
      Inside i (globN s "heap_ptr") (globN s5 "heap_ptr") → M08IvlUnhit s5 mid i := by
    intro i hi_in
    apply m08_ivlUnhit_of_frameOutside_add hfr_5m
    · intro j hj; exact (hwf_tw_5.1 j hj).2.1
    · exact hA5.2.2.2.2.2.2.1
    · intro j hj
      rw [hfp_tw_5] at hj
      exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hA5.2 (hal_tw j hj) hi_in
    · exact Or.inr (Or.inr (Or.inl (by have := hi_in.2; dsimp; omega)))
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have h5_hi : globN s5 "heap_ptr" ≤ heapLimit := hA5.2.2.1
  obtain ⟨hm0_m, hm8_m, hm16_m, hm24_m, hm32_m⟩ :=
    balEnsureAlloc_pw_slots_mid h5_hi hpw8 (by omega)
      (hu_5m_of_fresh05 ⟨by dsimp; omega, by dsimp; omega⟩)
      hm0_5 hm8_5 hm16_5 hm24_5 hm32_5
  obtain ⟨hwf_t0_m, hfp_t0_m, hhdr_t0_m⟩ :=
    htabWF_transfer_unhit hA5 hAm hwf_t0_5
      (fun i hi => hu_5m_of_fresh05 ⟨le_trans (by omega) (hfp_t0_5 i hi).2.1, le_trans (hfp_t0_5 i hi).2.2 (by omega)⟩)
      (fun i hi => Or.inl ⟨by have := (hfp_t0_5 i hi).2.1; omega, by have := (hfp_t0_5 i hi).2.2; omega⟩)
  obtain ⟨hwf_t8_m, hfp_t8_m, hhdr_t8_m⟩ :=
    htabWF_transfer_unhit hA5 hAm hwf_t8_5
      (fun i hi => hu_5m_of_fresh05 ⟨le_trans (by omega) (hfp_t8_5 i hi).2.1, le_trans (hfp_t8_5 i hi).2.2 (by omega)⟩)
      (fun i hi => Or.inl ⟨by have := (hfp_t8_5 i hi).2.1; omega, by have := (hfp_t8_5 i hi).2.2; omega⟩)
  have hcnt_t0_m : hdr mid t0w.toNat 3 = 0 := (hhdr_t0_m 3 (by omega)).trans hcnt_t0_5
  have hkey_t0_m : hdr mid t0w.toNat 0 = 32 := (hhdr_t0_m 0 (by omega)).trans hkey_t0_5
  have hkey_t8_m : hdr mid t8w.toNat 0 = 32 := (hhdr_t8_m 0 (by omega)).trans hkey_t8_5
  have hvals_t0_m : htabValues mid t0w.toNat = [] := by
    unfold htabValues; rw [hcnt_t0_m]; rfl
  have hl32_8 : l32w.toNat % 8 = 0 := by
    have h := hA5.2.2.2.2.2.2.1; omega
  have hl24_8 : l24w.toNat % 8 = 0 := by omega
  have hl16_8 : l16w.toNat % 8 = 0 := by omega
  obtain ⟨hlst16_m, hobjs16_m⟩ := balEnsureAlloc_lst_mid l16w.toNat 40 4 h5_hi hl16_8 (by omega) (by omega)
    (hu_5m_of_fresh05 ⟨by dsimp; omega, by dsimp; omega⟩) hlst16_5 hobjs16_5
  obtain ⟨hlst24_m, hobjs24_m⟩ := balEnsureAlloc_lst_mid l24w.toNat 16 4 h5_hi hl24_8 (by omega) (by omega)
    (hu_5m_of_fresh05 ⟨by dsimp; omega, by dsimp; omega⟩) hlst24_5 hobjs24_5
  obtain ⟨hlst32_m, hobjs32_m⟩ := balEnsureAlloc_lst_mid l32w.toNat 24 2 h5_hi hl32_8 (by omega) (by omega)
    (hu_5m_of_fresh05 ⟨by dsimp; omega, by dsimp; omega⟩) hlst32_5 hobjs32_5
  have hm0_8_16 := balEnsureAlloc_low_words hAR hWF_tw hal_tw hfr_0m
  refine ⟨hsp_mid, hAm, hhp_0m, hgk,
    balEnsureAlloc_recordsKept hAR hAm hW0 ht_eq hba_nz hgs hhp_0m hWF_tw hfr_0m, ?_⟩
  intro S Nd hWT _
  exact balEnsureAlloc_worldStep_core hAR hA5 hAm hWT ht_eq hba_nz hgk hsp_mid hhp_05 hhp_5m
    hbe_0m hpw_eq hpw8 hpw_t0 ht0_s1 hs1_t8 ht8_l16 hl16_l24 hl24_l32 hl32_s5
    hfr_0m hfp_tw_5 hhdr0_tw_m hwf_tw_m hfp_tw_m hvalues_0m
    hwf_t0_m hwf_t8_m hfp_t0_m hfp_t8_m hfp_t0_5 hfp_t8_5 hpw_tabs_5
    hkey_t0_m hkey_t8_m hvals_t0_m hm0_m hm8_m hm16_m hm24_m hm32_m
    hlst16_m hobjs16_m hlst24_m hobjs24_m hlst32_m hobjs32_m hm0_8_16 hmem_rec

private theorem balEnsureAlloc_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (tw kw : BitVec 64)
    (hWOK : WorldOK s)
    (hroot : s.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)))
    (ht_nz : tw ≠ 0)
    (hak : s.locals.lookup (ofString "addr") = some (.val (.word kw)))
    (hnt : (evaluateHOLFiniteState s balEnsureAllocProg).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s balEnsureAllocProg).1) :
    ∃ (pw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s balEnsureAllocProg).1 = some (.returned (.val (.word pw))) ∧
      (∃ L_out, (evaluateHOLFiniteState s balEnsureAllocProg).2 = { mid with locals := L_out }) ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep
        (fun _ _ post _ _ => pw.toNat ∈ balRecords post) s
        (some (.returned (.val (.word pw)))) mid := by
  have hAR : ArenaReady s := hWOK.1
  have ht_eq : tw.toNat = globN s "bal_accounts" := by
    simp [globN, hroot]
  obtain ⟨S0, hWT0⟩ := hWOK.2
  obtain ⟨Nd0, hW0⟩ := (worldTyped_iff_with s S0).1 hWT0
  have hba_nz : globN s "bal_accounts" ≠ 0 := by
    intro h0; apply ht_nz; apply BitVec.eq_of_toNat_eq; simp [ht_eq, h0]
  have htw_nz : tw.toNat ≠ 0 := by rw [ht_eq]; exact hba_nz
  have hba_S0 : tw.toNat ∈ S0 := by
    rw [ht_eq]
    rcases hW0.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hba_nz
    · exact hm
  have hWF_tw : HtabWF s tw.toNat := (hW0.1.2.1 _ hba_S0).1
  have hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i :=
    fun i hi => ((hW0.1.2.1 _ hba_S0).2 i hi).1
  obtain ⟨pw, t0w, t8w, l16w, l24w, l32w, s1, s5, mid,
    hpw_eq, hpw8, _,
    hpw_t0, ht0_s1, hs1_t8, ht8_l16, hl16_l24, hl24_l32, hl32_s5,
    hA5, hbe5, hsp5, hgl5, hfr_05,
    hwf_t0_5, hcnt_t0_5, hkey_t0_5, hfp_t0_5,
    hwf_t8_5, _, hkey_t8_5, hfp_t8_5, hpw_tabs_5,
    hm0_5, hm8_5, hm16_5, hm24_5, hm32_5,
    hlst16_5, hobjs16_5, hlst24_5, hobjs24_5, hlst32_5, hobjs32_5,
    hexit, hvalues_5m, hbe_mid, hmem_rec, hev_fst, hev_snd⟩ :=
    balEnsureAlloc_eval s tw kw hAR hroot hak htw_nz hWF_tw hal_tw hnt hres
  obtain ⟨hsp_mid, hWS⟩ := balEnsureAlloc_transfer hAR hA5 hexit.1 hW0 ht_eq hba_nz hWF_tw hal_tw
    hpw_eq hpw8 hpw_t0 ht0_s1 hs1_t8 ht8_l16 hl16_l24 hl24_l32 hl32_s5
    hbe5 hsp5 hgl5 hfr_05 hwf_t0_5 hcnt_t0_5 hkey_t0_5 hfp_t0_5
    hwf_t8_5 hkey_t8_5 hfp_t8_5 hpw_tabs_5 hm0_5 hm8_5 hm16_5 hm24_5 hm32_5
    hlst16_5 hobjs16_5 hlst24_5 hobjs24_5 hlst32_5 hobjs32_5
    hexit hvalues_5m hbe_mid hmem_rec
  exact ⟨pw, mid, hev_fst, hev_snd, hsp_mid, hWS⟩

private theorem balRecord_slot_load {F : Type}
    (s : PanSemStateFiniteExact 64 F) (adw off : BitVec 64) (adExp : ExpHOL 64)
    (hW : WorldOK s)
    (had_rec : adw.toNat ∈ balRecords s)
    (hev_ad : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) adExp =
      some (.val (.word adw)))
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ 40) :
    adw ≠ 0 ∧ adw.toNat % 8 = 0 ∧ sourceBase ≤ adw.toNat ∧ adw.toNat + 40 ≤ heapEnd ∧
    ∃ fw : BitVec 64,
      fw.toNat = memW s (adw.toNat + off.toNat) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [adExp, .const off])) = some (.val (.word fw)) := by
  have hAR : ArenaReady s := hW.1
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have had_fix : (adw.toNat, 40) ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append_right; unfold balObjects
    exact List.mem_flatMap.2 ⟨adw.toNat, had_rec, List.mem_cons_self⟩
  rcases hWT0.2.2.1.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
  · cases h0
  have had_bnd : adw.toNat + 40 ≤ heapEnd ∧ adw.toNat + 40 ≤ 2 ^ 64 :=
    ivl_allocated_bound hAR.2 hal_ad
  have had_lo : sourceBase ≤ adw.toNat := by
    rcases hal_ad with h | h
    · exact h.1
    · have h1 := hAR.2.2.2.1; have h2 := hAR.2.2.2.2.1
      have h3 : sourceBase ≤ scratchStart := by decide
      exact le_trans h3 (le_trans h1 (le_trans h2 h.1))
  have hsb_pos : 0 < sourceBase := by decide
  have had_nz : adw ≠ 0 := by
    intro h0; subst h0; simp at had_lo; omega
  have had_align : adw.toNat % 8 = 0 := hw_ad.1
  have had_add_lt : adw.toNat + off.toNat < 2 ^ 64 := by omega
  have had_add_bv : adw + off = BitVec.ofNat 64 (adw.toNat + off.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hdom : s.memaddrs (adw + off) := by
    rw [hAR.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, had_add_bv,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt had_add_lt]
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨fw, _, hfw_mem0⟩ := hw_ad.2.2 (off.toNat / 8) (Nat.div_lt_of_lt_mul (by omega))
  have hfw_mem : s.memory (adw + off) = .word fw := by
    have heq_addr : BitVec.ofNat 64 (adw.toNat + 8 * (off.toNat / 8)) = adw + off := by
      rw [had_add_bv]; apply congrArg (BitVec.ofNat 64)
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hoff8)]
    rw [← heq_addr]; exact hfw_mem0
  have hfw_nat : fw.toNat = memW s (adw.toNat + off.toNat) := by
    change fw.toNat = (match s.memory (BitVec.ofNat 64 (adw.toNat + off.toNat)) with | .word w => w.toNat)
    rw [← had_add_bv, hfw_mem]
  have hz_off : off + 0 = off := BitVec.add_zero _
  refine ⟨had_nz, had_align, had_lo, had_bnd.1, fw, hfw_nat, ?_⟩
  simp [evalHOLExact, evalListHOLExact, hev_ad, valueIsWord, valueWord, wordOpHOL, wordOp,
    hz_off, memLoadHOLExact, isWfShapeExactHOL, hdom, hfw_mem]

theorem decCall_bal_ensure_account_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (addrExp : ExpHOL 64) (addrw : BitVec 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (hev_addr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word addrw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont)).1) :
    ∃ (adw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      adw ≠ 0 ∧
      adw.toNat % 8 = 0 ∧
      sourceBase ≤ adw.toNat ∧
      adw.toNat + 40 ≤ heapEnd ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid ∧
      WorldOK mid ∧
      adw.toNat ∈ balRecords mid ∧
      (∀ off : BitVec 64, off.toNat % 8 = 0 → off.toNat + 8 ≤ 40 →
        ∃ fw : BitVec 64,
          fw.toNat = memW mid (adw.toNat + off.toNat) ∧
          @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
            (.load .one (.op .add [.var .local x, .const off])) = some (.val (.word fw))) ∧
      mid.locals.lookup x = some (.val (.word adw)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hAs := hW.1
  have hG := hAs.1
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [addrExp] = some [.val (.word addrw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev_addr]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "bal_ensure_account")
    (ofString "addr") (sourceFnBody Guest.Software.guestFn_bal_ensure_account) addrw
    (by rw [hG.code]; exact lookup_bal_ensure_account_add)
  rw [hargs] at hnt hres; dsimp only at hnt hres
  rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := HolFiniteMapExact.empty.update (ofString "addr", ValueHOL.val (.word addrw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_eq : ent = { s with locals := cmap, clock := s.clock - 1 } := rfl
    have hent_W : WorldOK ent := (worldOK_with_locals s cmap (s.clock - 1)).2 hW
    have hent_G : GuestInv ent := hent_W.1.1
    have hent_addr : ent.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hbody_out : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_bal_ensure_account) with ⟨rb, sb⟩
    have hbody_out' : evaluateHOLFiniteState ent
        (sourceFnBody Guest.Software.guestFn_bal_ensure_account) = (rb, sb) := hbody_out
    rw [hbody_out] at hnt hres
    have hbody_nt : (evaluateHOLFiniteState ent
        (sourceFnBody Guest.Software.guestFn_bal_ensure_account)).1 ≠ some .timeOut := by
      rw [hbody_out']; intro hto; dsimp only at hto; subst hto; exact hnt rfl
    have hbody_res : Resumes (evaluateHOLFiniteState ent
        (sourceFnBody Guest.Software.guestFn_bal_ensure_account)).1 := by
      rw [hbody_out']; dsimp only
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
            exact bal_ensure_account_no_catchable_exn_add ent hG.code e ev hne
              (congrArg Prod.fst hbody_out')
        | returned vb => exact Or.inl ⟨vb, rfl⟩
    set cont_m : ProgHOL 64 :=
      .seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
              (.return (.rfield 1 (.var .local (ofString "m")))) .skip)
        balEnsureAllocProg
    have hfn_eq : sourceFnBody Guest.Software.guestFn_bal_ensure_account =
        .decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
          [.var .global (ofString "bal_accounts"), .var .local (ofString "addr")] cont_m := rfl
    rw [hfn_eq] at hbody_nt hbody_res hbody_out'
    obtain ⟨tw, kw, f0, f1, ck, hev_t, hev_k, htw_nz, hf1_val, hnt1, hres1, heq1_r, heq1_s⟩ :=
      decCall_htab_get_resumes ent (ofString "m")
        (.var .global (ofString "bal_accounts")) (.var .local (ofString "addr")) cont_m
        hent_G hbody_nt hbody_res
    set s1 := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
      { ent with clock := ck }
    have hs1_eq : s1 = { s with locals := s1.locals, clock := ck } := rfl
    have hs1_W : WorldOK s1 := (worldOK_with_locals s s1.locals ck).2 hW
    have hs1_m : s1.locals.lookup (ofString "m") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_addr : s1.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "addr" by decide, hent_addr]
    obtain ⟨baw, hbaw⟩ := hAs.2.2.2.2.2.2.2.2.2 "bal_accounts" (by decide)
    have hbaw_s : s.globals.lookup (ofString "bal_accounts") = some (.val (.word baw)) := hbaw
    have htw_eq : tw = baw := by
      have hbaw_ent : ent.globals.lookup (ofString "bal_accounts") = some (.val (.word baw)) := hbaw_s
      simp [evalHOLExact, hbaw_ent] at hev_t; exact hev_t.symm
    subst htw_eq
    have hroot_nat : globN s "bal_accounts" = tw.toNat := by simp [globN, hbaw_s]
    by_cases hf0 : f0 = 0
    · subst hf0
      have hmiss := bal_ensure_missing_tail s1 f1 balEnsureAllocProg hs1_m
      change evaluateHOLFiniteState s1 cont_m = evaluateHOLFiniteState s1 balEnsureAllocProg at hmiss
      rw [hmiss] at hnt1 hres1 heq1_r heq1_s
      obtain ⟨adw, mid_a, ha_fst, ⟨L_out, ha_snd⟩, _, hws_a⟩ :=
        balEnsureAlloc_worldStep s1 tw addrw hs1_W hbaw_s htw_nz hs1_addr hnt1 hres1
      let mid : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite x (.val (.word adw)) { sb with locals := s.locals }
      have hrb_eq : rb = some (.returned (.val (.word adw))) := by
        have h1 := congrArg Prod.fst hbody_out'
        dsimp only at h1; rw [← h1, heq1_r, ha_fst]
      have hsb_eq : sb =
          { mid_a with
            locals := HolFiniteMapExact.resVarEq L_out
              (ofString "m", ent.locals.lookup (ofString "m")) } := by
        have h2 := congrArg Prod.snd hbody_out'
        dsimp only at h2; rw [← h2, heq1_s, ha_snd]
      have hmid_eq : mid = { mid_a with locals := s.locals.update (x, .val (.word adw)) } := by
        simp [mid, hsb_eq, setVarHOLFinite]
      have hws_s_mid_a : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
          (fun _ _ post _ _ => adw.toNat ∈ balRecords post) s none mid_a :=
        worldStep_with_locals_left hs1_eq rfl (fun _ _ h => h) hws_a
      have hws_s_mid_rec : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
          (fun _ _ post _ _ => adw.toNat ∈ balRecords post) s none mid := by
        rw [hmid_eq]
        exact worldStep_with_locals_right _ mid_a.clock (fun _ _ h => h) hws_s_mid_a
      have hws_total : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
        worldStep_weaken (fun _ h => h) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
          (fun _ _ _ _ hi => False.elim (List.not_mem_nil hi)) (fun _ _ _ => trivial) hws_s_mid_rec
      have hW_mid : WorldOK mid := worldOK_of_step hW hws_total
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      obtain ⟨_, _, _, _, _, _, had_rec⟩ :=
        hws_s_mid_rec.2.2.2.2 S0 Nd0 hWT0 (fun _ hi => False.elim (List.not_mem_nil hi))
      have hmid_x : mid.locals.lookup x = some (.val (.word adw)) := by
        simp [hmid_eq, HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_other : ∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y := by
        intro y hy; simp [hmid_eq, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy]
      have hev_x : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.var .local x) = some (.val (.word adw)) := by
        simp [evalHOLExact, hmid_x]
      obtain ⟨had_nz, had8, had_lo, had_hi, _⟩ :=
        balRecord_slot_load mid adw 0#64 (.var .local x) hW_mid had_rec hev_x (by decide) (by decide)
      have hsh_ad : (shapeEqHOL (shapeOfHOLExact (.val (.word adw) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word adw) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      subst rb
      dsimp only at hnt hres
      rw [if_pos hsh_ad] at hnt hres
      have heval_eq : evaluateHOLFiniteState s
          (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont) =
          ((evaluateHOLFiniteState mid cont).1,
            { (evaluateHOLFiniteState mid cont).2 with
              locals := HolFiniteMapExact.resVarEq
                (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]; dsimp only
        rw [hlk]; dsimp only; rw [if_neg hcz, hbody_out]; dsimp only
        rw [if_pos hsh_ad]
      refine ⟨adw, mid, had_nz, had8, had_lo, had_hi, hws_total, hW_mid, had_rec,
        fun off hoff8 hoff_hi =>
          (balRecord_slot_load mid adw off (.var .local x) hW_mid had_rec hev_x hoff8 hoff_hi).2.2.2.2,
        hmid_x, hmid_other, hnt, hres, by rw [heval_eq], by rw [heval_eq]⟩
    · obtain ⟨hex_ev, _⟩ := bal_ensure_existing_tail s1 f0 f1 balEnsureAllocProg hs1_W hs1_m hf0
      change evaluateHOLFiniteState s1 cont_m =
        (some (.returned (.val (.word f1))), emptyLocalsHOLFinite s1) at hex_ev
      let mid : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite x (.val (.word f1)) { sb with locals := s.locals }
      have hrb_eq : rb = some (.returned (.val (.word f1))) := by
        have h1 := congrArg Prod.fst hbody_out'
        dsimp only at h1; rw [← h1, heq1_r, hex_ev]
      have hsb_eq : sb =
          { emptyLocalsHOLFinite s1 with
            locals := HolFiniteMapExact.resVarEq
              (emptyLocalsHOLFinite s1).locals (ofString "m", ent.locals.lookup (ofString "m")) } := by
        have h2 := congrArg Prod.snd hbody_out'
        dsimp only at h2; rw [← h2, heq1_s, hex_ev]
      have hmid_eq : mid = { s with locals := s.locals.update (x, .val (.word f1)), clock := ck } := by
        dsimp only [mid]
        rw [hsb_eq]
        dsimp only [setVarHOLFinite, emptyLocalsHOLFinite]
        rw [hs1_eq]
      have hws_total : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
        worldStep_refl (fun _ => []) ["heap_ptr"] hAs (by rw [hmid_eq])
      have hW_mid : WorldOK mid := by rw [hmid_eq]; exact (worldOK_with_locals s _ ck).2 hW
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      have hf1_rec_s : f1.toNat ∈ balRecords s :=
        bal_lookup_value_record hroot_nat htw_nz hf0
          (fun hwf_s => hf1_val ((htabWF_with_locals s cmap (s.clock - 1) tw.toNat).2 hwf_s)) hWT0
      have hf1_rec : f1.toNat ∈ balRecords mid := by
        have hbr : balRecords mid = balRecords s := by
          rw [hmid_eq]; rfl
        rw [hbr]; exact hf1_rec_s
      have hmid_x : mid.locals.lookup x = some (.val (.word f1)) := by
        simp [hmid_eq, HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_other : ∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y := by
        intro y hy; simp [hmid_eq, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy]
      have hev_x : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.var .local x) = some (.val (.word f1)) := by
        simp [evalHOLExact, hmid_x]
      obtain ⟨had_nz, had8, had_lo, had_hi, _⟩ :=
        balRecord_slot_load mid f1 0#64 (.var .local x) hW_mid hf1_rec hev_x (by decide) (by decide)
      have hsh_f1 : (shapeEqHOL (shapeOfHOLExact (.val (.word f1) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word f1) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      subst rb
      dsimp only at hnt hres
      rw [if_pos hsh_f1] at hnt hres
      have heval_eq : evaluateHOLFiniteState s
          (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont) =
          ((evaluateHOLFiniteState mid cont).1,
            { (evaluateHOLFiniteState mid cont).2 with
              locals := HolFiniteMapExact.resVarEq
                (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]; dsimp only
        rw [hlk]; dsimp only; rw [if_neg hcz, hbody_out]; dsimp only
        rw [if_pos hsh_f1]
      refine ⟨f1, mid, had_nz, had8, had_lo, had_hi, hws_total, hW_mid, hf1_rec,
        fun off hoff8 hoff_hi =>
          (balRecord_slot_load mid f1 off (.var .local x) hW_mid hf1_rec hev_x hoff8 hoff_hi).2.2.2.2,
        hmid_x, hmid_other, hnt, hres, by rw [heval_eq], by rw [heval_eq]⟩

private def addCodeTailProg : ProgHOL 64 :=
  .seq
    (.store (.op .add [.var .local (ofString "e"), .const 8#64]) (.var .local (ofString "code")))
    (.seq
      (.store (.op .add [.var .local (ofString "e"), .const 16#64]) (.var .local (ofString "code_len")))
      (.return (.const 0#64)))

private theorem add_code_change_tail_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (lw ew codew clenw : BitVec 64)
    (hW : WorldOK s)
    (hlw_nz : lw ≠ 0)
    (horig : ∀ S Nd, WorldTypedWith s S Nd → LstOK s lw.toNat ∧ BalListOrigin s lw.toNat 24)
    (hew8 : ew.toNat % 8 = 0)
    (hew_sb : sourceBase ≤ ew.toNat)
    (hew_he : ew.toNat + 24 ≤ heapEnd)
    (hew_lo : memW s lw.toNat ≤ ew.toNat)
    (hew_hi : ew.toNat + 24 ≤ memW s lw.toNat + 24 * memW s (lw.toNat + 16))
    (hs_e : s.locals.lookup (ofString "e") = some (.val (.word ew)))
    (hs_code : s.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs_clen : s.locals.lookup (ofString "code_len") = some (.val (.word clenw))) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s addCodeTailProg).1
      (evaluateHOLFiniteState s addCodeTailProg).2 := by
  have he8_lt : ew.toNat + 8 < 2 ^ 64 := by
    have hhe : heapEnd ≤ 2 ^ 64 := by decide
    omega
  have he16_lt : ew.toNat + 16 < 2 ^ 64 := by
    have hhe : heapEnd ≤ 2 ^ 64 := by decide
    omega
  have he8_toNat : (ew + 8#64).toNat = ew.toNat + 8 := by
    rw [BitVec.toNat_add]
    change (ew.toNat + 8) % 2 ^ 64 = ew.toNat + 8
    exact Nat.mod_eq_of_lt he8_lt
  have he16_toNat : (ew + 16#64).toNat = ew.toNat + 16 := by
    rw [BitVec.toNat_add]
    change (ew.toNat + 16) % 2 ^ 64 = ew.toNat + 16
    exact Nat.mod_eq_of_lt he16_lt
  have hdom8 : s.memaddrs (ew + 8#64) := by
    rw [hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he8_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hz8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
  have hz16 : (16#64 : BitVec 64) + 0 = 16#64 := BitVec.add_zero _
  have hev_dst1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "e"), .const 8#64]) = some (.val (.word (ew + 8#64))) := by
    simp [evalHOLExact, evalListHOLExact, hs_e, valueIsWord, valueWord, wordOpHOL, wordOp, hz8]
  have hev_val1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "code")) = some (.val (.word codew)) := by
    simp [evalHOLExact, hs_code]
  let st1 : PanSemStateFiniteExact 64 F :=
    { s with memory := fun a => if a = ew + 8#64 then .word codew else s.memory a }
  have hst1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "e"), .const 8#64]) (.var .local (ofString "code"))) =
      (none, st1) := by
    rw [evaluateHOLFiniteState_store, hev_dst1, hev_val1]
    simp only [flattenHOL]
    unfold panMemStoresHOL panMemStoreHOL
    rw [if_pos hdom8]; rfl
  have hdom16 : st1.memaddrs (ew + 16#64) := by
    dsimp only [st1]
    rw [hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he16_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hev_dst2 : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
      (.op .add [.var .local (ofString "e"), .const 16#64]) = some (.val (.word (ew + 16#64))) := by
    simp [evalHOLExact, evalListHOLExact, st1, hs_e, valueIsWord, valueWord, wordOpHOL, wordOp, hz16]
  have hev_val2 : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
      (.var .local (ofString "code_len")) = some (.val (.word clenw)) := by
    simp [evalHOLExact, st1, hs_clen]
  let st2 : PanSemStateFiniteExact 64 F :=
    { st1 with memory := fun a => if a = ew + 16#64 then .word clenw else st1.memory a }
  have hst2 : evaluateHOLFiniteState st1
      (.store (.op .add [.var .local (ofString "e"), .const 16#64]) (.var .local (ofString "code_len"))) =
      (none, st2) := by
    rw [evaluateHOLFiniteState_store, hev_dst2, hev_val2]
    simp only [flattenHOL]
    unfold panMemStoresHOL panMemStoreHOL
    rw [if_pos hdom16]; rfl
  have hret : evaluateHOLFiniteState st2 (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite st2) := by
    rw [evaluateHOLFiniteState_return]
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos (by decide)]
  have htot : evaluateHOLFiniteState s addCodeTailProg =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite st2) := by
    dsimp only [addCodeTailProg]
    rw [evaluateHOLFiniteState_seq_line780, hst1]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hst2]; dsimp only
    exact hret
  let Rl : List Ivl := [(memW s lw.toNat, 24 * memW s (lw.toNat + 16))]
  have hbre1 : ByteRegionEffect s st1 Rl := by
    refine (bre_of_store_multi hW.1.1.memaddrs (nw := 1) (by omega) hst1
      (fun v hv => by
        rw [hev_val1] at hv; injection hv with hv'; subst hv'; simp [flattenHOL])
      (fun addr hdst _ => ?_)).1
    rw [hev_dst1] at hdst; injection hdst with hd; injection hd with hd'; injection hd' with hd''; subst hd''
    refine ⟨by rw [he8_toNat]; omega, (memW s lw.toNat, 24 * memW s (lw.toNat + 16)),
      List.mem_singleton.2 rfl, by rw [he8_toNat]; omega, by dsimp only; rw [he8_toNat]; omega⟩
  have hbre2 : ByteRegionEffect st1 st2 Rl := by
    have hma1 : st1.memaddrs = ordinaryDomain := hW.1.1.memaddrs
    refine (bre_of_store_multi (s := st1) (post := st2) hma1 (nw := 1) (by omega) hst2
      (fun v hv => by
        rw [hev_val2] at hv; injection hv with hv'; subst hv'; simp [flattenHOL])
      (fun addr hdst _ => ?_)).1
    rw [hev_dst2] at hdst; injection hdst with hd; injection hd with hd'; injection hd' with hd''; subst hd''
    refine ⟨by rw [he16_toNat]; omega, (memW s lw.toNat, 24 * memW s (lw.toNat + 16)),
      List.mem_singleton.2 rfl, by rw [he16_toNat]; omega, by dsimp only; rw [he16_toNat]; omega⟩
  have hbre_st2 : ByteRegionEffect s st2 Rl := hbre1.trans hbre2
  have hbre_emp : ByteRegionEffect s (emptyLocalsHOLFinite st2) Rl :=
    hbre_st2.with_locals_clock (emptyLocalsHOLFinite st2).locals st2.clock
  have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [htot]; dsimp only
  exact (bal_list_store_arr_worldStep
    (r := some (.returned (.val (.word 0#64))))
    hW hlw_nz_nat (Or.inr (Or.inl rfl)) horig hbre_emp).1

private theorem add_code_change_body_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (addrw idxw codew clenw : BitVec 64)
    (hW : WorldOK s)
    (hs_addr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)))
    (hs_idx : s.locals.lookup (ofString "idx") = some (.val (.word idxw)))
    (hs_code : s.locals.lookup (ofString "code") = some (.val (.word codew)))
    (hs_clen : s.locals.lookup (ofString "code_len") = some (.val (.word clenw)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_code_change)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_code_change)).1) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_code_change)).1
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_code_change)).2 := by
  have hAR0 : ArenaReady s := hW.1
  set cont1 : ProgHOL 64 :=
    .decCall (ofString "e") .one (ofString "lst_upsert_idx")
      [.load .one (.op .add [.var .local (ofString "ad"), .const 32#64]),
       .const 24#64, .var .local (ofString "idx")]
      addCodeTailProg
  have hbody_eq : sourceFnBody Guest.Software.guestFn_add_code_change =
      .decCall (ofString "ad") .one (ofString "bal_ensure_account")
        [.var .local (ofString "addr")] cont1 := rfl
  rw [hbody_eq] at hnt hres ⊢
  obtain ⟨adw, mid1, _, _, _, _, hws1, hW1, had_rec1, hslot1,
      _, hmid1_other, hnt1, hres1, heq1_r, heq1_s⟩ :=
    decCall_bal_ensure_account_resumes s (ofString "ad")
      (.var .local (ofString "addr")) addrw cont1 hW
      (by simp [evalHOLExact, hs_addr]) hnt hres
  obtain ⟨lw, hlw_nat, hev_l⟩ := hslot1 32#64 (by decide) (by decide)
  have hmid1_idx : mid1.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
    rw [hmid1_other _ (by decide)]; exact hs_idx
  have hmid1_code : mid1.locals.lookup (ofString "code") = some (.val (.word codew)) := by
    rw [hmid1_other _ (by decide)]; exact hs_code
  have hmid1_clen : mid1.locals.lookup (ofString "code_len") = some (.val (.word clenw)) := by
    rw [hmid1_other _ (by decide)]; exact hs_clen
  have horig1 : lw ≠ 0 → ∀ S Nd, WorldTypedWith mid1 S Nd →
      LstOK mid1 lw.toNat ∧ BalListOrigin mid1 lw.toNat (24#64 : BitVec 64).toNat := by
    intro _ S Nd hWT1
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    have h24 : (24#64 : BitVec 64).toNat = 24 := rfl
    have hlw_m32 : memW mid1 (adw.toNat + 32) = lw.toNat := by
      rw [← h32]; exact hlw_nat.symm
    have hlst1 : LstOK mid1 lw.toNat := by
      rw [← hlw_m32]
      exact (hWT1.1.2.2.2.2.2.2.2.2.2.1 adw.toNat had_rec1).2.2.1 32 (by decide)
    exact ⟨hlst1, Or.inl ⟨adw.toNat, had_rec1, Or.inr (Or.inr ⟨hlw_m32, h24⟩)⟩⟩
  obtain ⟨ew, mid2, hlw_nz, hws2, hW2, horig2, hew8, hew_sb, hew_he, hew_lo, hew_hi,
      hmid2_e, hmid2_other, _, _, heq2_r, heq2_s⟩ :=
    decCall_lst_upsert_idx_resumes mid1 (ofString "e")
      (.load .one (.op .add [.var .local (ofString "ad"), .const 32#64]))
      (.const 24#64) (.var .local (ofString "idx"))
      lw 24#64 idxw addCodeTailProg hW1
      hev_l rfl (by simp [evalHOLExact, hmid1_idx])
      (Or.inr (Or.inl rfl)) horig1 hnt1 hres1
  have hmid2_code : mid2.locals.lookup (ofString "code") = some (.val (.word codew)) := by
    rw [hmid2_other _ (by decide)]; exact hmid1_code
  have hmid2_clen : mid2.locals.lookup (ofString "code_len") = some (.val (.word clenw)) := by
    rw [hmid2_other _ (by decide)]; exact hmid1_clen
  have hws3 := add_code_change_tail_worldStep mid2 lw ew codew clenw hW2 hlw_nz horig2
    hew8 hew_sb hew_he hew_lo hew_hi hmid2_e hmid2_code hmid2_clen
  have hws12 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid2 :=
    worldStep_hp_trans hAR0.2 hws1 hws2
  have hws123 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState mid2 addCodeTailProg).1
      (evaluateHOLFiniteState mid2 addCodeTailProg).2 :=
    worldStep_hp_trans hAR0.2 hws12 hws3
  rw [heq1_r, heq1_s]
  dsimp only [cont1]
  rw [heq2_r, heq2_s]
  let p3 := (evaluateHOLFiniteState mid2 addCodeTailProg).2
  have hupd :
      { { p3 with
          locals := HolFiniteMapExact.resVarEq p3.locals
            (ofString "e", mid1.locals.lookup (ofString "e")) } with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq p3.locals
            (ofString "e", mid1.locals.lookup (ofString "e")))
          (ofString "ad", s.locals.lookup (ofString "ad")) } =
      { p3 with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq p3.locals
            (ofString "e", mid1.locals.lookup (ofString "e")))
          (ofString "ad", s.locals.lookup (ofString "ad"))
        clock := p3.clock } := rfl
  dsimp only [p3] at hupd
  rw [hupd]
  exact worldStep_with_locals_right _ (evaluateHOLFiniteState mid2 addCodeTailProg).2.clock
    (fun _ _ _ => trivial) hws123

private theorem shapeOne_eq_word {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | _ | _
  · exact ⟨w, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at h
  · simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem ite_some_eq_some {α : Type} {P : Prop} [Decidable P] {a b : α}
    (h : (if P then some a else none) = some b) : P ∧ a = b := by
  by_cases hp : P
  · rw [if_pos hp] at h; exact ⟨hp, Option.some.inj h⟩
  · rw [if_neg hp] at h; cases h

private theorem lookupCode_four_word_any
    {codeLookup : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 p3 p4 : MlS} {body : ProgHOL 64} {rs : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne14 : p1 ≠ p4)
    (hne23 : p2 ≠ p3) (hne24 : p2 ≠ p4) (hne34 : p3 ≠ p4)
    (hlook : codeLookup fname =
      some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, rs))
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite codeLookup fname vals =
      some (body, L, rs)) :
    ∃ w1 w2 w3 w4 : BitVec 64,
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.val (.word w4)) := by
  have hx := lookupCodeHOLFinite_eq_some codeLookup fname vals body L rs hl
  unfold lookupCodeHOLExact at hx
  rw [hlook] at hx; dsimp only at hx
  obtain ⟨⟨_, hlen, hall⟩, heq⟩ := ite_some_eq_some hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · cases hlen
  · cases hlen
  · cases hlen
  · cases hlen
  · simp only [List.zip, List.zipWith, List.all, Bool.and_eq_true, Bool.and_true] at hall
    obtain ⟨w1, rfl⟩ := shapeOne_eq_word hall.1
    obtain ⟨w2, rfl⟩ := shapeOne_eq_word hall.2.1
    obtain ⟨w3, rfl⟩ := shapeOne_eq_word hall.2.2.1
    obtain ⟨w4, rfl⟩ := shapeOne_eq_word hall.2.2.2
    have hL_eq : (List.foldl
        (fun map (entry : MlS × ValueHOL 64) current =>
          if current = entry.1 then some entry.2 else map current)
        (fun _ => none)
        [(p1, .val (.word w1)), (p2, .val (.word w2)),
         (p3, .val (.word w3)), (p4, .val (.word w4))]) = L.lookup :=
      (Prod.mk.inj (Prod.mk.inj heq).2).1
    dsimp only [List.foldl] at hL_eq
    refine ⟨w1, w2, w3, w4, ?_, ?_, ?_, ?_⟩
    · have := congrFun hL_eq p1
      rw [← this, if_neg hne14, if_neg hne13, if_neg hne12, if_pos rfl]
    · have := congrFun hL_eq p2
      rw [← this, if_neg hne24, if_neg hne23, if_pos rfl]
    · have := congrFun hL_eq p3
      rw [← this, if_neg hne34, if_pos rfl]
    · have := congrFun hL_eq p4
      rw [← this, if_pos rfl]
  · cases hlen

theorem «wk_add_code_change» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "add_code_change") := by
  refine ⟨_, _, _, lookup_add_code_change_add, ?_⟩
  intro F s _ hW hvalid hnt hres
  obtain ⟨values, hlook_fn⟩ := hvalid
  obtain ⟨addrw, idxw, codew, clenw, hs_addr, hs_idx, hs_code, hs_clen⟩ :=
    lookupCode_four_word_any (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_add_code_change_add hlook_fn
  exact add_code_change_body_worldStep s addrw idxw codew clenw hW
    hs_addr hs_idx hs_code hs_clen hnt hres

private theorem shapeComb4_eq_words {v : ValueHOL 64}
    (h : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
  cases v with
  | val _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | rStruct fields =>
    cases fields with
    | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    | cons v0 tail =>
      cases tail with
      | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
      | cons v1 tail =>
        cases tail with
        | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
        | cons v2 tail =>
          cases tail with
          | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
          | cons v3 tail =>
            cases tail with
            | cons _ _ => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
            | nil =>
              simp only [shapeOfHOLExact, List.map_cons, List.map_nil,
                shapeEqHOL, shapeEqHOL.shapeEqListHOL, Bool.and_eq_true, and_true] at h
              obtain ⟨w0, rfl⟩ := shapeOne_eq_word h.1
              obtain ⟨w1, rfl⟩ := shapeOne_eq_word h.2.1
              obtain ⟨w2, rfl⟩ := shapeOne_eq_word h.2.2.1
              obtain ⟨w3, rfl⟩ := shapeOne_eq_word h.2.2.2
              exact ⟨w0, w1, w2, w3, rfl⟩

private theorem lookupCode_two_word_comb4
    {codeLookup : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 p3 : MlS} {body : ProgHOL 64} {rs : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : codeLookup fname =
      some ([(p1, .one), (p2, .one), (p3, .comb [.one, .one, .one, .one])], body, rs))
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite codeLookup fname vals =
      some (body, L, rs)) :
    ∃ (w1 w2 pb0 pb1 pb2 pb3 : BitVec 64),
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.rStruct [.val (.word pb0), .val (.word pb1), .val (.word pb2), .val (.word pb3)]) := by
  have hx := lookupCodeHOLFinite_eq_some codeLookup fname vals body L rs hl
  unfold lookupCodeHOLExact at hx
  rw [hlook] at hx; dsimp only at hx
  obtain ⟨⟨_, hlen, hall⟩, heq⟩ := ite_some_eq_some hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · cases hlen
  · cases hlen
  · cases hlen
  · simp only [List.zip, List.zipWith, List.all, Bool.and_eq_true, Bool.and_true] at hall
    obtain ⟨w1, rfl⟩ := shapeOne_eq_word hall.1
    obtain ⟨w2, rfl⟩ := shapeOne_eq_word hall.2.1
    obtain ⟨pb0, pb1, pb2, pb3, rfl⟩ := shapeComb4_eq_words hall.2.2
    have hL_eq : (List.foldl
        (fun map (entry : MlS × ValueHOL 64) current =>
          if current = entry.1 then some entry.2 else map current)
        (fun _ => none)
        [(p1, .val (.word w1)), (p2, .val (.word w2)),
         (p3, .rStruct [.val (.word pb0), .val (.word pb1), .val (.word pb2), .val (.word pb3)])]) = L.lookup :=
      (Prod.mk.inj (Prod.mk.inj heq).2).1
    dsimp only [List.foldl] at hL_eq
    refine ⟨w1, w2, pb0, pb1, pb2, pb3, ?_, ?_, ?_⟩
    · have := congrFun hL_eq p1
      rw [← this, if_neg hne13, if_neg hne12, if_pos rfl]
    · have := congrFun hL_eq p2
      rw [← this, if_neg hne23, if_pos rfl]
    · have := congrFun hL_eq p3
      rw [← this, if_pos rfl]
  · cases hlen

private def addBalanceTailProg : ProgHOL 64 :=
  .seq
    (.store (.op .add [.var .local (ofString "e"), .const 8#64]) (.var .local (ofString "post_balance")))
    (.return (.const 0#64))

private theorem add_balance_change_tail_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (lw ew pb0 pb1 pb2 pb3 : BitVec 64)
    (hW : WorldOK s)
    (hlw_nz : lw ≠ 0)
    (horig : ∀ S Nd, WorldTypedWith s S Nd → LstOK s lw.toNat ∧ BalListOrigin s lw.toNat 40)
    (hew8 : ew.toNat % 8 = 0)
    (hew_sb : sourceBase ≤ ew.toNat)
    (hew_he : ew.toNat + 40 ≤ heapEnd)
    (hew_lo : memW s lw.toNat ≤ ew.toNat)
    (hew_hi : ew.toNat + 40 ≤ memW s lw.toNat + 40 * memW s (lw.toNat + 16))
    (hs_e : s.locals.lookup (ofString "e") = some (.val (.word ew)))
    (hs_pb : s.locals.lookup (ofString "post_balance") =
      some (.rStruct [.val (.word pb0), .val (.word pb1), .val (.word pb2), .val (.word pb3)])) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s addBalanceTailProg).1
      (evaluateHOLFiniteState s addBalanceTailProg).2 := by
  have hhe : heapEnd ≤ 2 ^ 64 := by decide
  have he8_toNat : (ew + 8#64).toNat = ew.toNat + 8 := by
    rw [BitVec.toNat_add]
    change (ew.toNat + 8) % 2 ^ 64 = ew.toNat + 8
    exact Nat.mod_eq_of_lt (by omega)
  have he16_toNat : (ew + 8#64 + 8#64).toNat = ew.toNat + 16 := by
    rw [BitVec.toNat_add, he8_toNat]
    change (ew.toNat + 8 + 8) % 2 ^ 64 = ew.toNat + 16
    exact Nat.mod_eq_of_lt (by omega)
  have he24_toNat : (ew + 8#64 + 8#64 + 8#64).toNat = ew.toNat + 24 := by
    rw [BitVec.toNat_add, he16_toNat]
    change (ew.toNat + 16 + 8) % 2 ^ 64 = ew.toNat + 24
    exact Nat.mod_eq_of_lt (by omega)
  have he32_toNat : (ew + 8#64 + 8#64 + 8#64 + 8#64).toNat = ew.toNat + 32 := by
    rw [BitVec.toNat_add, he24_toNat]
    change (ew.toNat + 24 + 8) % 2 ^ 64 = ew.toNat + 32
    exact Nat.mod_eq_of_lt (by omega)
  have hbw : (panBytesInWord 64 : BitVec 64) = 8#64 := by decide
  have hdom8 : s.memaddrs (ew + 8#64) := by
    rw [hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he8_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hdom16 : s.memaddrs (ew + 8#64 + panBytesInWord 64) := by
    rw [hbw, hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he16_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hdom24 : s.memaddrs (ew + 8#64 + panBytesInWord 64 + panBytesInWord 64) := by
    rw [hbw, hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he24_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hdom32 : s.memaddrs (ew + 8#64 + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64) := by
    rw [hbw, hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he32_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hz8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
  have hev_dst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "e"), .const 8#64]) = some (.val (.word (ew + 8#64))) := by
    simp [evalHOLExact, evalListHOLExact, hs_e, valueIsWord, valueWord, wordOpHOL, wordOp, hz8]
  have hev_val : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "post_balance")) =
      some (.rStruct [.val (.word pb0), .val (.word pb1), .val (.word pb2), .val (.word pb3)]) := by
    simp [evalHOLExact, hs_pb]
  let m0 := s.memory
  let m1 := fun a => if a = ew + 8#64 then HolWordLab.word pb0 else m0 a
  let m2 := fun a => if a = ew + 8#64 + panBytesInWord 64 then HolWordLab.word pb1 else m1 a
  let m3 := fun a => if a = ew + 8#64 + panBytesInWord 64 + panBytesInWord 64 then HolWordLab.word pb2 else m2 a
  let m4 := fun a => if a = ew + 8#64 + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64 then HolWordLab.word pb3 else m3 a
  let st1 : PanSemStateFiniteExact 64 F := { s with memory := m4 }
  have hst1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "e"), .const 8#64]) (.var .local (ofString "post_balance"))) =
      (none, st1) := by
    rw [evaluateHOLFiniteState_store, hev_dst, hev_val]
    simp only [flattenHOL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.singleton_append,
      panMemStoresHOL, panMemStoreHOL, hdom8, hdom16, hdom24, hdom32, ↓reduceIte]
    rfl
  have hret : evaluateHOLFiniteState st1 (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite st1) := by
    rw [evaluateHOLFiniteState_return]
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos (by decide)]
  have htot : evaluateHOLFiniteState s addBalanceTailProg =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite st1) := by
    dsimp only [addBalanceTailProg]
    rw [evaluateHOLFiniteState_seq_line780, hst1]; dsimp only
    exact hret
  let Rl : List Ivl := [(memW s lw.toNat, 40 * memW s (lw.toNat + 16))]
  have hbre1 : ByteRegionEffect s st1 Rl := by
    refine (bre_of_store_multi hW.1.1.memaddrs (nw := 4) (by omega) hst1
      (fun v hv => by
        rw [hev_val] at hv; injection hv with hv'; subst hv'; simp [flattenHOL])
      (fun addr hdst _ => ?_)).1
    rw [hev_dst] at hdst; injection hdst with hd; injection hd with hd'; injection hd' with hd''; subst hd''
    refine ⟨by rw [he8_toNat]; omega, (memW s lw.toNat, 40 * memW s (lw.toNat + 16)),
      List.mem_singleton.2 rfl, by rw [he8_toNat]; omega, by dsimp only; rw [he8_toNat]; omega⟩
  have hbre_emp : ByteRegionEffect s (emptyLocalsHOLFinite st1) Rl :=
    hbre1.with_locals_clock (emptyLocalsHOLFinite st1).locals st1.clock
  have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [htot]; dsimp only
  exact (bal_list_store_arr_worldStep
    (r := some (.returned (.val (.word 0#64))))
    hW hlw_nz_nat (Or.inr (Or.inr rfl)) horig hbre_emp).1

private theorem add_balance_change_body_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (addrw idxw pb0 pb1 pb2 pb3 : BitVec 64)
    (hW : WorldOK s)
    (hs_addr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)))
    (hs_idx : s.locals.lookup (ofString "idx") = some (.val (.word idxw)))
    (hs_pb : s.locals.lookup (ofString "post_balance") =
      some (.rStruct [.val (.word pb0), .val (.word pb1), .val (.word pb2), .val (.word pb3)]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_balance_change)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_balance_change)).1) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_balance_change)).1
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_balance_change)).2 := by
  have hAR0 : ArenaReady s := hW.1
  set cont1 : ProgHOL 64 :=
    .decCall (ofString "e") .one (ofString "lst_upsert_idx")
      [.load .one (.op .add [.var .local (ofString "ad"), .const 16#64]),
       .const 40#64, .var .local (ofString "idx")]
      addBalanceTailProg
  have hbody_eq : sourceFnBody Guest.Software.guestFn_add_balance_change =
      .decCall (ofString "ad") .one (ofString "bal_ensure_account")
        [.var .local (ofString "addr")] cont1 := rfl
  rw [hbody_eq] at hnt hres ⊢
  obtain ⟨adw, mid1, _, _, _, _, hws1, hW1, had_rec1, hslot1,
      _, hmid1_other, hnt1, hres1, heq1_r, heq1_s⟩ :=
    decCall_bal_ensure_account_resumes s (ofString "ad")
      (.var .local (ofString "addr")) addrw cont1 hW
      (by simp [evalHOLExact, hs_addr]) hnt hres
  obtain ⟨lw, hlw_nat, hev_l⟩ := hslot1 16#64 (by decide) (by decide)
  have hmid1_idx : mid1.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
    rw [hmid1_other _ (by decide)]; exact hs_idx
  have hmid1_pb : mid1.locals.lookup (ofString "post_balance") =
      some (.rStruct [.val (.word pb0), .val (.word pb1), .val (.word pb2), .val (.word pb3)]) := by
    rw [hmid1_other _ (by decide)]; exact hs_pb
  have horig1 : lw ≠ 0 → ∀ S Nd, WorldTypedWith mid1 S Nd →
      LstOK mid1 lw.toNat ∧ BalListOrigin mid1 lw.toNat (40#64 : BitVec 64).toNat := by
    intro _ S Nd hWT1
    have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
    have h40 : (40#64 : BitVec 64).toNat = 40 := rfl
    have hlw_m16 : memW mid1 (adw.toNat + 16) = lw.toNat := by
      rw [← h16]; exact hlw_nat.symm
    have hlst1 : LstOK mid1 lw.toNat := by
      rw [← hlw_m16]
      exact (hWT1.1.2.2.2.2.2.2.2.2.2.1 adw.toNat had_rec1).2.2.1 16 (by decide)
    exact ⟨hlst1, Or.inl ⟨adw.toNat, had_rec1, Or.inl ⟨hlw_m16, h40⟩⟩⟩
  obtain ⟨ew, mid2, hlw_nz, hws2, hW2, horig2, hew8, hew_sb, hew_he, hew_lo, hew_hi,
      hmid2_e, hmid2_other, _, _, heq2_r, heq2_s⟩ :=
    decCall_lst_upsert_idx_resumes mid1 (ofString "e")
      (.load .one (.op .add [.var .local (ofString "ad"), .const 16#64]))
      (.const 40#64) (.var .local (ofString "idx"))
      lw 40#64 idxw addBalanceTailProg hW1
      hev_l rfl (by simp [evalHOLExact, hmid1_idx])
      (Or.inr (Or.inr rfl)) horig1 hnt1 hres1
  have hmid2_pb : mid2.locals.lookup (ofString "post_balance") =
      some (.rStruct [.val (.word pb0), .val (.word pb1), .val (.word pb2), .val (.word pb3)]) := by
    rw [hmid2_other _ (by decide)]; exact hmid1_pb
  have hws3 := add_balance_change_tail_worldStep mid2 lw ew pb0 pb1 pb2 pb3 hW2 hlw_nz horig2
    hew8 hew_sb hew_he hew_lo hew_hi hmid2_e hmid2_pb
  have hws12 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid2 :=
    worldStep_hp_trans hAR0.2 hws1 hws2
  have hws123 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState mid2 addBalanceTailProg).1
      (evaluateHOLFiniteState mid2 addBalanceTailProg).2 :=
    worldStep_hp_trans hAR0.2 hws12 hws3
  rw [heq1_r, heq1_s]
  dsimp only [cont1]
  rw [heq2_r, heq2_s]
  let p3 := (evaluateHOLFiniteState mid2 addBalanceTailProg).2
  have hupd :
      { { p3 with
          locals := HolFiniteMapExact.resVarEq p3.locals
            (ofString "e", mid1.locals.lookup (ofString "e")) } with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq p3.locals
            (ofString "e", mid1.locals.lookup (ofString "e")))
          (ofString "ad", s.locals.lookup (ofString "ad")) } =
      { p3 with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq p3.locals
            (ofString "e", mid1.locals.lookup (ofString "e")))
          (ofString "ad", s.locals.lookup (ofString "ad"))
        clock := p3.clock } := rfl
  dsimp only [p3] at hupd
  rw [hupd]
  exact worldStep_with_locals_right _ (evaluateHOLFiniteState mid2 addBalanceTailProg).2.clock
    (fun _ _ _ => trivial) hws123

theorem «wk_add_balance_change» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "add_balance_change") := by
  refine ⟨_, _, _, lookup_add_balance_change_add, ?_⟩
  intro F s _ hW hvalid hnt hres
  obtain ⟨values, hlook_fn⟩ := hvalid
  obtain ⟨addrw, idxw, pb0, pb1, pb2, pb3, hs_addr, hs_idx, hs_pb⟩ :=
    lookupCode_two_word_comb4 (by decide) (by decide) (by decide)
      lookup_add_balance_change_add hlook_fn
  exact add_balance_change_body_worldStep s addrw idxw pb0 pb1 pb2 pb3 hW
    hs_addr hs_idx hs_pb hnt hres

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal
