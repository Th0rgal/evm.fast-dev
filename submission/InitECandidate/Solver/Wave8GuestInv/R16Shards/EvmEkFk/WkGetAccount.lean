import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkGetCode
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRootTop

/-!
# R16 Shard `WkGetAccount`: `wk_get_account`, `wk_ext_code_of`, `wk_account_deployable`

Standalone 0-`sorry` proofs of C08 `WorldKeeps` contracts:
- `«wk_get_account»`
- `«wk_ext_code_of»`
- `«wk_account_deployable»`
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! ## 1. Runtime Code Lookups -/

theorem lookup_acct_new :
    originalRuntimeCode.lookup (ofString "acct_new") =
      some ([(ofString "nonce", .one), (ofString "balance", .comb [.one, .one, .one, .one]),
             (ofString "code_hash", .one)],
        sourceFnBody Guest.Software.guestFn_acct_new, .one) :=
  lookup_of_guestAst_getElem 361 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_acct_new) rfl

theorem lookup_acct_empty :
    originalRuntimeCode.lookup (ofString "acct_empty") =
      some ((sourceFunctionEntry Guest.Software.guestFn_acct_empty).2) :=
  lookup_of_guestAst_getElem 362 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_acct_empty) rfl

theorem lookup_ws_account_has_storage :
    originalRuntimeCode.lookup (ofString "ws_account_has_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_ws_account_has_storage).2) :=
  lookup_of_guestAst_getElem 371 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_account_has_storage) rfl

theorem lookup_get_pre_state_account_optional :
    originalRuntimeCode.lookup (ofString "get_pre_state_account_optional") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_pre_state_account_optional).2) :=
  lookup_of_guestAst_getElem 372 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_pre_state_account_optional) rfl

theorem lookup_get_account_optional :
    originalRuntimeCode.lookup (ofString "get_account_optional") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_account_optional).2) :=
  lookup_of_guestAst_getElem 374 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_account_optional) rfl

theorem lookup_get_account :
    originalRuntimeCode.lookup (ofString "get_account") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_account).2) :=
  lookup_of_guestAst_getElem 375 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_account) rfl

theorem lookup_account_has_storage :
    originalRuntimeCode.lookup (ofString "account_has_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_account_has_storage).2) :=
  lookup_of_guestAst_getElem 382 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_account_has_storage) rfl

theorem lookup_account_deployable :
    originalRuntimeCode.lookup (ofString "account_deployable") =
      some ((sourceFunctionEntry Guest.Software.guestFn_account_deployable).2) :=
  lookup_of_guestAst_getElem 383 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_account_deployable) rfl

theorem lookup_ext_code_of :
    originalRuntimeCode.lookup (ofString "ext_code_of") =
      some ((sourceFunctionEntry Guest.Software.guestFn_ext_code_of).2) :=
  lookup_of_guestAst_getElem 543 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ext_code_of) rfl

/-! ## 2. Multi-Word Store Helper for `WorldEff` (`acct_new`'s 4-word `balance` store) -/

private theorem panMemStores_eff_local
    (dom : BitVec 64 → Prop) [DecidablePred dom] (be : Bool)
    (hdom_ord : dom = ordinaryDomain) :
    ∀ (ws : List (HolWordLab 64)) (addr : BitVec 64)
      (mem mem' : BitVec 64 → HolWordLab 64),
      addr.toNat + 8 * ws.length < 2 ^ 64 →
      panMemStoresHOL addr ws dom mem = some mem' →
      (∀ x : BitVec 64, mem' x ≠ mem x →
        dom x ∧ addr.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ addr.toNat + 8 * ws.length) ∧
      (∀ b : Nat, b < 2 ^ 64 →
        (R10Shards.P26_P28.memByteAt mem' be (BitVec.ofNat 64 b)).toNat ≠
          (R10Shards.P26_P28.memByteAt mem be (BitVec.ofNat 64 b)).toNat →
        addr.toNat ≤ b ∧ b < addr.toNat + 8 * ws.length)
  | [], _, mem, mem', _, hst => by
    simp [panMemStoresHOL] at hst; subst hst
    exact ⟨fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩
  | w :: rest, addr, mem, mem', hlt, hst => by
    simp only [panMemStoresHOL, panMemStoreHOL] at hst
    by_cases hd : dom addr
    · simp only [hd, ↓reduceIte] at hst
      have hbw : (panBytesInWord 64 : BitVec 64).toNat = 8 := rfl
      have hnext_add : (addr + panBytesInWord 64).toNat = addr.toNat + 8 := by
        apply BitVec.toNat_add_of_lt
        rw [hbw]; simp [List.length_cons] at hlt; omega
      have hlt_rest : (addr + panBytesInWord 64).toNat + 8 * rest.length < 2 ^ 64 := by
        rw [hnext_add]; simp [List.length_cons] at hlt; omega
      let mid := fun current => if current = addr then w else mem current
      obtain ⟨ih_c, ih_b⟩ := panMemStores_eff_local dom be hdom_ord rest
        (addr + panBytesInWord 64) mid mem' hlt_rest hst
      refine ⟨?_, ?_⟩
      · intro x hne
        by_cases hxm : mem' x = mid x
        · rw [hxm] at hne
          by_cases hxa : x = addr
          · subst hxa; simp only [List.length_cons]; exact ⟨hd, le_rfl, by omega⟩
          · simp [mid, hxa] at hne
        · obtain ⟨hdx, hx1, hx2⟩ := ih_c x hxm
          rw [hnext_add] at hx1 hx2
          simp only [List.length_cons]; exact ⟨hdx, by omega, by omega⟩
      · intro b hb64 hne
        by_cases hbm : (R10Shards.P26_P28.memByteAt mem' be (BitVec.ofNat 64 b)).toNat =
            (R10Shards.P26_P28.memByteAt mid be (BitVec.ofNat 64 b)).toNat
        · rw [hbm] at hne
          by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = addr
          · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
            rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64] at hc_nat
            simp only [List.length_cons]; omega
          · unfold R10Shards.P26_P28.memByteAt R10Shards.P26_P28.memWordAt at hne
            simp [mid, hal] at hne
        · obtain ⟨hb1, hb2⟩ := ih_b b hb64 hbm
          rw [hnext_add] at hb1 hb2
          simp only [List.length_cons]; omega
    · simp [hd] at hst

theorem worldEff_store_multi {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    (dstExp valExp : ExpHOL 64) (k : Nat) (hk : 0 < k)
    (hval_len : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some v → (flattenHOL v).length = k)
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word x)) →
      x.toNat + 8 * k ≤ heapEnd ∧
      ((∃ j ∈ Rl, j.1 ≤ x.toNat ∧ x.toNat + 8 * k ≤ j.1 + j.2) ∨
       (∃ gs ∈ B, (bufferRegion s gs).1 ≤ x.toNat ∧ x.toNat + 8 * k ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
       (globN s "frame_mem_ptr" ≤ x.toNat ∧ x.toNat + 8 * k ≤ globN s "scratch_ptr") ∨
       (globN s "heap_ptr" ≤ x.toNat ∧ x.toNat + 8 * k ≤ heapLimit))) :
    WorldEff s (evaluateHOLFiniteState cur (.store dstExp valExp)).2 Rl B gw := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  rw [evaluateHOLFiniteState_store]
  rcases hx : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp with _ | dv
  · exact h
  · rcases dv with ⟨⟨x⟩⟩ | _ | _ <;> try exact h
    rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | val
    · exact h
    · have hlen := hval_len val hv
      obtain ⟨hx_he, hx_in⟩ := hin x hx
      dsimp only
      split
      · rename_i mem' hmem
        have hlt : x.toNat + 8 * (flattenHOL val).length < 2 ^ 64 := by omega
        obtain ⟨hc, hb⟩ := @panMemStores_eff_local cur.memaddrs
          (fun a => Classical.propDecidable (cur.memaddrs a)) cur.be h.arena.1.memaddrs
          (flattenHOL val) x cur.memory mem' hlt hmem
        have hbeff : Fast_C08WkShard03.ByteEff cur
            { cur with memory := mem' } [(x.toNat, 8 * k)] := by
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            fun a hne => (hc a hne).1,
            fun a hne => ?_,
            fun b hb64 hne => ?_⟩
          · obtain ⟨_, h1, h2⟩ := hc a hne
            exact ⟨(x.toNat, 8 * k), List.mem_singleton.2 rfl, by omega, by omega, by omega⟩
          · rw [R10Shards.P26_P28.memB_eq_memByteAt, R10Shards.P26_P28.memB_eq_memByteAt] at hne
            obtain ⟨h1, h2⟩ := hb b hb64 hne
            exact ⟨(x.toNat, 8 * k), List.mem_singleton.2 rfl, by omega, by omega⟩
        exact h.of_byteEff hbeff (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          exact hx_in)
      · exact h

/-! ## 3. `acct_new` & `acct_empty` via `WorldEff` → `WorldKeepsSc` -/

private theorem flattenHOL_shape_u256 {v : ValueHOL 64}
    (hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    (flattenHOL v).length = 4 := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨d⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    simp [flattenHOL]
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh

private theorem acct_new_params {vals : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_new") vals =
      some (body, callee, rs)) :
    ∃ (wn wc : BitVec 64) (vb : ValueHOL 64),
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vb) = true ∧
      callee.lookup (ofString "nonce") = some (.val (.word wn)) ∧
      callee.lookup (ofString "balance") = some vb ∧
      callee.lookup (ofString "code_hash") = some (.val (.word wc)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "acct_new")
    vals body callee rs hl
  simp only [lookupCodeHOLExact, lookup_acct_new] at hx
  rcases vals with _ | ⟨vn, _ | ⟨vb, _ | ⟨vc, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases vn with ⟨⟨wn⟩⟩ | _ | _ <;> rcases vc with ⟨⟨wc⟩⟩ | _ | _ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL] at hx)
    simp [shapeOfHOLExact, shapeEqHOL,
      show ofString "nonce" ≠ ofString "balance" by decide,
      show ofString "nonce" ≠ ofString "code_hash" by decide,
      show ofString "balance" ≠ ofString "code_hash" by decide] at hx
    obtain ⟨hsh_b, _, hL, _⟩ := hx
    refine ⟨wn, wc, vb, hsh_b, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [show ofString "nonce" ≠ ofString "balance" by decide,
        show ofString "nonce" ≠ ofString "code_hash" by decide,
        show ofString "balance" ≠ ofString "nonce" by decide,
        show ofString "balance" ≠ ofString "code_hash" by decide,
        show ofString "code_hash" ≠ ofString "nonce" by decide,
        show ofString "code_hash" ≠ ofString "balance" by decide])
  · simp at hx

theorem worldEff_acct_new {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (hgw_hp : ofString "heap_ptr" ∈ gw.map ofString)
    (heff_cur : WorldEff s0 cur Rl B gw)
    {wn wc : BitVec 64} {vb : ValueHOL 64}
    (hsh_b : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vb) = true)
    (hlk_n : cur.locals.lookup (ofString "nonce") = some (.val (.word wn)))
    (hlk_b : cur.locals.lookup (ofString "balance") = some vb)
    (hlk_c : cur.locals.lookup (ofString "code_hash") = some (.val (.word wc)))
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_acct_new)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_acct_new)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_acct_new)).2 Rl B gw := by
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_acct_new,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_alloc heff_cur hgw_hp (ofString "a") (.const 56#64)
    hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun wa nw m1 hsz_ev _ hm1_loc _ heff_m1 _ _ hwa_lo hwa_end hhp_m1 _ hnt1 hcr1 => ?_)
  have hnw_eq : nw = 56#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw_eq
  have hwa_hi : wa.toNat + 56 ≤ heapLimit := by
    change wa.toNat + (56 + 7) / 8 * 8 = globN m1 "heap_ptr" at hwa_end
    omega
  have hm1_a : m1.locals.lookup (ofString "a") = some (.val (.word wa)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm1_n : m1.locals.lookup (ofString "nonce") = some (.val (.word wn)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlk_n,
      show ofString "a" ≠ ofString "nonce" by decide]
  have hm1_b : m1.locals.lookup (ofString "balance") = some vb := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlk_b,
      show ofString "a" ≠ ofString "balance" by decide]
  have hm1_c : m1.locals.lookup (ofString "code_hash") = some (.val (.word wc)) := by
    rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlk_c,
      show ofString "a" ≠ ofString "code_hash" by decide]
  -- Store 1: `*(a + 0) := nonce`
  refine worldEff_seq hnt1 hcr1
    (fun _ _ => worldEff_store_word heff_m1 _ _
      (fun v hv => by simp [evalHOLExact, toExact, hm1_n] at hv; exact ⟨wn, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, toExact, hm1_a, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hx
        subst hx
        have hx0 : (wa + 0#64).toNat = wa.toNat := by simp
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (fun m2 hm2 heff_m2 hnt2 hcr2 => ?_)
  have hm2_loc : m2.locals = m1.locals := by
    have hk := fun k => evaluate_avoidsLocal_flowing k
      (.store (.op .add [.var .local (ofString "a"), .const 0#64]) (.var .local (ofString "nonce")))
      rfl m1 (by rw [hm2]; exact Or.inl rfl)
    apply HolFiniteMapExact.ext; funext k; simpa [hm2] using hk k
  -- Store 2: `*(a + 8) := balance` (4 words)
  refine worldEff_seq hnt2 hcr2
    (fun _ _ => worldEff_store_multi heff_m2 _ _ 4 (by decide)
      (fun v hv => by
        simp [evalHOLExact, toExact, hm2_loc, hm1_b] at hv
        subst hv
        exact flattenHOL_shape_u256 hsh_b)
      (fun x hx => by
        simp [evalHOLExact, evalListHOLExact, toExact, hm2_loc, hm1_a, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hx
        subst hx
        have hx8 : (wa + 8#64).toNat = wa.toNat + 8 := by
          apply BitVec.toNat_add_of_lt; change wa.toNat + 8 < 2 ^ 64; omega
        exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩))
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m1.locals := by
    have hk := fun k => evaluate_avoidsLocal_flowing k
      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "balance")))
      rfl m2 (by rw [hm3]; exact Or.inl rfl)
    apply HolFiniteMapExact.ext; funext k; rw [← hm2_loc]; simpa [hm3] using hk k
  -- Store 3: `*(a + 40) := empty_trie_root`
  refine worldEff_seq hnt3 hcr3
    (fun _ _ => worldEff_store_word heff_m3 _ _
      (fun v hv => by
        simp only [evalHOLExact, toExact] at hv
        obtain ⟨wetr, hwetr⟩ := heff_m3.arena.2.2.2.2.2.2.2.2.2 "empty_trie_root" (by decide)
        unfold GlobalWord at hwetr
        rw [hwetr] at hv; injection hv with hv'; exact ⟨wetr, hv'.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, toExact, hm3_loc, hm1_a, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hx
        subst hx
        have hx40 : (wa + 40#64).toNat = wa.toNat + 40 := by
          apply BitVec.toNat_add_of_lt; change wa.toNat + 40 < 2 ^ 64; omega
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m1.locals := by
    have hk := fun k => evaluate_avoidsLocal_flowing k
      (.store (.op .add [.var .local (ofString "a"), .const 40#64]) (.var .global (ofString "empty_trie_root")))
      rfl m3 (by rw [hm4]; exact Or.inl rfl)
    apply HolFiniteMapExact.ext; funext k; rw [← hm3_loc]; simpa [hm4] using hk k
  -- Store 4: `*(a + 48) := code_hash` ; `return a`
  refine worldEff_seq hnt4 hcr4
    (fun _ _ => worldEff_store_word heff_m4 _ _
      (fun v hv => by simp [evalHOLExact, toExact, hm4_loc, hm1_c] at hv; exact ⟨wc, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, toExact, hm4_loc, hm1_a, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hx
        subst hx
        have hx48 : (wa + 48#64).toNat = wa.toNat + 48 := by
          apply BitVec.toNat_add_of_lt; change wa.toNat + 48 < 2 ^ 64; omega
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (fun m5 _ heff_m5 _ _ => worldEff_return heff_m5 _)

theorem wkSc_acct_new :
    WorldKeepsSc WorldOK (bufRegions []) ["heap_ptr"] stdKeep NoExtra (ofString "acct_new") := by
  refine ⟨_, _, _, lookup_acct_new, fun s hc hWOK ⟨vals, hl⟩ hnt hres => ?_⟩
  obtain ⟨wn, wc, vb, hsh_b, hlk_n, hlk_b, hlk_c⟩ := acct_new_params hl
  have heff := worldEff_acct_new s s (Rl := []) (B := []) (gw := ["heap_ptr"])
    (by decide) (WorldEff.refl s [] [] ["heap_ptr"] hWOK.1 hc)
    hsh_b hlk_n hlk_b hlk_c hnt hres
  have hws : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_acct_new)).1
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_acct_new)).2 :=
    heff.to_worldStep_Q hWOK (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
  exact ⟨hws, heff.sp_hi⟩

theorem wkSc_acct_empty :
    WorldKeepsSc WorldOK (bufRegions []) ["heap_ptr"] stdKeep NoExtra (ofString "acct_empty") := by
  have hB : ValidBufList [] := by intro p hp; cases hp
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsSc_of_progWStep lookup_acct_empty ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_acct_empty,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; exact hg)
    wkSc_acct_new ?_
  exact progWStep_return _ _ _

/-! ## 4. Lift `ws_get_account_optional` and `ws_storage_root_of` to `WorldKeepsSc` -/

abbrev wsAcctBufs : BufList :=
  [("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)]

abbrev extCodeBufs : BufList :=
  [("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64), ("sk_buf", 52)]

theorem validBufList_wsAcctBufs : ValidBufList wsAcctBufs := by
  intro p hp
  simp only [wsAcctBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨136, by decide, by decide, by decide⟩
  · exact ⟨200, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩

theorem validBufList_extCodeBufs : ValidBufList extCodeBufs := by
  intro p hp
  simp only [extCodeBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨136, by decide, by decide, by decide⟩
  · exact ⟨200, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩

theorem safeStepGlobals_hp_sp : SafeStepGlobals ["heap_ptr", "scratch_ptr"] := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

theorem wkSc_ws_get_account_optional :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "ws_get_account_optional") := by
  refine ⟨_, _, _, lookup_ws_get_account_optional_top, fun s hc hWOK _ hnt hres => ?_⟩
  have heff := worldEff_ws_get_account_optional s s hWOK.1.2
    (WorldEff.refl s [] wsBufs wsGw hWOK.1 hc) hnt hres
  have heff' : WorldEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2
      (bufRegions wsAcctBufs s) wsBufs wsGw :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  have hws : WorldStep (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2 :=
    heff'.to_worldStep_Q hWOK (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
  exact ⟨hws, heff.sp_hi⟩

theorem wkSc_ws_storage_root_of :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "ws_storage_root_of") := by
  refine ⟨_, _, _, lookup_ws_storage_root_of_top, fun s hc hWOK _ hnt hres => ?_⟩
  have heff := worldEff_ws_storage_root_of s s hWOK.1.2
    (WorldEff.refl s [] wsBufs wsGw hWOK.1 hc) hnt hres
  have heff' : WorldEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_storage_root_of)).2
      (bufRegions wsAcctBufs s) wsBufs wsGw :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  have hws : WorldStep (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_storage_root_of)).1
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_storage_root_of)).2 :=
    heff'.to_worldStep_Q hWOK (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
  exact ⟨hws, heff.sp_hi⟩

/-! ## 5. `WorldKeepsSc` Proofs for Account & Code Callees -/

theorem wkSc_ws_account_has_storage :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "ws_account_has_storage") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_ws_account_has_storage ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_ws_account_has_storage,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkSc_ws_storage_root_of ?_
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  exact progWStep_return _ _ _

theorem wkSc_get_pre_state_account_optional :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "get_pre_state_account_optional") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_get_pre_state_account_optional ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_pre_state_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_seq hB hgw
    (progWStep_call0_htab_set_recSlot "ts" "ts+8" 8 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonValueSlot_ts8 s S hT hts ht0)) ?_
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_seq hB hgw
    (progWStep_call0 (by intro p hp; cases hp) (by intro g hg; simp at hg; subst hg; simp)
      wkSc_record_pre_state_read) ?_
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkSc_ws_get_account_optional ?_
  exact progWStep_return _ _ _

theorem wkSc_get_account_optional :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "get_account_optional") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_get_account_optional ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_seq hB hgw
    (progWStep_call0_htab_set_recSlot "ts" "ts+8" 8 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonValueSlot_ts8 s S hT hts ht0)) ?_
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkSc_get_pre_state_account_optional ?_
  exact progWStep_return _ _ _

theorem wkSc_get_account :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "get_account") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_get_account ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_account,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkSc_get_account_optional ?_
  refine progWStep_seq hB hgw
    (progWStep_ite
      (progWStep_call_local (by intro p hp; cases hp) (by intro g hg; simp at hg; subst hg; simp)
        wkSc_acct_empty)
      (progWStep_skip _ _)) ?_
  exact progWStep_return _ _ _

theorem wkSc_account_has_storage :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "account_has_storage") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_account_has_storage ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_account_has_storage,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStep_seq hB hgw
    (progWStep_ite (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) (progWStep_skip _ _)) ?_
  refine progWStep_seq hB hgw
    (progWStep_call_local (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get)) ?_
  refine progWStep_seq hB hgw
    (progWStep_ite (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) (progWStep_skip _ _)) ?_
  refine progWStep_seq hB hgw
    (progWStep_call0 (by intro p hp; cases hp) (by intro g hg; simp at hg; subst hg; simp)
      wkSc_record_pre_state_read) ?_
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkSc_ws_account_has_storage ?_
  exact progWStep_return _ _ _

theorem wkSc_account_deployable :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "account_deployable") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_account_deployable ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_account_deployable,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkSc_get_account ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkSc_account_has_storage ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  exact progWStep_return _ _ _

theorem wkSc_ext_code_of :
    WorldKeepsSc WorldOK (bufRegions extCodeBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "ext_code_of") := by
  have hB := validBufList_extCodeBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_ext_code_of ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_ext_code_of,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs, extCodeBufs] at hp ⊢; exact hp.imp_right (fun h => h.imp_right Or.inl))
    (fun _ h => h)
    wkSc_get_account ?_
  refine progWStep_decCall hB hgw
    (by intro p hp; simp at hp; subst hp; simp [extCodeBufs])
    (by intro g hg; simp at hg; subst hg; simp)
    wkSc_get_code ?_
  exact progWStep_return _ _ _

/-! ## 6. Frozen C08 Contract Theorems -/

theorem «wk_get_account» :
    WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "get_account") :=
  wkSc_get_account.to_worldKeeps

theorem «wk_account_deployable» :
    WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "account_deployable") :=
  wkSc_account_deployable.to_worldKeeps

theorem «wk_ext_code_of» :
    WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ext_code_of") :=
  wkSc_ext_code_of.to_worldKeeps

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
