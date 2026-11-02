import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetNewNode

/-! Semantic specs for `htab_new_leaf` and `htab_new_internal`. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem Ret.dec_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (h : ∀ val, evalAt s init = some val → Ret (setVarHOLFinite x val s) body Φ) :
    Ret s (.dec x sh init body) Φ :=
  Ret.dec fun val hval v hv => hLF v _ _ (h val hval v hv)

theorem ev_order_addr {F : Type} (st : PanSemStateFiniteExact 64 F) (tw posw ow : BitVec 64)
    (ht : st.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hp : st.locals.lookup (ofString "pos") = some (.val (.word posw)))
    (hdom : st.memaddrs (tw + 48#64))
    (hm : st.memory (tw + 48#64) = .word ow) :
    evalAt st (.op .add [.load .one (.op .add [.var .local (ofString "t"), .const 48#64]),
      .panop .mul [.var .local (ofString "pos"), .const 8#64]]) =
      some (.val (.word (ow + (posw * 8#64 + (0 : BitVec 64))))) := by
  simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht, hp,
    isWfShapeExactHOL, memLoadHOLExact, hdom, hm, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]

theorem frameOutside_updW_mem {F : Type} (s s' : PanSemStateFiniteExact 64 F)
    (m1 : BitVec 64 → HolWordLab 64)
    (hm1 : s'.memory = m1)
    (a w : BitVec 64) (keep : List Ivl) (fresh : Ivl)
    (hprev : FrameOutside s s' keep fresh)
    (ha : (∃ i ∈ keep, CellHits a.toNat i) ∨ CellHits a.toNat fresh)
    (s'' : PanSemStateFiniteExact 64 F) (hm2 : s''.memory = updW m1 a w) :
    FrameOutside s s'' keep fresh := by
  intro x hx hfresh
  rw [hm2]
  by_cases hxa : x = a
  · subst x; exfalso
    rcases ha with ⟨i, hi, hhit⟩ | hhit
    · exact hx i hi hhit
    · exact hfresh hhit
  · simp only [updW, hxa, ↓reduceIte, ← hm1]
    exact hprev x hx hfresh

/-! ## 1. `htab_new_leaf` Postcondition -/

def NewLeafPost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) (valw : BitVec 64)
    (A : List Nat) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s0 "heap_ptr", globN post "heap_ptr" - globN s0 "heap_ptr")
  ∃ nl : BitVec 64, ∃ Fr1 : List Nat,
    v = .val (.word nl) ∧
    ArenaReady post ∧
    NodeState post t (A ++ [nl.toNat]) Fr1 ∧
    hdr post t 0 = hdr s0 t 0 ∧
    hdr post t 1 = hdr s0 t 1 ∧
    hdr post t 3 = hdr s0 t 3 + 1 ∧
    hdr post t 7 = hdr s0 t 7 ∧
    nodeF post (hdr post t 5) nl.toNat 0 = 0 ∧
    nodeF post (hdr post t 5) nl.toNat 8 = valw.toNat ∧
    nodeF post (hdr post t 5) nl.toNat 16 = hdr s0 t 3 ∧
    nodeF post (hdr post t 5) nl.toNat 24 = 8 * hdr s0 t 0 ∧
    memW post (hdr post t 6 + 8 * hdr s0 t 3) = nl.toNat ∧
    (∀ x ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF post (hdr post t 5) x off = nodeF s0 (hdr s0 t 5) x off) ∧
    (∀ i, i < hdr s0 t 3 →
      memW post (hdr post t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) ∧
    globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s0 post (htabFootprint s0 t) fresh ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = post.globals.lookup k)

theorem locFree_newLeafPost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat)
    (valw : BitVec 64) (A : List Nat) :
    LocFreePost (NewLeafPost s0 t valw A) := by
  intro v p L' h
  obtain ⟨nl, Fr1, hv, hA, hNS, c0, c1, c3, c7, n0, n8, n16, n24, ordc, cnd, cord, chp, cfp, cfr, cg⟩ := h
  exact ⟨nl, Fr1, hv, ⟨guestInv_congr (s := { p with locals := L' }) rfl rfl rfl rfl hA.1, hA.2⟩,
    hNS, c0, c1, c3, c7, n0, n8, n16, n24, ordc, cnd, cord, chp, cfp, cfr, cg⟩

theorem htab_new_leaf_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64) (A Fr0 : List Nat)
    (ht : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey : s0.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval : s0.locals.lookup (ofString "value") = some (.val (.word valw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hcnt_le : hdr s0 tw.toNat 3 ≤ A.length)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_new_leaf)
      (NewLeafPost s0 tw.toNat valw A) := by
  set t := tw.toNat
  have hLF := locFree_newLeafPost s0 t valw A
  set cnt := hdr s0 t 3
  set klen := hdr s0 t 0
  set stride := hdr s0 t 1
  have hA_len : A.length ≤ hdr s0 t 10 := by
    have hndA : A.Nodup := (List.nodup_append.mp hNS0.2.1).1
    have hle := nodup_len_le_range hndA (fun x hx => (hNS0.2.2.1 x).mp (List.mem_append_left _ hx))
    have := hNS0.1.2.2.2.2.2.2
    omega
  have hcnt_le_nc0 : cnt ≤ hdr s0 t 10 := le_trans hcnt_le hA_len
  htab_unfold Guest.Software.guestFn_htab_new_leaf
  -- 1. decCall n := htab_new_node(t)
  refine Ret.decCall_new_node_lf hLF tw A Fr0 (by simp [evalAt, evalHOLExact, ht]) hA0 hNS0 hal0 ?_
  intro nlw Fr1 s1 hA1 hNS1 hh0_1 hh1_1 hh3_1 hh7_1 hnc_le_1 hnd_1 hord_1 hhp_1 hfp_1 hfr_1 hg_1 hloc_1
  change NodeState s1 t (A ++ [nlw.toNat]) Fr1 at hNS1
  change hdr s1 t 0 = hdr s0 t 0 at hh0_1
  change hdr s1 t 1 = hdr s0 t 1 at hh1_1
  change hdr s1 t 3 = hdr s0 t 3 at hh3_1
  change hdr s1 t 7 = hdr s0 t 7 at hh7_1
  change hdr s0 t 10 ≤ hdr s1 t 10 at hnc_le_1
  obtain ⟨hB1, hnodup1, hmem1, hfc1⟩ := hNS1
  obtain ⟨hnc1_lt, hst1_ge8, hst1_le64, hst1_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB1
  have hnx1_le : hdr s1 t 8 ≤ hdr s1 t 10 + 1 := hB1.2.2.2.2.2.2.2
  have hnl_rng : 1 ≤ nlw.toNat ∧ nlw.toNat < hdr s1 t 8 :=
    (hmem1 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  have hnl_lt_nc1 : nlw.toNat < hdr s1 t 10 + 1 := by omega
  have hcnt_lt_nc1 : cnt < hdr s1 t 10 + 1 := by
    have hndAnl : (A ++ [nlw.toNat]).Nodup := (List.nodup_append.mp hnodup1).1
    have hle := nodup_len_le_range hndAnl (fun x hx => (hmem1 x).mp (List.mem_append_left _ hx))
    rw [List.length_append, List.length_singleton] at hle
    have : cnt ≤ A.length := hcnt_le
    omega
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom1_t0, hm1_t0⟩ := word_of_hdr s1 tw 0 (by omega) hB1
  obtain ⟨hdom1_t1, hm1_t1⟩ := word_of_hdr s1 tw 1 (by omega) hB1
  obtain ⟨hdom1_t3, hm1_t3⟩ := word_of_hdr s1 tw 3 (by omega) hB1
  obtain ⟨hdom1_t4, hm1_t4⟩ := word_of_hdr s1 tw 4 (by omega) hB1
  obtain ⟨hdom1_t5, hm1_t5⟩ := word_of_hdr s1 tw 5 (by omega) hB1
  obtain ⟨hdom1_t6, hm1_t6⟩ := word_of_hdr s1 tw 6 (by omega) hB1
  -- 2. dec klen := load(t + 0)
  apply Ret.dec_lf hLF; intro vkl hvkl
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 0#64
    (by simp [setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "n" ≠ ofString "t" by decide]) vkl hvkl
  have hm0 : (setVarHOLFinite (ofString "n") (.val (.word nlw)) s1).memory (tw + 0#64) = .word (BitVec.ofNat 64 klen) := by
    change s1.memory (tw + BitVec.ofNat 64 (8 * 0)) = .word (BitVec.ofNat 64 (hdr s0 tw.toNat 0))
    rw [← hh0_1]; exact hm1_t0
  rw [hm0]
  -- 3. dec stride := load(t + 8)
  apply Ret.dec_lf hLF; intro vst hvst
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 8#64
    (by simp [setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "klen" ≠ ofString "t" by decide, show ofString "n" ≠ ofString "t" by decide]) vst hvst
  have hm8 : (setVarHOLFinite (ofString "klen") (.val (.word (BitVec.ofNat 64 klen)))
      (setVarHOLFinite (ofString "n") (.val (.word nlw)) s1)).memory (tw + 8#64) = .word (BitVec.ofNat 64 stride) := by
    change s1.memory (tw + BitVec.ofNat 64 (8 * 1)) = .word (BitVec.ofNat 64 (hdr s0 tw.toNat 1))
    rw [← hh1_1]; exact hm1_t1
  rw [hm8]
  -- 4. call memcpy(load(t + 32) + n * stride, key, klen)
  let L1_3 : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((s1.locals.update (ofString "n", .val (.word nlw))).update
      (ofString "klen", .val (.word (BitVec.ofNat 64 klen)))).update
      (ofString "stride", .val (.word (BitVec.ofNat 64 stride)))
  let s1_3 : PanSemStateFiniteExact 64 F := { s1 with locals := L1_3 }
  change Ret s1_3 _ _
  have hkeys1_in := (hB1.1 (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) (by simp [htabFootprint])).1
  change hdr s1 t 4 ≥ sourceBase ∧ hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1 ≤ heapEnd at hkeys1_in
  have hklen_le_st : klen ≤ stride := by have := hNS0.1.2.2.2.2.1; dsimp [klen, stride]; omega
  have hklen_le60 : klen ≤ 60 := hNS0.1.2.2.2.1
  have hh1_1_t : hdr s1 t 1 = stride := hh1_1
  have hmul_le_nl : nlw.toNat * stride + stride ≤ (hdr s1 t 10 + 1) * stride := by
    have h1 : (nlw.toNat + 1) * stride ≤ (hdr s1 t 10 + 1) * stride := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    exact h1
  have hkeys1_hi : hdr s1 t 4 + (hdr s1 t 10 + 1) * stride ≤ heapEnd := by
    rw [← hh1_1_t]; exact hkeys1_in.2
  have hst_le64_0 : stride ≤ 64 := by rw [← hh1_1_t]; exact hst1_le64
  set dst_k := BitVec.ofNat 64 (hdr s1 t 4 + nlw.toNat * stride)
  have hdst_k_nat : dst_k.toNat = hdr s1 t 4 + nlw.toNat * stride := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have he_md : evalAt s1_3 (.op .add [.load .one (.op .add [.var .local (ofString "t"), .const 32#64]),
      .panop .mul [.var .local (ofString "n"), .var .local (ofString "stride")]]) =
      some (.val (.word dst_k)) := by
    have ht_l : s1_3.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s1_3, L1_3, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
        show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide,
        show ofString "n" ≠ ofString "t" by decide]
    have hn_l : s1_3.locals.lookup (ofString "n") = some (.val (.word nlw)) := by
      simp [s1_3, L1_3, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "stride" ≠ ofString "n" by decide, show ofString "klen" ≠ ofString "n" by decide]
    have hst_l : s1_3.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 stride))) := by
      simp [s1_3, L1_3, HolFiniteMapExact.lookup_update, FUPDATE]
    have h320 : 32#64 + (0 : BitVec 64) = 32#64 := rfl
    have hdom32 : s1_3.memaddrs (tw + 32#64) := hdom1_t4
    have hm32 : s1_3.memory (tw + 32#64) = .word (BitVec.ofNat 64 (hdr s1 t 4)) := hm1_t4
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
      ht_l, hn_l, hst_l, h320, hdom32, hm32, isWfShapeExactHOL, memLoadHOLExact,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hst_mod : (BitVec.ofNat 64 stride).toNat = stride := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hmul_mod : (nlw * BitVec.ofNat 64 stride).toNat = nlw.toNat * stride := by
      rw [BitVec.toNat_mul, hst_mod, Nat.mod_eq_of_lt (by omega)]
    have h4_mod : (BitVec.ofNat 64 (hdr s1 t 4)).toNat = hdr s1 t 4 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hz : nlw * BitVec.ofNat 64 stride + (0 : BitVec 64) = nlw * BitVec.ofNat 64 stride := BitVec.add_zero _
    rw [hz, BitVec.toNat_add, h4_mod, hmul_mod, hdst_k_nat, Nat.mod_eq_of_lt (by omega)]
  have he_ms : evalAt s1_3 (.var .local (ofString "key")) = some (.val (.word keyw)) := by
    simp [s1_3, L1_3, hloc_1, evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hkey,
      show ofString "stride" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide,
      show ofString "n" ≠ ofString "key" by decide]
  have he_mn : evalAt s1_3 (.var .local (ofString "klen")) = some (.val (.word (BitVec.ofNat 64 klen))) := by
    simp [s1_3, L1_3, evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "stride" ≠ ofString "klen" by decide]
  have hwklen : (BitVec.ofNat 64 klen).toNat = klen := by rw [BitVec.toNat_ofNat]; omega
  refine Ret.seq_memcpy_frame (s := s1_3) ⟨guestInv_congr (s := s1) rfl rfl rfl rfl hA1.1, hA1.2⟩
    dst_k keyw (BitVec.ofNat 64 klen)
    (by rw [hdst_k_nat, hwklen]; omega)
    (by rw [hwklen]; omega)
    he_md he_ms he_mn ?_
  intro s2 hA2 hmcf_k hloc2
  have hpair1 := hB1.2.1
  simp only [htabFootprint, List.pairwise_cons, List.mem_cons] at hpair1
  have hd1_tk : Disj (t, 88) (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) := hpair1.1 _ (Or.inl rfl)
  have hd1_kn : Disj (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) := hpair1.2.1 _ (Or.inl rfl)
  have hd1_ko : Disj (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) := hpair1.2.1 _ (Or.inr (Or.inl rfl))
  have hsub_keys : Inside (dst_k.toNat, (BitVec.ofNat 64 klen).toNat) (hdr s1 t 4) (hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1) := by
    rw [hdst_k_nat, hwklen, hh1_1_t]
    exact ⟨by omega, by omega⟩
  have hdr_s2_eq : ∀ k < 11, hdr s2 t k = hdr s1 t k := by
    intro k hk
    unfold hdr
    apply memW_eq_of_frame_disj hmcf_k.2.2.2.2.2.2 (by omega)
    have h1 := hsub_keys.1; have h2 := hsub_keys.2
    rcases hd1_tk with hz | hz | hle | hle
    · cases hz
    · rw [hh1_1_t] at hz; have : 0 < (hdr s1 t 10 + 1) * stride := Nat.mul_pos (by omega) (by omega); omega
    · exact Or.inl (by change t + 88 ≤ hdr s1 t 4 at hle; omega)
    · exact Or.inr (by change hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1 ≤ t at hle; omega)
  have hnd_s2_eq : ∀ n < hdr s1 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s2 (hdr s1 t 5) n off = nodeF s1 (hdr s1 t 5) n off := by
    intro n hn off hoff
    have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd1_in
    unfold nodeF
    apply memW_eq_of_frame_disj hmcf_k.2.2.2.2.2.2 (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
    have h1 := hsub_keys.1; have h2 := hsub_keys.2
    rcases hd1_kn with hz | hz | hle | hle
    · rw [hh1_1_t] at hz; have : 0 < (hdr s1 t 10 + 1) * stride := Nat.mul_pos (by omega) (by omega); omega
    · omega
    · exact Or.inr (by change hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1 ≤ hdr s1 t 5 at hle; rcases hoff with rfl | rfl | rfl | rfl <;> omega)
    · exact Or.inl (by change hdr s1 t 5 + (hdr s1 t 10 + 1) * 32 ≤ hdr s1 t 4 at hle; rcases hoff with rfl | rfl | rfl | rfl <;> omega)
  have hord_s2_eq : ∀ i < hdr s1 t 10 + 1,
      memW s2 (hdr s1 t 6 + 8 * i) = memW s1 (hdr s1 t 6 + 8 * i) := by
    intro i hi
    have hord1_in := (hB1.1 (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) (by simp [htabFootprint])).1
    unfold Inside at hord1_in
    apply memW_eq_of_frame_disj hmcf_k.2.2.2.2.2.2 (by omega)
    have h1 := hsub_keys.1; have h2 := hsub_keys.2
    rcases hd1_ko with hz | hz | hle | hle
    · rw [hh1_1_t] at hz; have : 0 < (hdr s1 t 10 + 1) * stride := Nat.mul_pos (by omega) (by omega); omega
    · omega
    · exact Or.inr (by change hdr s1 t 4 + (hdr s1 t 10 + 1) * hdr s1 t 1 ≤ hdr s1 t 6 at hle; omega)
    · exact Or.inl (by change hdr s1 t 6 + (hdr s1 t 10 + 1) * 8 ≤ hdr s1 t 4 at hle; omega)
  have hfp_s2 : htabFootprint s2 t = htabFootprint s1 t := by
    simp [htabFootprint, hdr_s2_eq 1 (by omega), hdr_s2_eq 4 (by omega), hdr_s2_eq 5 (by omega), hdr_s2_eq 6 (by omega), hdr_s2_eq 10 (by omega)]
  have hB2 : HtabBlocks s2 t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv
      rw [hfp_s2] at hiv
      obtain ⟨hin, hwok⟩ := hB1.1 iv hiv
      exact ⟨hin, wordsOK_block s2 hA2.1.memaddrs iv.1 iv.2 hwok.1 hwok.2.1 hin.1 hin.2⟩
    · rw [hfp_s2]; exact hB1.2.1
    · rw [hdr_s2_eq 0 (by omega)]; exact hB1.2.2.1
    · rw [hdr_s2_eq 0 (by omega)]; exact hB1.2.2.2.1
    · rw [hdr_s2_eq 1 (by omega), hdr_s2_eq 0 (by omega)]; exact hB1.2.2.2.2.1
    · rw [hdr_s2_eq 10 (by omega)]; exact hB1.2.2.2.2.2.1
    · rw [hdr_s2_eq 8 (by omega)]; exact hB1.2.2.2.2.2.2.1
    · rw [hdr_s2_eq 8 (by omega), hdr_s2_eq 10 (by omega)]; exact hB1.2.2.2.2.2.2.2
  have hfr_s0_s2 : FrameOutside s0 s2 (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    intro x hxk hxf
    have hm2_1 : s2.memory x = s1_3.memory x := by
      apply hmcf_k.2.2.2.2.2.2 x
      · intro i hi hhit
        rw [List.mem_singleton.mp hi] at hhit
        have hhit_keys : CellHits x.toNat (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) :=
          cellHits_of_inside hhit hsub_keys
        rcases (hfp_1 (hdr s1 t 4, (hdr s1 t 10 + 1) * hdr s1 t 1) (by dsimp [t]; simp [htabFootprint])).2 with ⟨j, hj, hij⟩ | hfresh
        · exact hxk j hj (cellHits_of_inside hhit_keys hij)
        · exact hxf (cellHits_of_inside hhit_keys hfresh)
      · intro ⟨_, c2⟩; omega
    rw [hm2_1]
    exact hfr_1 x (fun i hi => by rw [List.mem_singleton.mp hi]; exact hxk (t, 88) (by simp [htabFootprint])) hxf
  -- 5. Now enter `NS` on `s2` for the rest of `htab_new_leaf`!
  obtain ⟨hdom2_t5, hm2_t5⟩ := word_of_hdr s2 tw 5 (by omega) hB2
  obtain ⟨hdom2_t3, hm2_t3⟩ := word_of_hdr s2 tw 3 (by omega) hB2
  obtain ⟨hdom2_t6, hm2_t6⟩ := word_of_hdr s2 tw 6 (by omega) hB2
  apply Ret.of_NS
  apply Ret.ns_dec_lf hLF; intro vnd hvnd
  obtain ⟨_, hvnd_eq⟩ := ev_field_load (NS s2 s2.locals s2.globals s2.memory s2.clock) (ofString "t") tw 40#64
    (by simp only [NS_locals, hloc2]; simp [s1_3, L1_3, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide,
      show ofString "n" ≠ ofString "t" by decide]) vnd hvnd
  have hm40_2 : s2.memory (tw + 40#64) = .word (BitVec.ofNat 64 (hdr s1 t 5)) := by
    rw [← hdr_s2_eq 5 (by omega)]; exact hm2_t5
  have hvnd_eq' : vnd = .val (.word (BitVec.ofNat 64 (hdr s1 t 5))) := by
    rw [NS_memory, hm40_2] at hvnd_eq; exact hvnd_eq
  subst hvnd_eq'
  set ndw := BitVec.ofNat 64 (hdr s1 t 5)
  have hndw_nat : ndw.toNat = hdr s1 t 5 := by
    have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd1_in; rw [BitVec.toNat_ofNat]; omega
  have eval_nd_nl : ∀ (st : PanSemStateFiniteExact 64 F) (off : Nat),
      st.locals.lookup (ofString "nodes") = some (.val (.word ndw)) →
      st.locals.lookup (ofString "n") = some (.val (.word nlw)) →
      evalAt st (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "n"), .const 32#64], .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (ndw + nlw * 32#64 + BitVec.ofNat 64 off))) := by
    intro st off hnd_l hn_l
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnd_l, hn_l,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
    rw [hz, BitVec.add_assoc]
  let L_s2n := s2.locals.update (ofString "nodes", .val (.word ndw))
  have hloc_s2n_nd : L_s2n.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_s2n, HolFiniteMapExact.lookup_update, FUPDATE]
  have hloc_s2n_n : L_s2n.lookup (ofString "n") = some (.val (.word nlw)) := by
    simp [L_s2n, hloc2, s1_3, L1_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nodes" ≠ ofString "n" by decide,
      show ofString "stride" ≠ ofString "n" by decide, show ofString "klen" ≠ ofString "n" by decide]
  have hloc_s2n_val : L_s2n.lookup (ofString "value") = some (.val (.word valw)) := by
    simp [L_s2n, hloc2, s1_3, L1_3, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, hval,
      show ofString "nodes" ≠ ofString "value" by decide,
      show ofString "stride" ≠ ofString "value" by decide, show ofString "klen" ≠ ofString "value" by decide,
      show ofString "n" ≠ ofString "value" by decide]
  have hloc_s2n_t : L_s2n.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_s2n, hloc2, s1_3, L1_3, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "nodes" ≠ ofString "t" by decide,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide,
      show ofString "n" ≠ ofString "t" by decide]
  have hloc_s2n_kl : L_s2n.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 klen))) := by
    simp [L_s2n, hloc2, s1_3, L1_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nodes" ≠ ofString "klen" by decide,
      show ofString "stride" ≠ ofString "klen" by decide]
  -- 6. store(nodes + n * 32 + 0, 0)
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 0#64) 0#64
    (eval_nd_nl _ 0 hloc_s2n_nd hloc_s2n_n) rfl ?_
  intro _
  -- 7. store(nodes + n * 32 + 8, value)
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 8#64) valw
    (eval_nd_nl _ 8 hloc_s2n_nd hloc_s2n_n)
    (by simp [evalAt, evalHOLExact]; exact hloc_s2n_val) ?_
  intro _
  -- 8. dec pos := load(t + 24)
  apply Ret.ns_dec_lf hLF; intro vpos hvpos
  obtain ⟨_, hvpos_eq⟩ := ev_field_load (NS s2 L_s2n s2.globals (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) (ndw + nlw * 32#64 + 8#64) valw) s2.clock)
    (ofString "t") tw 24#64 hloc_s2n_t vpos hvpos
  have hsep1 := htabBlocks_cell_sep hB1
  have haddr_nl : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      ndw + nlw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off) := by
    intro off _; rw [← hndw_nat]; exact (ofNat_node_addr ndw nlw off).symm
  have hm24_cur : (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) (ndw + nlw * 32#64 + 8#64) valw) (tw + 24#64) =
      .word (BitVec.ofNat 64 cnt) := by
    have htw24 : tw + 24#64 = BitVec.ofNat 64 (t + 8 * 3) := (ofNat_add_toNat tw 24).symm
    have hne8 : tw + 24#64 ≠ ndw + nlw * 32#64 + 8#64 := by
      rw [htw24, haddr_nl 8 (Or.inr (Or.inl rfl))]; exact hsep1.1 3 (by omega) nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl))
    have hne0 : tw + 24#64 ≠ ndw + nlw * 32#64 + 0#64 := by
      rw [htw24, haddr_nl 0 (Or.inl rfl)]; exact hsep1.1 3 (by omega) nlw.toNat hnl_lt_nc1 0 (Or.inl rfl)
    simp only [updW, hne8, hne0, ↓reduceIte]
    have hm24_s2 : s2.memory (tw + 24#64) = .word (BitVec.ofNat 64 (hdr s2 t 3)) := hm2_t3
    rw [hm24_s2, hdr_s2_eq 3 (by omega), hh3_1]
  have hvpos_eq' : vpos = .val (.word (BitVec.ofNat 64 cnt)) := by
    rw [NS_memory, hm24_cur] at hvpos_eq; exact hvpos_eq
  subst hvpos_eq'
  set posw := BitVec.ofNat 64 cnt
  have hposw_nat : posw.toNat = cnt := by rw [BitVec.toNat_ofNat]; omega
  let L_pos := L_s2n.update (ofString "pos", .val (.word posw))
  have hl_pos_nd : L_pos.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "nodes" by decide, hloc_s2n_nd]
  have hl_pos_n : L_pos.lookup (ofString "n") = some (.val (.word nlw)) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "n" by decide, hloc_s2n_n]
  have hl_pos_t : L_pos.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "t" by decide, hloc_s2n_t]
  have hl_pos_kl : L_pos.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 klen))) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "pos" ≠ ofString "klen" by decide, hloc_s2n_kl]
  have hl_pos_p : L_pos.lookup (ofString "pos") = some (.val (.word posw)) := by
    simp [L_pos, HolFiniteMapExact.lookup_update, FUPDATE]
  -- 9. store(nodes + n * 32 + 16, pos)
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 16#64) posw
    (eval_nd_nl _ 16 hl_pos_nd hl_pos_n)
    (by simp [evalAt, evalHOLExact]; exact hl_pos_p) ?_
  intro _
  -- 10. store(nodes + n * 32 + 24, klen * 8)
  have hkl8_eq : BitVec.ofNat 64 klen * 8#64 = BitVec.ofNat 64 (8 * klen) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8#64).toNat = 8 from rfl]
    omega
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 24#64) (BitVec.ofNat 64 (8 * klen))
    (eval_nd_nl _ 24 hl_pos_nd hl_pos_n)
    (by
      have hkl_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 klen))) := hl_pos_kl
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          hkl_cur, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
          panOpHOL, valueIsWord, valueWord, hkl8_eq]) ?_
  intro _
  -- 11. store(load(t + 48) + pos * 8, n)
  set ow := BitVec.ofNat 64 (hdr s1 t 6)
  have hord1_in := (hB1.1 (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) (by simp [htabFootprint])).1
  change hdr s1 t 6 ≥ sourceBase ∧ hdr s1 t 6 + (hdr s1 t 10 + 1) * 8 ≤ heapEnd at hord1_in
  have how_nat : ow.toNat = hdr s1 t 6 := by
    rw [BitVec.toNat_ofNat]; omega
  set m4 := updW (updW (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64)
              (ndw + nlw * 32#64 + 8#64) valw)
              (ndw + nlw * 32#64 + 16#64) posw)
              (ndw + nlw * 32#64 + 24#64) (BitVec.ofNat 64 (8 * klen))
  have hm48_m4 : m4 (tw + 48#64) = .word ow := by
    have htw48 : tw + 48#64 = BitVec.ofNat 64 (t + 8 * 6) := (ofNat_add_toNat tw 48).symm
    have hne : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) → tw + 48#64 ≠ ndw + nlw * 32#64 + BitVec.ofNat 64 off := by
      intro off hoff; rw [htw48, haddr_nl off hoff]; exact hsep1.1 6 (by omega) nlw.toNat hnl_lt_nc1 off hoff
    simp only [m4, updW, hne 24 (Or.inr (Or.inr (Or.inr rfl))), hne 16 (Or.inr (Or.inr (Or.inl rfl))),
      hne 8 (Or.inr (Or.inl rfl)), hne 0 (Or.inl rfl), ↓reduceIte]
    have hm48_s2 : s2.memory (tw + 48#64) = .word (BitVec.ofNat 64 (hdr s2 t 6)) := hm2_t6
    rw [hm48_s2, hdr_s2_eq 6 (by omega)]
  have hord_addr_eq : ow + (posw * 8#64 + (0 : BitVec 64)) = BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) := by
    apply BitVec.eq_of_toNat_eq
    have hz : posw * 8#64 + (0 : BitVec 64) = posw * 8#64 := BitVec.add_zero _
    have hp8 : (posw * 8#64).toNat = cnt * 8 := by
      rw [BitVec.toNat_mul, hposw_nat, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [hz, BitVec.toNat_add, how_nat, hp8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  refine Ret.ns_storeW (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)) nlw
    (by rw [← hord_addr_eq]; exact ev_order_addr _ tw posw ow hl_pos_t hl_pos_p hdom2_t6 hm48_m4)
    (by
      have hn_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "n") = some (.val (.word nlw)) := hl_pos_n
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hn_cur]) ?_
  intro _
  -- 12. store(t + 24, pos + 1)
  have hpos1_eq : posw + (1#64 + (0 : BitVec 64)) = BitVec.ofNat 64 (cnt + 1) := by
    apply BitVec.eq_of_toNat_eq
    have h10 : 1#64 + (0 : BitVec 64) = 1#64 := rfl
    have hlt_c1 : cnt + 1 < 2 ^ 64 := by omega
    rw [h10, BitVec.toNat_add, hposw_nat, show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt_c1]
  refine Ret.ns_storeW (tw + 24#64) (BitVec.ofNat 64 (cnt + 1))
    (by
      have ht_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "t") = some (.val (.word tw)) := hl_pos_t
      have h240 : 24#64 + (0 : BitVec 64) = 24#64 := rfl
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_cur,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        valueIsWord, valueWord, wordOpHOL, wordOp, h240])
    (by
      have hp_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "pos") = some (.val (.word posw)) := hl_pos_p
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          hp_cur, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
          valueIsWord, valueWord, wordOpHOL, wordOp, hpos1_eq]) ?_
  intro _
  -- 13. return n
  apply Ret.ns_ret; intro val hval
  have hval_eq : val = .val (.word nlw) := by
    have hn_cur : ((s2.locals.update (ofString "nodes", .val (.word ndw))).update (ofString "pos", .val (.word posw))).lookup (ofString "n") = some (.val (.word nlw)) := hl_pos_n
    simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hn_cur, Option.some.injEq] at hval
    exact hval.symm
  subst hval_eq
  set m6 := updW (updW m4 (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)) nlw) (tw + 24#64) (BitVec.ofNat 64 (cnt + 1))
  let s_end := NS s2 HolFiniteMapExact.empty s2.globals m6 s2.clock
  have htw24_eq : tw + 24#64 = BitVec.ofNat 64 (t + 8 * 3) := (ofNat_add_toNat tw 24).symm
  have hdr_end_other : ∀ k < 11, k ≠ 3 → hdr s_end t k = hdr s1 t k := by
    intro k hk hk3
    have hne3 : BitVec.ofNat 64 (t + 8 * k) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
    have hne_ord : BitVec.ofNat 64 (t + 8 * k) ≠ BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) :=
      hsep1.2.1 k hk cnt hcnt_lt_nc1
    have hne_nd : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        BitVec.ofNat 64 (t + 8 * k) ≠ ndw + nlw * 32#64 + BitVec.ofNat 64 off := by
      intro off hoff; rw [haddr_nl off hoff]; exact hsep1.1 k hk nlw.toNat hnl_lt_nc1 off hoff
    unfold hdr memW
    have hm : s_end.memory (BitVec.ofNat 64 (t + 8 * k)) = s2.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s_end, NS_memory, m6, m4, updW, hne3, hne_ord,
        hne_nd 24 (Or.inr (Or.inr (Or.inr rfl))), hne_nd 16 (Or.inr (Or.inr (Or.inl rfl))),
        hne_nd 8 (Or.inr (Or.inl rfl)), hne_nd 0 (Or.inl rfl), ↓reduceIte]
    rw [hm]; exact hdr_s2_eq k hk
  have hh3_end : hdr s_end t 3 = cnt + 1 := by
    unfold hdr memW
    rw [← htw24_eq]
    simp only [s_end, NS_memory, m6, updW, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  have hh5_end : hdr s_end t 5 = hdr s1 t 5 := hdr_end_other 5 (by omega) (by omega)
  have hh6_end : hdr s_end t 6 = hdr s1 t 6 := hdr_end_other 6 (by omega) (by omega)
  have hh8_end : hdr s_end t 8 = hdr s1 t 8 := hdr_end_other 8 (by omega) (by omega)
  have hh9_end : hdr s_end t 9 = hdr s1 t 9 := hdr_end_other 9 (by omega) (by omega)
  have hfp_end : htabFootprint s_end t = htabFootprint s1 t := by
    simp [htabFootprint, hdr_end_other 1 (by omega) (by omega), hdr_end_other 4 (by omega) (by omega),
      hh5_end, hh6_end, hdr_end_other 10 (by omega) (by omega)]
  have hB_end : HtabBlocks s_end t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv; rw [hfp_end] at hiv; obtain ⟨hin, hwok⟩ := hB1.1 iv hiv
      exact ⟨hin, wordsOK_block s_end hA2.1.memaddrs iv.1 iv.2 hwok.1 hwok.2.1 hin.1 hin.2⟩
    · rw [hfp_end]; exact hB1.2.1
    · rw [hdr_end_other 0 (by omega) (by omega)]; exact hB1.2.2.1
    · rw [hdr_end_other 0 (by omega) (by omega)]; exact hB1.2.2.2.1
    · rw [hdr_end_other 1 (by omega) (by omega), hdr_end_other 0 (by omega) (by omega)]; exact hB1.2.2.2.2.1
    · rw [hdr_end_other 10 (by omega) (by omega)]; exact hB1.2.2.2.2.2.1
    · rw [hh8_end]; exact hB1.2.2.2.2.2.2.1
    · rw [hh8_end, hdr_end_other 10 (by omega) (by omega)]; exact hB1.2.2.2.2.2.2.2
  have hnl_field : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      s_end.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off)) =
        m4 (BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off)) := by
    intro off hoff
    have hne3 : BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact (hsep1.1 3 (by omega) nlw.toNat hnl_lt_nc1 off hoff).symm
    have hne_ord : BitVec.ofNat 64 (hdr s1 t 5 + 32 * nlw.toNat + off) ≠ BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) :=
      (hsep1.2.2.1 nlw.toNat hnl_lt_nc1 off hoff cnt hcnt_lt_nc1).symm
    simp [s_end, m6, updW, hne3, hne_ord]
  have hnl_0 : nodeF s_end (hdr s1 t 5) nlw.toNat 0 = 0 := by
    unfold nodeF memW; rw [hnl_field 0 (Or.inl rfl)]
    have hne24 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 0 (Or.inl rfl) nlw.toNat hnl_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    have hne16 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 0 (Or.inl rfl) nlw.toNat hnl_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    have hne8 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 0 (Or.inl rfl) nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    simp only [m4, updW, haddr_nl 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_nl 16 (Or.inr (Or.inr (Or.inl rfl))),
      haddr_nl 8 (Or.inr (Or.inl rfl)), haddr_nl 0 (Or.inl rfl), hne24, hne16, hne8, ↓reduceIte]
    rfl
  have hnl_8 : nodeF s_end (hdr s1 t 5) nlw.toNat 8 = valw.toNat := by
    unfold nodeF memW; rw [hnl_field 8 (Or.inr (Or.inl rfl))]
    have hne24 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    have hne16 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    simp only [m4, updW, haddr_nl 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_nl 16 (Or.inr (Or.inr (Or.inl rfl))),
      haddr_nl 8 (Or.inr (Or.inl rfl)), hne24, hne16, ↓reduceIte]
  have hnl_16 : nodeF s_end (hdr s1 t 5) nlw.toNat 16 = cnt := by
    unfold nodeF memW; rw [hnl_field 16 (Or.inr (Or.inr (Or.inl rfl)))]
    have hne24 := hsep1.2.2.2.1 nlw.toNat hnl_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) nlw.toNat hnl_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    simp only [m4, updW, haddr_nl 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_nl 16 (Or.inr (Or.inr (Or.inl rfl))), hne24, ↓reduceIte, hposw_nat]
  have hnl_24 : nodeF s_end (hdr s1 t 5) nlw.toNat 24 = 8 * klen := by
    unfold nodeF memW; rw [hnl_field 24 (Or.inr (Or.inr (Or.inr rfl)))]
    simp only [m4, updW, haddr_nl 24 (Or.inr (Or.inr (Or.inr rfl))), ↓reduceIte, BitVec.toNat_ofNat]
    omega
  have hnd_other : ∀ x < hdr s1 t 10 + 1, x ≠ nlw.toNat → ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s_end (hdr s1 t 5) x off = nodeF s1 (hdr s1 t 5) x off := by
    intro x hx hxne off hoff
    have hne3 : BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact (hsep1.1 3 (by omega) x hx off hoff).symm
    have hne_ord : BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off) ≠ BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) :=
      (hsep1.2.2.1 x hx off hoff cnt hcnt_lt_nc1).symm
    have hne_nl : ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
        BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off) ≠ ndw + nlw * 32#64 + BitVec.ofNat 64 off2 := by
      intro off2 hoff2; rw [haddr_nl off2 hoff2]
      exact hsep1.2.2.2.1 x hx off hoff nlw.toNat hnl_lt_nc1 off2 hoff2 (Or.inl hxne)
    have hm : s_end.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off)) = s2.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off)) := by
      simp only [s_end, NS_memory, m6, m4, updW, hne3, hne_ord,
        hne_nl 24 (Or.inr (Or.inr (Or.inr rfl))), hne_nl 16 (Or.inr (Or.inr (Or.inl rfl))),
        hne_nl 8 (Or.inr (Or.inl rfl)), hne_nl 0 (Or.inl rfl), ↓reduceIte]
    have h1 : nodeF s_end (hdr s1 t 5) x off = nodeF s2 (hdr s1 t 5) x off := by unfold nodeF memW; rw [hm]
    exact h1.trans (hnd_s2_eq x hx off hoff)
  have hord_cnt : memW s_end (hdr s1 t 6 + 8 * cnt) = nlw.toNat := by
    have hne3 : BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact (hsep1.2.1 3 (by omega) cnt hcnt_lt_nc1).symm
    unfold memW; simp [s_end, m6, updW, hne3]
  have hord_lt : ∀ i < cnt, memW s_end (hdr s1 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
    intro i hi
    have hi_lt : i < hdr s1 t 10 + 1 := by omega
    have hne3 : BitVec.ofNat 64 (hdr s1 t 6 + 8 * i) ≠ tw + 24#64 := by
      rw [htw24_eq]; exact (hsep1.2.1 3 (by omega) i hi_lt).symm
    have hne_cnt : BitVec.ofNat 64 (hdr s1 t 6 + 8 * i) ≠ BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt) :=
      hsep1.2.2.2.2 i hi_lt cnt hcnt_lt_nc1 (by omega)
    have hne_nl : ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
        BitVec.ofNat 64 (hdr s1 t 6 + 8 * i) ≠ ndw + nlw * 32#64 + BitVec.ofNat 64 off2 := by
      intro off2 hoff2; rw [haddr_nl off2 hoff2]
      exact hsep1.2.2.1 nlw.toNat hnl_lt_nc1 off2 hoff2 i hi_lt
    have hm : s_end.memory (BitVec.ofNat 64 (hdr s1 t 6 + 8 * i)) = s2.memory (BitVec.ofNat 64 (hdr s1 t 6 + 8 * i)) := by
      simp only [s_end, NS_memory, m6, m4, updW, hne3, hne_cnt,
        hne_nl 24 (Or.inr (Or.inr (Or.inr rfl))), hne_nl 16 (Or.inr (Or.inr (Or.inl rfl))),
        hne_nl 8 (Or.inr (Or.inl rfl)), hne_nl 0 (Or.inl rfl), ↓reduceIte]
    have h1 : memW s_end (hdr s1 t 6 + 8 * i) = memW s2 (hdr s1 t 6 + 8 * i) := by unfold memW; rw [hm]
    exact (h1.trans (hord_s2_eq i hi_lt)).trans (hord_1 i (by change i < hdr s0 t 10 + 1; omega))
  have hNS_end : NodeState s_end t (A ++ [nlw.toNat]) Fr1 := by
    refine ⟨hB_end, hnodup1, fun x => by rw [hh8_end]; exact hmem1 x, ?_⟩
    rw [hh5_end, hh9_end]
    refine FreeChainF.congr Fr1 _ ?_ hfc1
    intro f hf
    have hf_ne : f ≠ nlw.toNat := by
      rintro rfl
      exact (List.nodup_append.mp hnodup1).2.2 nlw.toNat (List.mem_append_right _ (by simp)) nlw.toNat hf rfl
    have hf_rng := (hmem1 f).mp (List.mem_append_right _ hf)
    exact hnd_other f (by omega) hf_ne 0 (Or.inl rfl)
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    have hit_of_s1_fp : ∀ (addr : BitVec 64) (blk : Ivl),
        blk ∈ htabFootprint s1 t → CellHits addr.toNat blk →
        (∃ j ∈ htabFootprint s0 t, CellHits addr.toNat j) ∨
          CellHits addr.toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      intro addr blk hblk hhit
      rcases (hfp_1 blk hblk).2 with ⟨j, hj, hij⟩ | hfr
      · exact Or.inl ⟨j, hj, cellHits_of_inside hhit hij⟩
      · exact Or.inr (cellHits_of_inside hhit hfr)
    have hit_nd : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        (∃ j ∈ htabFootprint s0 t, CellHits (ndw + nlw * 32#64 + BitVec.ofNat 64 off).toNat j) ∨
          CellHits (ndw + nlw * 32#64 + BitVec.ofNat 64 off).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      intro off hoff
      apply hit_of_s1_fp _ (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])
      rw [haddr_nl off hoff, BitVec.toNat_ofNat]
      have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
      unfold Inside at hnd1_in
      rw [Nat.mod_eq_of_lt (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)]
      unfold CellHits
      rcases hoff with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    have hit_ord : (∃ j ∈ htabFootprint s0 t, CellHits (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)).toNat j) ∨
        CellHits (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      apply hit_of_s1_fp _ (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) (by simp [htabFootprint])
      have hord1_in := (hB1.1 (hdr s1 t 6, (hdr s1 t 10 + 1) * 8) (by simp [htabFootprint])).1
      unfold Inside at hord1_in
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact ⟨by omega, by omega⟩
    have hit_t24 : (∃ j ∈ htabFootprint s0 t, CellHits (tw + 24#64).toNat j) ∨
        CellHits (tw + 24#64).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      have htw24_nat : (tw + 24#64).toNat = t + 24 := by rw [BitVec.toNat_add, show (24#64).toNat = 24 from rfl]; omega
      exact Or.inl ⟨(t, 88), by simp [htabFootprint], by rw [htw24_nat]; exact ⟨by omega, by omega⟩⟩
    have f1 := frameOutside_updW_mem s0 s2 s2.memory rfl _ 0#64 _ _ hfr_s0_s2 (hit_nd 0 (Or.inl rfl))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) s2.clock) rfl
    have f2 := frameOutside_updW_mem s0 _ _ rfl _ valw _ _ f1 (hit_nd 8 (Or.inr (Or.inl rfl)))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) (ndw + nlw * 32#64 + 8#64) valw) s2.clock) rfl
    have f3 := frameOutside_updW_mem s0 _ _ rfl _ posw _ _ f2 (hit_nd 16 (Or.inr (Or.inr (Or.inl rfl))))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW (updW (updW s2.memory (ndw + nlw * 32#64 + 0#64) 0#64) (ndw + nlw * 32#64 + 8#64) valw) (ndw + nlw * 32#64 + 16#64) posw) s2.clock) rfl
    have f4 := frameOutside_updW_mem s0 _ _ rfl _ (BitVec.ofNat 64 (8 * klen)) _ _ f3 (hit_nd 24 (Or.inr (Or.inr (Or.inr rfl))))
      (NS s2 HolFiniteMapExact.empty s2.globals m4 s2.clock) rfl
    have f5 := frameOutside_updW_mem s0 _ _ rfl _ nlw _ _ f4 hit_ord
      (NS s2 HolFiniteMapExact.empty s2.globals (updW m4 (BitVec.ofNat 64 (hdr s1 t 6 + 8 * cnt)) nlw) s2.clock) rfl
    exact frameOutside_updW_mem s0 _ _ rfl _ (BitVec.ofNat 64 (cnt + 1)) _ _ f5 hit_t24 s_end rfl
  have hg2_1 : s2.globals = s1.globals := hmcf_k.2.2.2.2.2.1
  have hgn_end : globN s_end "heap_ptr" = globN s1 "heap_ptr" := by
    change globN s2 "heap_ptr" = _; unfold globN; rw [hg2_1]
  have hal_end : ∀ iv ∈ htabFootprint s_end t, Allocated s_end iv ∧
      ((∃ j ∈ htabFootprint s0 t, Inside iv j.1 (j.1 + j.2)) ∨
        Inside iv (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr"))) := by
    rw [hfp_end]
    intro iv hiv
    obtain ⟨hal_s1, hprov⟩ := hfp_1 iv hiv
    have hal_s2 : Allocated s_end iv := by
      change Allocated s2 iv; unfold Allocated globN; rw [hg2_1]; exact hal_s1
    exact ⟨hal_s2, hprov⟩
  refine ⟨nlw, Fr1, rfl, ⟨guestInv_congr (s := s2) rfl rfl rfl rfl hA2.1, hA2.2⟩,
    hNS_end,
    (hdr_end_other 0 (by omega) (by omega)).trans hh0_1,
    (hdr_end_other 1 (by omega) (by omega)).trans hh1_1,
    hh3_end,
    (hdr_end_other 7 (by omega) (by omega)).trans hh7_1,
    by rw [hh5_end]; exact hnl_0,
    by rw [hh5_end]; exact hnl_8,
    by rw [hh5_end]; exact hnl_16,
    by rw [hh5_end]; exact hnl_24,
    by rw [hh6_end]; exact hord_cnt,
    ?_, ?_,
    by rw [hgn_end]; exact hhp_1,
    ?_, ?_,
    fun k hk => (hg_1 k hk).trans (congrArg (fun g => g.lookup k) hg2_1.symm)⟩
  · intro x hxA off hoff
    rw [hh5_end]
    have hx_ne : x ≠ nlw.toNat := by
      rintro rfl
      have hndAnl : (A ++ [nlw.toNat]).Nodup := (List.nodup_append.mp hnodup1).1
      exact (List.nodup_append.mp hndAnl).2.2 nlw.toNat hxA nlw.toNat (by simp) rfl
    have hx_rng := (hmem1 x).mp (List.mem_append_left _ (List.mem_append_left _ hxA))
    exact (hnd_other x (by omega) hx_ne off hoff).trans (hnd_1 x hxA off hoff)
  · intro i hi
    rw [hh6_end]; exact hord_lt i hi
  · rw [hgn_end]; exact hal_end
  · change FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s_end "heap_ptr" - globN s0 "heap_ptr")
    rw [hgn_end]; exact hfr_end

/-! ## 2. `htab_new_internal` Postcondition -/

def NewInternalPost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) (bitw : BitVec 64)
    (A : List Nat) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s0 "heap_ptr", globN post "heap_ptr" - globN s0 "heap_ptr")
  ∃ ni : BitVec 64, ∃ Fr1 : List Nat,
    v = .val (.word ni) ∧
    ArenaReady post ∧
    NodeState post t (A ++ [ni.toNat]) Fr1 ∧
    hdr post t 0 = hdr s0 t 0 ∧
    hdr post t 1 = hdr s0 t 1 ∧
    hdr post t 3 = hdr s0 t 3 ∧
    hdr post t 7 = hdr s0 t 7 ∧
    hdr s0 t 10 ≤ hdr post t 10 ∧
    nodeF post (hdr post t 5) ni.toNat 0 = 0 ∧
    nodeF post (hdr post t 5) ni.toNat 8 = 0 ∧
    nodeF post (hdr post t 5) ni.toNat 16 = 0 ∧
    nodeF post (hdr post t 5) ni.toNat 24 = bitw.toNat ∧
    (∀ x ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF post (hdr post t 5) x off = nodeF s0 (hdr s0 t 5) x off) ∧
    (∀ i, i < hdr s0 t 10 + 1 →
      memW post (hdr post t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) ∧
    globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s0 post (htabFootprint s0 t) fresh ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = post.globals.lookup k)

theorem locFree_newInternalPost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat)
    (bitw : BitVec 64) (A : List Nat) :
    LocFreePost (NewInternalPost s0 t bitw A) := by
  intro v p L' h
  obtain ⟨ni, Fr1, hv, hA, hNS, c0, c1, c3, c7, c10, n0, n8, n16, n24, cnd, cord, chp, cfp, cfr, cg⟩ := h
  exact ⟨ni, Fr1, hv, ⟨guestInv_congr (s := { p with locals := L' }) rfl rfl rfl rfl hA.1, hA.2⟩,
    hNS, c0, c1, c3, c7, c10, n0, n8, n16, n24, cnd, cord, chp, cfp, cfr, cg⟩

theorem htab_new_internal_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tw bitw : BitVec 64) (A Fr0 : List Nat)
    (ht : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hbit : s0.locals.lookup (ofString "bit") = some (.val (.word bitw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_new_internal)
      (NewInternalPost s0 tw.toNat bitw A) := by
  set t := tw.toNat
  have hLF := locFree_newInternalPost s0 t bitw A
  htab_unfold Guest.Software.guestFn_htab_new_internal
  -- 1. decCall n := htab_new_node(t)
  refine Ret.decCall_new_node_lf hLF tw A Fr0 (by simp [evalAt, evalHOLExact, ht]) hA0 hNS0 hal0 ?_
  intro niw Fr1 s1 hA1 hNS1 hh0_1 hh1_1 hh3_1 hh7_1 hnc_le_1 hnd_1 hord_1 hhp_1 hfp_1 hfr_1 hg_1 hloc_1
  change NodeState s1 t (A ++ [niw.toNat]) Fr1 at hNS1
  change hdr s1 t 0 = hdr s0 t 0 at hh0_1
  change hdr s1 t 1 = hdr s0 t 1 at hh1_1
  change hdr s1 t 3 = hdr s0 t 3 at hh3_1
  change hdr s1 t 7 = hdr s0 t 7 at hh7_1
  change hdr s0 t 10 ≤ hdr s1 t 10 at hnc_le_1
  obtain ⟨hB1, hnodup1, hmem1, hfc1⟩ := hNS1
  obtain ⟨hnc1_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB1
  have hnx1_le : hdr s1 t 8 ≤ hdr s1 t 10 + 1 := hB1.2.2.2.2.2.2.2
  have hni_rng : 1 ≤ niw.toNat ∧ niw.toNat < hdr s1 t 8 :=
    (hmem1 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  have hni_lt_nc1 : niw.toNat < hdr s1 t 10 + 1 := by omega
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨_, hm1_t5⟩ := word_of_hdr s1 tw 5 (by omega) hB1
  -- 2. dec nodes := load(t + 40) via `NS`!
  let L_init := s1.locals.update (ofString "n", .val (.word niw))
  change Ret (NS s1 L_init s1.globals s1.memory s1.clock) _ _
  apply Ret.ns_dec_lf hLF; intro vnd hvnd
  obtain ⟨_, hvnd_eq⟩ := ev_field_load (NS s1 L_init s1.globals s1.memory s1.clock) (ofString "t") tw 40#64
    (by simp [L_init, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "n" ≠ ofString "t" by decide]) vnd hvnd
  have hm40 : s1.memory (tw + 40#64) = .word (BitVec.ofNat 64 (hdr s1 t 5)) := hm1_t5
  have hvnd_eq' : vnd = .val (.word (BitVec.ofNat 64 (hdr s1 t 5))) := by
    rw [NS_memory, hm40] at hvnd_eq; exact hvnd_eq
  subst hvnd_eq'
  set ndw := BitVec.ofNat 64 (hdr s1 t 5)
  have hndw_nat : ndw.toNat = hdr s1 t 5 := by
    have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd1_in; rw [BitVec.toNat_ofNat]; omega
  have eval_nd_ni : ∀ (st : PanSemStateFiniteExact 64 F) (off : Nat),
      st.locals.lookup (ofString "nodes") = some (.val (.word ndw)) →
      st.locals.lookup (ofString "n") = some (.val (.word niw)) →
      evalAt st (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "n"), .const 32#64], .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (ndw + niw * 32#64 + BitVec.ofNat 64 off))) := by
    intro st off hnd_l hn_l
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnd_l, hn_l,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
    rw [hz, BitVec.add_assoc]
  let L_ni : HolFiniteMapExact MlS (ValueHOL 64) := L_init.update (ofString "nodes", .val (.word ndw))
  have hl_nd : L_ni.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_ni, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl_n : L_ni.lookup (ofString "n") = some (.val (.word niw)) := by
    simp [L_ni, L_init, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nodes" ≠ ofString "n" by decide]
  have hl_bit : L_ni.lookup (ofString "bit") = some (.val (.word bitw)) := by
    simp [L_ni, L_init, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, hbit,
      show ofString "nodes" ≠ ofString "bit" by decide, show ofString "n" ≠ ofString "bit" by decide]
  -- 3. Four stores to `ni` (+0 := 0, +8 := 0, +16 := 0, +24 := bit)
  change Ret (NS s1 L_ni s1.globals s1.memory s1.clock) _ _
  refine Ret.ns_storeW (ndw + niw * 32#64 + 0#64) 0#64 (eval_nd_ni _ 0 hl_nd hl_n) rfl ?_
  intro _
  refine Ret.ns_storeW (ndw + niw * 32#64 + 8#64) 0#64 (eval_nd_ni _ 8 hl_nd hl_n) rfl ?_
  intro _
  refine Ret.ns_storeW (ndw + niw * 32#64 + 16#64) 0#64 (eval_nd_ni _ 16 hl_nd hl_n) rfl ?_
  intro _
  refine Ret.ns_storeW (ndw + niw * 32#64 + 24#64) bitw (eval_nd_ni _ 24 hl_nd hl_n)
    (by simp [evalAt, evalHOLExact, hl_bit]) ?_
  intro _
  apply Ret.ns_ret; intro val hval
  have hval_eq : val = .val (.word niw) := by
    simp [evalAt, evalHOLExact, hl_n] at hval; exact hval.symm
  subst hval_eq
  set m_ni := updW (updW (updW (updW s1.memory (ndw + niw * 32#64 + 0#64) 0#64)
                (ndw + niw * 32#64 + 8#64) 0#64)
                (ndw + niw * 32#64 + 16#64) 0#64)
                (ndw + niw * 32#64 + 24#64) bitw
  let s_end := NS s1 HolFiniteMapExact.empty s1.globals m_ni s1.clock
  have hsep1 := htabBlocks_cell_sep hB1
  have haddr_ni : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      ndw + niw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s1 t 5 + 32 * niw.toNat + off) := by
    intro off _; rw [← hndw_nat]; exact (ofNat_node_addr ndw niw off).symm
  have hdr_end_eq : ∀ k < 11, hdr s_end t k = hdr s1 t k := by
    intro k hk
    have hne : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        BitVec.ofNat 64 (t + 8 * k) ≠ ndw + niw * 32#64 + BitVec.ofNat 64 off := by
      intro off hoff; rw [haddr_ni off hoff]; exact hsep1.1 k hk niw.toNat hni_lt_nc1 off hoff
    unfold hdr memW
    have hm : s_end.memory (BitVec.ofNat 64 (t + 8 * k)) = s1.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s_end, NS_memory, m_ni, updW, hne 24 (Or.inr (Or.inr (Or.inr rfl))),
        hne 16 (Or.inr (Or.inr (Or.inl rfl))), hne 8 (Or.inr (Or.inl rfl)), hne 0 (Or.inl rfl), ↓reduceIte]
    rw [hm]
  have hh5_end : hdr s_end t 5 = hdr s1 t 5 := hdr_end_eq 5 (by omega)
  have hh6_end : hdr s_end t 6 = hdr s1 t 6 := hdr_end_eq 6 (by omega)
  have hh8_end : hdr s_end t 8 = hdr s1 t 8 := hdr_end_eq 8 (by omega)
  have hh9_end : hdr s_end t 9 = hdr s1 t 9 := hdr_end_eq 9 (by omega)
  have hfp_end : htabFootprint s_end t = htabFootprint s1 t := by
    simp [htabFootprint, hdr_end_eq 1 (by omega), hdr_end_eq 4 (by omega), hh5_end, hh6_end, hdr_end_eq 10 (by omega)]
  have hB_end : HtabBlocks s_end t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv; rw [hfp_end] at hiv; obtain ⟨hin, hwok⟩ := hB1.1 iv hiv
      exact ⟨hin, wordsOK_block s_end hA1.1.memaddrs iv.1 iv.2 hwok.1 hwok.2.1 hin.1 hin.2⟩
    · rw [hfp_end]; exact hB1.2.1
    · rw [hdr_end_eq 0 (by omega)]; exact hB1.2.2.1
    · rw [hdr_end_eq 0 (by omega)]; exact hB1.2.2.2.1
    · rw [hdr_end_eq 1 (by omega), hdr_end_eq 0 (by omega)]; exact hB1.2.2.2.2.1
    · rw [hdr_end_eq 10 (by omega)]; exact hB1.2.2.2.2.2.1
    · rw [hh8_end]; exact hB1.2.2.2.2.2.2.1
    · rw [hh8_end, hdr_end_eq 10 (by omega)]; exact hB1.2.2.2.2.2.2.2
  have hni_0 : nodeF s_end (hdr s1 t 5) niw.toNat 0 = 0 := by
    unfold nodeF memW
    have hne24 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 0 (Or.inl rfl) niw.toNat hni_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    have hne16 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 0 (Or.inl rfl) niw.toNat hni_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    have hne8 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 0 (Or.inl rfl) niw.toNat hni_lt_nc1 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    simp only [s_end, NS_memory, m_ni, updW, haddr_ni 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_ni 16 (Or.inr (Or.inr (Or.inl rfl))),
      haddr_ni 8 (Or.inr (Or.inl rfl)), haddr_ni 0 (Or.inl rfl), hne24, hne16, hne8, ↓reduceIte]
    rfl
  have hni_8 : nodeF s_end (hdr s1 t 5) niw.toNat 8 = 0 := by
    unfold nodeF memW
    have hne24 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    have hne16 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    simp only [s_end, NS_memory, m_ni, updW, haddr_ni 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_ni 16 (Or.inr (Or.inr (Or.inl rfl))),
      haddr_ni 8 (Or.inr (Or.inl rfl)), hne24, hne16, ↓reduceIte]
    rfl
  have hni_16 : nodeF s_end (hdr s1 t 5) niw.toNat 16 = 0 := by
    unfold nodeF memW
    have hne24 := hsep1.2.2.2.1 niw.toNat hni_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl))) niw.toNat hni_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (by omega))
    simp only [s_end, NS_memory, m_ni, updW, haddr_ni 24 (Or.inr (Or.inr (Or.inr rfl))), haddr_ni 16 (Or.inr (Or.inr (Or.inl rfl))), hne24, ↓reduceIte]
    rfl
  have hni_24 : nodeF s_end (hdr s1 t 5) niw.toNat 24 = bitw.toNat := by
    unfold nodeF memW
    simp [s_end, m_ni, updW, haddr_ni 24 (Or.inr (Or.inr (Or.inr rfl)))]
  have hnd_other : ∀ x < hdr s1 t 10 + 1, x ≠ niw.toNat → ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s_end (hdr s1 t 5) x off = nodeF s1 (hdr s1 t 5) x off := by
    intro x hx hxne off hoff
    have hne : ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
        BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off) ≠ ndw + niw * 32#64 + BitVec.ofNat 64 off2 := by
      intro off2 hoff2; rw [haddr_ni off2 hoff2]
      exact hsep1.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc1 off2 hoff2 (Or.inl hxne)
    unfold nodeF memW
    have hm : s_end.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off)) = s1.memory (BitVec.ofNat 64 (hdr s1 t 5 + 32 * x + off)) := by
      simp only [s_end, NS_memory, m_ni, updW, hne 24 (Or.inr (Or.inr (Or.inr rfl))),
        hne 16 (Or.inr (Or.inr (Or.inl rfl))), hne 8 (Or.inr (Or.inl rfl)), hne 0 (Or.inl rfl), ↓reduceIte]
    rw [hm]
  have hord_end : ∀ i < hdr s0 t 10 + 1, memW s_end (hdr s1 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
    intro i hi
    have hi1 : i < hdr s1 t 10 + 1 := by omega
    have hne : ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
        BitVec.ofNat 64 (hdr s1 t 6 + 8 * i) ≠ ndw + niw * 32#64 + BitVec.ofNat 64 off2 := by
      intro off2 hoff2; rw [haddr_ni off2 hoff2]
      exact hsep1.2.2.1 niw.toNat hni_lt_nc1 off2 hoff2 i hi1
    have h1 : memW s_end (hdr s1 t 6 + 8 * i) = memW s1 (hdr s1 t 6 + 8 * i) := by
      unfold memW
      have hm : s_end.memory (BitVec.ofNat 64 (hdr s1 t 6 + 8 * i)) = s1.memory (BitVec.ofNat 64 (hdr s1 t 6 + 8 * i)) := by
        simp only [s_end, NS_memory, m_ni, updW, hne 24 (Or.inr (Or.inr (Or.inr rfl))),
          hne 16 (Or.inr (Or.inr (Or.inl rfl))), hne 8 (Or.inr (Or.inl rfl)), hne 0 (Or.inl rfl), ↓reduceIte]
      rw [hm]
    exact h1.trans (hord_1 i hi)
  have hNS_end : NodeState s_end t (A ++ [niw.toNat]) Fr1 := by
    refine ⟨hB_end, hnodup1, fun x => by rw [hh8_end]; exact hmem1 x, ?_⟩
    rw [hh5_end, hh9_end]
    refine FreeChainF.congr Fr1 _ ?_ hfc1
    intro f hf
    have hf_ne : f ≠ niw.toNat := by
      rintro rfl
      exact (List.nodup_append.mp hnodup1).2.2 niw.toNat (List.mem_append_right _ (by simp)) niw.toNat hf rfl
    have hf_rng := (hmem1 f).mp (List.mem_append_right _ hf)
    exact hnd_other f (by omega) hf_ne 0 (Or.inl rfl)
  have hfr_s0_s1_fp : FrameOutside s0 s1 (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") :=
    fun x hxk hxf => hfr_1 x (fun i hi => by rw [List.mem_singleton.mp hi]; exact hxk (t, 88) (by simp [htabFootprint])) hxf
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    have hit_nd : ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        (∃ j ∈ htabFootprint s0 t, CellHits (ndw + niw * 32#64 + BitVec.ofNat 64 off).toNat j) ∨
          CellHits (ndw + niw * 32#64 + BitVec.ofNat 64 off).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
      intro off hoff
      have hhit_blk : CellHits (ndw + niw * 32#64 + BitVec.ofNat 64 off).toNat (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) := by
        rw [haddr_ni off hoff, BitVec.toNat_ofNat]
        have hnd1_in := (hB1.1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by simp [htabFootprint])).1
        unfold Inside at hnd1_in
        rw [Nat.mod_eq_of_lt (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)]
        unfold CellHits
        rcases hoff with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rcases (hfp_1 (hdr s1 t 5, (hdr s1 t 10 + 1) * 32) (by dsimp [t]; simp [htabFootprint])).2 with ⟨j, hj, hij⟩ | hfr
      · exact Or.inl ⟨j, hj, cellHits_of_inside hhit_blk hij⟩
      · exact Or.inr (cellHits_of_inside hhit_blk hfr)
    have f1 := frameOutside_updW_mem s0 s1 s1.memory rfl _ 0#64 _ _ hfr_s0_s1_fp (hit_nd 0 (Or.inl rfl))
      (NS s1 HolFiniteMapExact.empty s1.globals (updW s1.memory (ndw + niw * 32#64 + 0#64) 0#64) s1.clock) rfl
    have f2 := frameOutside_updW_mem s0 _ _ rfl _ 0#64 _ _ f1 (hit_nd 8 (Or.inr (Or.inl rfl)))
      (NS s1 HolFiniteMapExact.empty s1.globals (updW (updW s1.memory (ndw + niw * 32#64 + 0#64) 0#64) (ndw + niw * 32#64 + 8#64) 0#64) s1.clock) rfl
    have f3 := frameOutside_updW_mem s0 _ _ rfl _ 0#64 _ _ f2 (hit_nd 16 (Or.inr (Or.inr (Or.inl rfl))))
      (NS s1 HolFiniteMapExact.empty s1.globals (updW (updW (updW s1.memory (ndw + niw * 32#64 + 0#64) 0#64) (ndw + niw * 32#64 + 8#64) 0#64) (ndw + niw * 32#64 + 16#64) 0#64) s1.clock) rfl
    exact frameOutside_updW_mem s0 _ _ rfl _ bitw _ _ f3 (hit_nd 24 (Or.inr (Or.inr (Or.inr rfl)))) s_end rfl
  refine ⟨niw, Fr1, rfl, ⟨guestInv_congr (s := s1) rfl rfl rfl rfl hA1.1, hA1.2⟩,
    hNS_end,
    (hdr_end_eq 0 (by omega)).trans hh0_1,
    (hdr_end_eq 1 (by omega)).trans hh1_1,
    (hdr_end_eq 3 (by omega)).trans hh3_1,
    (hdr_end_eq 7 (by omega)).trans hh7_1,
    (by change hdr s0 t 10 ≤ hdr s_end t 10; rw [hdr_end_eq 10 (by omega)]; exact hnc_le_1),
    by rw [hh5_end]; exact hni_0,
    by rw [hh5_end]; exact hni_8,
    by rw [hh5_end]; exact hni_16,
    by rw [hh5_end]; exact hni_24,
    ?_, ?_,
    hhp_1,
    (by change ∀ iv ∈ htabFootprint s_end t, Allocated s1 iv ∧ _
        rw [hfp_end]; exact hfp_1),
    hfr_end, hg_1⟩
  · intro x hxA off hoff
    rw [hh5_end]
    have hx_ne : x ≠ niw.toNat := by
      rintro rfl
      have hndAni : (A ++ [niw.toNat]).Nodup := (List.nodup_append.mp hnodup1).1
      exact (List.nodup_append.mp hndAni).2.2 niw.toNat hxA niw.toNat (by simp) rfl
    have hx_rng := (hmem1 x).mp (List.mem_append_left _ (List.mem_append_left _ hxA))
    exact (hnd_other x (by omega) hx_ne off hoff).trans (hnd_1 x hxA off hoff)
  · intro i hi
    rw [hh6_end]; exact hord_end i hi

/-- `Ret.decCall_new_leaf_lf`: call `htab_new_leaf(et, ekey, eval_)` under `LocFreePost Φ`! -/
theorem Ret.decCall_new_leaf_lf {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {x : MlS} {et ekey eval_ : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (tw keyw valw : BitVec 64) (A Fr0 : List Nat)
    (het : evalAt s0 et = some (.val (.word tw)))
    (hekey : evalAt s0 ekey = some (.val (.word keyw)))
    (heval : evalAt s0 eval_ = some (.val (.word valw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hcnt_le : hdr s0 tw.toNat 3 ≤ A.length)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hk : ∀ (nlw : BitVec 64) (Fr1 : List Nat) (s1 : PanSemStateFiniteExact 64 F),
      ArenaReady s1 →
      NodeState s1 tw.toNat (A ++ [nlw.toNat]) Fr1 →
      hdr s1 tw.toNat 0 = hdr s0 tw.toNat 0 →
      hdr s1 tw.toNat 1 = hdr s0 tw.toNat 1 →
      hdr s1 tw.toNat 3 = hdr s0 tw.toNat 3 + 1 →
      hdr s1 tw.toNat 7 = hdr s0 tw.toNat 7 →
      nodeF s1 (hdr s1 tw.toNat 5) nlw.toNat 0 = 0 →
      nodeF s1 (hdr s1 tw.toNat 5) nlw.toNat 8 = valw.toNat →
      nodeF s1 (hdr s1 tw.toNat 5) nlw.toNat 16 = hdr s0 tw.toNat 3 →
      nodeF s1 (hdr s1 tw.toNat 5) nlw.toNat 24 = 8 * hdr s0 tw.toNat 0 →
      memW s1 (hdr s1 tw.toNat 6 + 8 * hdr s0 tw.toNat 3) = nlw.toNat →
      (∀ z ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        nodeF s1 (hdr s1 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off) →
      (∀ i, i < hdr s0 tw.toNat 3 →
        memW s1 (hdr s1 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i)) →
      globN s0 "heap_ptr" ≤ globN s1 "heap_ptr" →
      (∀ i ∈ htabFootprint s1 tw.toNat, Allocated s1 i ∧
        ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
          Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr")))) →
      FrameOutside s0 s1 (htabFootprint s0 tw.toNat) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") →
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s0.globals.lookup k = s1.globals.lookup k) →
      s1.locals = s0.locals →
      Ret (setVarHOLFinite x (.val (.word nlw)) s1) cont Φ) :
    Ret s0 (.decCall x .one (ofString "htab_new_leaf") [et, ekey, eval_] cont) Φ := by
  refine Ret.decCall3_lf hLF hA0.1.code (by decide) (by decide) (by decide)
    lookup_htab_new_leaf tw keyw valw het hekey heval ?_
  intro nlw post hrun
  let entry := callEntryStateHOLFinite s0
    (((HolFiniteMapExact.empty.update (ofString "t", .val (.word tw))).update
      (ofString "key", .val (.word keyw))).update (ofString "value", .val (.word valw)))
  have hspec := htab_new_leaf_body_spec entry tw keyw valw A Fr0
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "value" ≠ ofString "t" by decide, show ofString "key" ≠ ofString "t" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "value" ≠ ofString "key" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hNS0 hcnt_le hal0
    (.val (.word nlw)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨nlw', Fr1, heq, hAp, hNSp, hh0, hh1, hh3, hh7, n0, n8, n16, n24, ordc, hnd, hord, hhp, hfp, hfr, hg⟩ := hspec
  injection heq with h1; injection h1 with h2; subst h2
  let s1 := { post with locals := s0.locals }
  exact hk nlw Fr1 s1
    ⟨guestInv_congr (s := post) rfl rfl rfl rfl hAp.1, hAp.2⟩
    hNSp hh0 hh1 hh3 hh7 n0 n8 n16 n24 ordc hnd hord hhp hfp hfr hg rfl

/-- `Ret.decCall_new_internal_lf`: call `htab_new_internal(et, ebit)` under `LocFreePost Φ`! -/
theorem Ret.decCall_new_internal_lf {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {x : MlS} {et ebit : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (tw bitw : BitVec 64) (A Fr0 : List Nat)
    (het : evalAt s0 et = some (.val (.word tw)))
    (hebit : evalAt s0 ebit = some (.val (.word bitw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hk : ∀ (niw : BitVec 64) (Fr1 : List Nat) (s1 : PanSemStateFiniteExact 64 F),
      ArenaReady s1 →
      NodeState s1 tw.toNat (A ++ [niw.toNat]) Fr1 →
      hdr s1 tw.toNat 0 = hdr s0 tw.toNat 0 →
      hdr s1 tw.toNat 1 = hdr s0 tw.toNat 1 →
      hdr s1 tw.toNat 3 = hdr s0 tw.toNat 3 →
      hdr s1 tw.toNat 7 = hdr s0 tw.toNat 7 →
      hdr s0 tw.toNat 10 ≤ hdr s1 tw.toNat 10 →
      nodeF s1 (hdr s1 tw.toNat 5) niw.toNat 0 = 0 →
      nodeF s1 (hdr s1 tw.toNat 5) niw.toNat 8 = 0 →
      nodeF s1 (hdr s1 tw.toNat 5) niw.toNat 16 = 0 →
      nodeF s1 (hdr s1 tw.toNat 5) niw.toNat 24 = bitw.toNat →
      (∀ z ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        nodeF s1 (hdr s1 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off) →
      (∀ i, i < hdr s0 tw.toNat 10 + 1 →
        memW s1 (hdr s1 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i)) →
      globN s0 "heap_ptr" ≤ globN s1 "heap_ptr" →
      (∀ i ∈ htabFootprint s1 tw.toNat, Allocated s1 i ∧
        ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
          Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr")))) →
      FrameOutside s0 s1 (htabFootprint s0 tw.toNat) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") →
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s0.globals.lookup k = s1.globals.lookup k) →
      s1.locals = s0.locals →
      Ret (setVarHOLFinite x (.val (.word niw)) s1) cont Φ) :
    Ret s0 (.decCall x .one (ofString "htab_new_internal") [et, ebit] cont) Φ := by
  refine Ret.decCall2_lf hLF hA0.1.code (by decide)
    lookup_htab_new_internal tw bitw het hebit ?_
  intro niw post hrun
  let entry := callEntryStateHOLFinite s0
    ((HolFiniteMapExact.empty.update (ofString "t", .val (.word tw))).update
      (ofString "bit", .val (.word bitw)))
  have hspec := htab_new_internal_body_spec entry tw bitw A Fr0
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "bit" ≠ ofString "t" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hNS0 hal0
    (.val (.word niw)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨niw', Fr1, heq, hAp, hNSp, hh0, hh1, hh3, hh7, hnc_le, n0, n8, n16, n24, hnd, hord, hhp, hfp, hfr, hg⟩ := hspec
  injection heq with h1; injection h1 with h2; subst h2
  let s1 := { post with locals := s0.locals }
  exact hk niw Fr1 s1
    ⟨guestInv_congr (s := post) rfl rfl rfl rfl hAp.1, hAp.2⟩
    hNSp hh0 hh1 hh3 hh7 hnc_le n0 n8 n16 n24 hnd hord hhp hfp hfr hg rfl

end InitECandidate.Solver.Wave8GuestInv.SoloHtabSet
