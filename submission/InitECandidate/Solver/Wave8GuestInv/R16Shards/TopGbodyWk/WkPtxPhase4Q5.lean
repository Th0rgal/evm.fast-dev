import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q4

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # Phase 4Q5: the g8 loop entry (instructions 31-38)

This file continues `WkPtxPhase4Q4`.  It composes the `lst_new` allocation
(`p4Q8_stableLogs_alloc`, instructions 31-33), the tail setup
(`p4Q8_tailSetup`, instructions 34-36) and the copy loop (`p4Q8_loop38`,
loop 38): the loop invariant `P4Q8Loop` is established at the post-setup
state with index `0`, and the loop's exit obligation is handed to the
caller's tail continuation.  The bound on the current receipt slice's
length cell (`hrc32`, established by instruction 27) is carried across the
allocation and the count store into the invariant.

The source logs list (the out-record's list at `w_out + 16`) was allocated
before the fresh `stable_logs` blocks, so each of its regions is a geo
region (`p4Q8OldGeo`): the `lst_new` frame and the count store into the
fresh header leave its cells unchanged. -/

/-! ## Locals across `setVarHOLFinite` -/

/-- A `setVarHOLFinite` binding is read back. -/
theorem p4Q8_lookup_setVar_same {F : Type} (u : PanSemStateFiniteExact 64 F)
    (n : MlS) (v : ValueHOL 64) :
    (setVarHOLFinite n v u).locals.lookup n = some v := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- A `setVarHOLFinite` binding leaves the other locals unchanged. -/
theorem p4Q8_lookup_setVar_other {F : Type} (u : PanSemStateFiniteExact 64 F)
    (n y : MlS) (v : ValueHOL 64) (hy : y ≠ n) :
    (setVarHOLFinite n v u).locals.lookup y = u.locals.lookup y := by
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hy, Ne.symm hy]

/-! ## The `lst_new` frame on the pre-existing allocations -/

/-- A cell of a region allocated at `s` is untouched by an allocation step
whose frame keeps only the (empty) scratch frontier and whose fresh region
is the heap growth `[heap_ptr s, heap_ptr mid)`. -/
theorem p4Q8_alloc_frame_cell {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAm : ArenaOK mid)
    (hhp : globN s "heap_ptr" ≤ globN mid "heap_ptr")
    (hFO : FrameOutside s mid [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr"))
    {a b k : Nat} (hal : Allocated s (a, b)) (hk1 : a ≤ k) (hk2 : k + 8 ≤ a + b) :
    mid.memory (BitVec.ofNat 64 k) = s.memory (BitVec.ofNat 64 k) := by
  have hhl := hAs.2.1
  have h3 := hAs.2.2.1
  have h4 := hAs.2.2.2.1
  have h5 := hAs.2.2.2.2.1
  have hml := hAm.2.1
  have hlim : heapLimit = scratchStart := rfl
  have hse : scratchEnd < 2 ^ 64 := by decide
  have hgeo : k + 8 ≤ globN s "heap_ptr" ∨ globN s "scratch_ptr" ≤ k := by
    rcases hal with hi | hi
    · unfold Inside at hi
      obtain ⟨hi1, hi2⟩ := hi
      dsimp only at hi1 hi2
      exact Or.inl (by omega)
    · unfold Inside at hi
      obtain ⟨hi1, hi2⟩ := hi
      dsimp only at hi1 hi2
      exact Or.inr (by omega)
  have hk64 : k < 2 ^ 64 := by
    rcases hal with hi | hi
    · unfold Inside at hi
      obtain ⟨hi1, hi2⟩ := hi
      dsimp only at hi1 hi2
      omega
    · unfold Inside at hi
      obtain ⟨hi1, hi2⟩ := hi
      dsimp only at hi1 hi2
      omega
  have hk' : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hk64
  refine hFO (BitVec.ofNat 64 k) ?_ ?_
  · intro i hi
    rcases List.mem_singleton.1 hi with rfl
    rw [hk']
    intro hcc
    unfold CellHits at hcc
    obtain ⟨c1, c2⟩ := hcc
    dsimp only at c1 c2
    omega
  · rw [hk']
    intro hcc
    unfold CellHits at hcc
    obtain ⟨c1, c2⟩ := hcc
    dsimp only at c1 c2
    omega

/-! ## The loop entry -/

/-- Instructions 31-38: the `lst_new` allocation of the stable-logs list,
the count store, the `stable_lp` load, the `i` reset and the copy loop.
The tail continuation receives the loop invariant at the loop's exit state
together with the failed loop condition. -/
theorem p4Q8_loopEntry {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (tail : ProgHOL 64)
    (nl_w lp_w : BitVec 64)
    (hnl : s.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hlp : s.locals.lookup (ofString "lp") = some (.val (.word lp_w)))
    (hd_nz : memW s (w_out.toNat + 16) ≠ 0)
    (hnl_eq : nl_w.toNat = memW s (memW s (w_out.toNat + 16) + 8))
    (hlp_eq : lp_w.toNat = memW s (memW s (w_out.toNat + 16)))
    (hLL : LogsListOK s (memW s (w_out.toNat + 16)))
    (hDF : LogsDisjFixed s (memW s (w_out.toNat + 16)))
    (hnl28 : nl_w.toNat < 2 ^ 28)
    (hrc32 : memW s (memW s (globN s "bo" + 32) + 16 * locN entry "index" + 8) < 2 ^ 40)
    (htail : ∀ (lw capw w_lp : BitVec 64) (t' : PanSemStateFiniteExact 64 F) (i_w : BitVec 64),
      P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w t' →
      evalAt t' p4Loop38Cond = some (.val (.word 0#64)) →
      PtxRelRunStrong entry tail t') :
    PtxRelRunStrong entry
      (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl"))
        (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap"))
            (.const 0x0000000000000000#64))
          (.assign .local (ofString "stable_log_cap")
            (.const 0x0000000000000001#64))
          .skip)
        (.decCall (ofString "stable_logs") .one (ofString "lst_new")
          [(.const 0x0000000000000008#64),
            (.var .local (ofString "stable_log_cap"))]
          (.seq (.store (.op .add [.var .local (ofString "stable_logs"),
              (.const 0x0000000000000008#64)])
              (.var .local (ofString "nl")))
            (.dec (ofString "stable_lp") .one
              (.load .one (.op .add [.var .local (ofString "stable_logs"),
                (.const 0x0000000000000000#64)]))
              (.seq (.assign .local (ofString "i") (.const 0x0000000000000000#64))
                (.seq (.while p4Loop38Cond p4Loop38Body) tail))))))) s := by
  refine p4Q8_stableLogs_alloc h hc _ nl_w lp_w hnl hlp (Nat.le_of_lt hnl28) ?_
  intro capw lw mid hcap1 hnlcap hmul hlw_eq hlw_al hlw_nz hm0 hm8 hm16 hgl_mid hhp_lt hARmid
    hsp_mid hfmp_mid hlst_mid hobjs_mid hdisj_mid hobjs_props hFO_mid hk_mid hlocm hlocap
    hlocl hwout hchain0 hDmid hcmid
  -- ===== 0. arena geometry =====
  have hAs : ArenaOK s := h.base.world.1.2
  have hAm : ArenaOK mid := hARmid.2
  have hsb_s := hAs.1
  have hhl_m := hAm.2.1
  have hhe64 : heapLimit < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (by decide : heapLimit ≤ heapEnd) (by decide : heapEnd < 2 ^ 64)
  have hse64 : scratchEnd < 2 ^ 64 := by decide
  have hhp_le : globN s "heap_ptr" ≤ globN mid "heap_ptr" := Nat.le_of_lt hhp_lt
  have hlt64 : lw.toNat < 2 ^ 64 := lw.isLt
  have hlw_ge : sourceBase ≤ lw.toNat := by
    rw [hlw_eq]
    exact hsb_s
  have hheap_lim : lw.toNat + 24 ≤ heapLimit := by omega
  have hlim64 : lw.toNat + 24 + 8 * capw.toNat ≤ 2 ^ 64 := by omega
  have hlw_of : BitVec.ofNat 64 lw.toNat = lw := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  -- the data-base word of the fresh header
  obtain ⟨w_lp, hw0', hwlp_nat⟩ : ∃ w_lp : BitVec 64,
      mid.memory lw = .word w_lp ∧ w_lp.toNat = lw.toNat + 24 := by
    have h0 := hm0
    unfold memW at h0
    rw [hlw_of] at h0
    cases hc2 : mid.memory lw with
    | word w =>
      rw [hc2] at h0
      exact ⟨w, rfl, h0⟩
  -- ===== 1. the source list at `s` =====
  have hLL' := hLL
  rcases hLL' with h0 | ⟨hhdw_s, hhd_alloc_s, hhd8c_s, hhd16c_s, hent_s⟩
  · exact absurd h0 hd_nz
  have ha_arr_s : Allocated s (lp_w.toNat, 8 * nl_w.toNat) := by
    rcases hDF with h0 | ⟨ha, _⟩
    · exact absurd h0 hd_nz
    · rw [hlp_eq, hnl_eq]
      exact ha
  have geo_hdr_s : p4Q8OldGeo lw.toNat (memW s (w_out.toNat + 16), 24) :=
    p4Q8OldGeo_of_alloc hAs hlw_eq.symm hhd_alloc_s
  have geo_arr : p4Q8OldGeo lw.toNat (lp_w.toNat, 8 * nl_w.toNat) :=
    p4Q8OldGeo_of_alloc hAs hlw_eq.symm ha_arr_s
  have hgeo_out : p4Q8OldGeo lw.toNat (w_out.toNat, 96) :=
    Or.inl ⟨h.out_inside.1, hwout⟩
  have hent_s' : ∀ i, i < nl_w.toNat →
      WordAt s (lp_w.toNat + 8 * i) ∧ LogEntryOK s (memW s (lp_w.toNat + 8 * i)) := by
    intro i hi
    have hi' : i < memW s (memW s (w_out.toNat + 16) + 8) := by
      rw [← hnl_eq]
      exact hi
    have hthis := hent_s i hi'
    rw [← hlp_eq] at hthis
    exact hthis
  have hent_geo_s : ∀ i, i < nl_w.toNat →
      p4Q8OldGeo lw.toNat (memW s (lp_w.toNat + 8 * i), 40) := by
    intro i hi
    have hle := (hent_s' i hi).2.2.1
    refine Or.inl ⟨hle.1, ?_⟩
    rw [hlw_eq]
    exact hle.2
  -- ===== 2. the `lst_new` frame on the source list =====
  have hframe : ∀ a b : Nat, Allocated s (a, b) → ∀ k : Nat, a ≤ k → k + 8 ≤ a + b →
      memW mid k = memW s k := by
    intro a b hal k hk1 hk2
    unfold memW
    rw [p4Q8_alloc_frame_cell hAs hAm hhp_le hFO_mid hal hk1 hk2]
  have h16_mid : memW mid (w_out.toNat + 16) = memW s (w_out.toNat + 16) :=
    hframe w_out.toNat 96 (Or.inl h.out_inside) _ (by omega) (by omega)
  have hhd0_mid : memW mid (memW s (w_out.toNat + 16)) =
      memW s (memW s (w_out.toNat + 16)) :=
    hframe _ 24 hhd_alloc_s _ (by omega) (by omega)
  have hhd8_mid : memW mid (memW s (w_out.toNat + 16) + 8) =
      memW s (memW s (w_out.toNat + 16) + 8) :=
    hframe _ 24 hhd_alloc_s _ (by omega) (by omega)
  have harr_cell_mid : ∀ i, i < nl_w.toNat →
      memW mid (lp_w.toNat + 8 * i) = memW s (lp_w.toNat + 8 * i) := by
    intro i hi
    exact hframe lp_w.toNat (8 * nl_w.toNat) ha_arr_s _ (by omega) (by omega)
  have hlp_mid : memW mid (memW mid (w_out.toNat + 16)) = lp_w.toNat := by
    rw [h16_mid, hhd0_mid]
    exact hlp_eq.symm
  have hnl8_mid : memW mid (memW mid (w_out.toNat + 16) + 8) = nl_w.toNat := by
    rw [h16_mid, hhd8_mid]
    exact hnl_eq.symm
  have hnz_mid : memW mid (w_out.toNat + 16) ≠ 0 := by
    rw [h16_mid]
    exact hd_nz
  have geo_hdr_mid : p4Q8OldGeo lw.toNat (memW mid (w_out.toNat + 16), 24) := by
    rw [h16_mid]
    exact geo_hdr_s
  have harr_mid : p4Q8OldGeo lw.toNat
      (memW mid (memW mid (w_out.toNat + 16)),
        8 * memW mid (memW mid (w_out.toNat + 16) + 8)) := by
    rw [hnl8_mid, hlp_mid]
    exact geo_arr
  have hent_mid : ∀ i, i < memW mid (memW mid (w_out.toNat + 16) + 8) →
      p4Q8OldGeo lw.toNat
        (memW mid (memW mid (memW mid (w_out.toNat + 16)) + 8 * i), 40) := by
    intro i hi
    rw [hnl8_mid] at hi
    rw [hlp_mid, harr_cell_mid i hi]
    exact hent_geo_s i hi
  -- the source entries at `mid`
  have hLLm := hDmid.logs_ok
  rcases hLLm with h0 | ⟨hhdw_m, hhd_alloc_m, hhd8c_m, hhd16c_m, hent_m⟩
  · exact absurd h0 hnz_mid
  have hent_m' : ∀ j, j < nl_w.toNat →
      WordAt mid (lp_w.toNat + 8 * j) ∧ LogEntryOK mid (memW mid (lp_w.toNat + 8 * j)) := by
    intro j hj
    have hj' : j < memW mid (memW mid (w_out.toNat + 16) + 8) := by
      rw [hnl8_mid]
      exact hj
    have hthis := hent_m j hj'
    rw [hlp_mid] at hthis
    exact hthis
  -- ===== 3. the count store (block `(lw, 24)`, offset 8) =====
  have hhdr_words : WordsOK mid (lw.toNat, 24) :=
    (hobjs_props (lw.toNat, 24) (by rw [hobjs_mid]; simp)).2.1
  have harr_words : WordsOK mid (lw.toNat + 24, 8 * capw.toNat) :=
    (hobjs_props (lw.toNat + 24, 8 * capw.toNat) (by rw [hobjs_mid]; simp)).2.1
  have hdom8 : mid.memaddrs (BitVec.ofNat 64 (lw.toNat + 8)) := by
    obtain ⟨u, hd8, _⟩ := hhdr_words.2.2 1 (by norm_num)
    have hz8 : BitVec.ofNat 64 (lw.toNat + 8 * 1) = BitVec.ofNat 64 (lw.toNat + 8) := by
      simp only [Nat.mul_one]
    rwa [hz8] at hd8
  have hst_cnt : @panMemStoresHOL 64 _ (BitVec.ofNat 64 (lw.toNat + 8))
      (flattenHOL (.val (.word nl_w))) mid.memaddrs
      (fun a => Classical.propDecidable (mid.memaddrs a)) mid.memory
      = some (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w) :=
    p4Q8_store_word_eq hdom8
  have hflen : (flattenHOL (.val (.word nl_w) : ValueHOL 64)).length = 1 := by
    simp [flattenHOL]
  have hx8 : BitVec.ofNat 64 (lw.toNat + 8) = lw + BitVec.ofNat 64 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hin_blk : Inside (lw.toNat, 24) sourceBase (globN mid "heap_ptr") := by
    unfold Inside
    dsimp only
    omega
  have hW_mid : WorldOK mid := hDmid.base.world
  have hstep_cnt : WorldStep (fun _ => [(lw.toNat, 24)]) [] stdKeep NoExtra mid none
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    worldStep_store_in_block hW_mid rfl hlw_al (by norm_num) (by norm_num) hin_blk hx8
      (by omega) hst_cnt
  have hAR_post : ArenaReady
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    hstep_cnt.1
  have hcode_post :
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}.code =
        originalRuntimeCode := hcmid
  obtain ⟨hcell_cnt, hEff_cnt⟩ := p4Q8_store_effect (t := mid) (base := lw.toNat)
    (sz := 24) (off := 8) (w_base := lw)
    (x := BitVec.ofNat 64 (lw.toNat + 8)) (v := (.val (.word nl_w) : ValueHOL 64))
    (mem' := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)
    hW_mid hAR_post hcode_post rfl hlw_al (by omega) (by norm_num) hin_blk hx8 (by omega)
    (by rw [hst_cnt])
  -- the chain and base at the post-store state
  have hchain_mid : p4Q8Chain entry s_pmc w_out lw capw mid := p4Q8Chain_of_bundle hchain0
  have hhp_ent_s : globN entry "heap_ptr" ≤ globN s "heap_ptr" := h.base.heap_entry
  have hhp_ent_lw : globN entry "heap_ptr" ≤ lw.toNat := by
    rw [hlw_eq]
    exact hhp_ent_s
  have hR_fresh : Inside (lw.toNat, 24) (globN entry "heap_ptr") (globN mid "heap_ptr") := by
    unfold Inside
    dsimp only
    omega
  have hRh : Disj (memW mid (w_out.toNat + 16), 24) (lw.toNat, 24) :=
    p4Q8OldGeo_disj geo_hdr_mid (le_refl _) hheap_lim
  have hRa : memW mid (w_out.toNat + 16) ≠ 0 →
      Disj (memW mid (memW mid (w_out.toNat + 16)),
        8 * memW mid (memW mid (w_out.toNat + 16) + 8)) (lw.toNat, 24) :=
    fun _ => p4Q8OldGeo_disj harr_mid (le_refl _) hheap_lim
  have hRe : memW mid (w_out.toNat + 16) ≠ 0 →
      ∀ i, i < memW mid (memW mid (w_out.toNat + 16) + 8) →
      Disj (memW mid (memW mid (memW mid (w_out.toNat + 16)) + 8 * i), 40) (lw.toNat, 24) :=
    fun _ i hi => p4Q8OldGeo_disj (hent_mid i hi) (le_refl _) hheap_lim
  have hw_out_blk : Disj (w_out.toNat, 96) (lw.toNat, 24) := by
    refine Or.inr (Or.inr (Or.inl ?_))
    dsimp only
    omega
  have hchain_post : p4Q8Chain entry s_pmc w_out lw capw
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    p4Q8Chain_store hchain_mid hW_mid hDmid.heap_pmc hDmid.base.heap_entry
      hDmid.base.frame_entry hDmid.base.scratch_entry hDmid.base.arena_entry hR_fresh rfl
      hlw_al (by norm_num) (by norm_num) hin_blk hx8 (by omega) hst_cnt (Or.inl rfl)
      (by have := hDmid.out_words.1; omega) hDmid.out_words hDmid.out_inside hw_out_blk
      hDmid.logs_ok hRh hRa hRe
  have hbo_unhit : PtxBlockOutUnhit mid
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    p4Q8_blockOutUnhit_store hchain_mid hDmid.base.ready_entry (Or.inl rfl) hARmid hEff_cnt
  have hcells : PtxBoCells true entry mid
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    p4Q8_boCells_store hDmid.base hchain_mid (Or.inl rfl) (by omega) hstep_cnt hbo_unhit
  have hbase_post : PtxRelBase true entry
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} :=
    p4Q8Base_store hDmid.base hchain_mid hchain_post (Or.inl rfl) (by omega) hstep_cnt hcells
  -- ===== 4. cell stability across the count store =====
  have hgeo64 : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → a + b < 2 ^ 64 := by
    intro a b hgeo
    rcases hgeo with hg | hg
    · unfold Inside at hg
      obtain ⟨hg1, hg2⟩ := hg
      omega
    · unfold Inside at hg
      obtain ⟨hg1, hg2⟩ := hg
      omega
  have hmemW_geo : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → ∀ k : Nat,
      a ≤ k → k + 8 ≤ a + b →
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w} k =
      memW mid k := by
    intro a b hgeo k hk1 hk2
    exact p4Q8MemW_store_of_geo hcell_cnt hgeo ⟨hk1, hk2⟩ (le_refl _) hheap_lim
      (by have := hgeo64 a b hgeo; omega)
  have hwordAt_geo : ∀ a b : Nat, p4Q8OldGeo lw.toNat (a, b) → ∀ k : Nat,
      a ≤ k → k + 8 ≤ a + b → WordAt mid k →
      WordAt {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        k := by
    intro a b hgeo k hk1 hk2 hwd
    exact p4Q8WordAt_store_of_geo hcell_cnt hwd hgeo ⟨hk1, hk2⟩ (le_refl _) hheap_lim
      (by have := hgeo64 a b hgeo; omega)
  have h16_post :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 16) = memW mid (w_out.toNat + 16) :=
    hmemW_geo w_out.toNat 96 hgeo_out _ (by omega) (by omega)
  have h80_post :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 80) = memW mid (w_out.toNat + 80) :=
    hmemW_geo w_out.toNat 96 hgeo_out _ (by omega) (by omega)
  have h88_post :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 88) = memW mid (w_out.toNat + 88) :=
    hmemW_geo w_out.toNat 96 hgeo_out _ (by omega) (by omega)
  have hhd0_post :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (memW mid (w_out.toNat + 16)) = memW mid (memW mid (w_out.toNat + 16)) :=
    hmemW_geo _ 24 geo_hdr_mid _ (by omega) (by omega)
  have hhd8_post :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (memW mid (w_out.toNat + 16) + 8) = memW mid (memW mid (w_out.toNat + 16) + 8) :=
    hmemW_geo _ 24 geo_hdr_mid _ (by omega) (by omega)
  -- ===== 5. the source-list transports =====
  have harr64 : memW mid (memW mid (w_out.toNat + 16)) +
      8 * memW mid (memW mid (w_out.toNat + 16) + 8) ≤ 2 ^ 64 := by
    have := hgeo64 _ _ harr_mid
    omega
  have hent64 : ∀ i, i < memW mid (memW mid (w_out.toNat + 16) + 8) →
      memW mid (memW mid (memW mid (w_out.toNat + 16)) + 8 * i) + 40 ≤ 2 ^ 64 := by
    intro i hi
    have := hgeo64 _ _ (hent_mid i hi)
    omega
  have hh64 : memW mid (w_out.toNat + 16) + 24 ≤ 2 ^ 64 := by
    have := hgeo64 _ _ geo_hdr_mid
    omega
  have hsrc_logs' : LogsListOK
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
      (memW mid (w_out.toNat + 16)) :=
    p4Q8LogsListOK_store hcell_cnt hnz_mid hDmid.logs_ok geo_hdr_mid harr_mid hent_mid
      (le_refl _) hheap_lim hh64 harr64 hent64
  have hsrc_ent_P : ∀ j, j < nl_w.toNat →
      WordAt {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (lp_w.toNat + 8 * j) ∧
      LogEntryOK {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
          (lp_w.toNat + 8 * j)) ∧
      p4Q8OldGeo lw.toNat
        (memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
          (lp_w.toNat + 8 * j), 40) := by
    intro j hj
    have hvalj :
        memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
          (lp_w.toNat + 8 * j) = memW mid (lp_w.toNat + 8 * j) :=
      hmemW_geo lp_w.toNat (8 * nl_w.toNat) geo_arr _ (by omega) (by omega)
    obtain ⟨hw1, hw2⟩ := hent_m' j hj
    have hw3 : p4Q8OldGeo lw.toNat (memW mid (lp_w.toNat + 8 * j), 40) := by
      rw [harr_cell_mid j hj]
      exact hent_geo_s j hj
    refine ⟨hwordAt_geo lp_w.toNat (8 * nl_w.toNat) geo_arr
        (lp_w.toNat + 8 * j) (by omega) (by omega) hw1, ?_, by rw [hvalj]; exact hw3⟩
    rw [hvalj]
    exact p4Q8LogEntryOK_store hcell_cnt hw2 hw3 (le_refl _) hheap_lim
      (by have := hgeo64 _ _ hw3; omega)
  have hsrc_nz_P :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 16) ≠ 0 := by
    rw [h16_post]
    exact hnz_mid
  have hsrc_logs_P : LogsListOK
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
      (memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 16)) := by
    rw [h16_post]
    exact hsrc_logs'
  have hsrc_lp_P : lp_w.toNat =
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
          (w_out.toNat + 16)) := by
    rw [h16_post, hhd0_post]
    exact hlp_mid.symm
  have hsrc_len_P :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
          (w_out.toNat + 16) + 8) = nl_w.toNat := by
    rw [h16_post]
    exact hhd8_post.trans hnl8_mid
  have hgeo_hdr_P : p4Q8OldGeo lw.toNat
      (memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 16), 24) := by
    rw [h16_post]
    exact geo_hdr_mid
  -- the marks transport
  have hmarks_P :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 80) ≠ 0 →
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 80) % 8 = 0 ∧
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 88) % 8 = 0 ∧
      globN s_pmc "frame_mem_ptr" ≤
        memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
          (w_out.toNat + 88) ∧
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 88) ≤
        memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
          (w_out.toNat + 80) ∧
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr" := by
    rw [h80_post, h88_post]
    exact hDmid.marks
  -- ===== 6. the locals of the post-setup state =====
  have hnl_mid : mid.locals.lookup (ofString "nl") = some (.val (.word nl_w)) := by
    rw [hlocl (ofString "nl") (by decide) (by decide)]
    exact hnl
  have hlp_loc_mid : mid.locals.lookup (ofString "lp") = some (.val (.word lp_w)) := by
    rw [hlocl (ofString "lp") (by decide) (by decide)]
    exact hlp
  have hlu : ∀ y : MlS, y ≠ ofString "i" → y ≠ ofString "stable_lp" →
      (setVarHOLFinite (ofString "i") (.val (.word 0x0000000000000000#64))
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp))
          {mid with memory :=
            (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)})).locals.lookup y =
      mid.locals.lookup y := by
    intro y h1 h2
    exact (p4Q8_lookup_setVar_other _ _ _ _ h1).trans (p4Q8_lookup_setVar_other _ _ _ _ h2)
  have hlu_slp :
      (setVarHOLFinite (ofString "i") (.val (.word 0x0000000000000000#64))
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp))
          {mid with memory :=
            (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)})).locals.lookup
        (ofString "stable_lp") = some (.val (.word w_lp)) :=
    (p4Q8_lookup_setVar_other _ _ _ _ (by decide)).trans (p4Q8_lookup_setVar_same _ _ _)
  -- the current receipt slice across the allocation and the count store
  have hrc_mid : memW mid (memW mid (globN mid "bo" + 32) + 16 * locN entry "index" + 8) <
      2 ^ 40 :=
    lt_of_eq_of_lt (p4Q8_rcptCur_of_fresh_heap h.base hDmid.base hARmid hFO_mid) hrc32
  have hrc_post :
      memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
          (globN {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
            "bo" + 32) + 16 * locN entry "index" + 8) < 2 ^ 40 :=
    lt_of_eq_of_lt (p4Q8_rcptCur_of_unhit hDmid.base hbase_post hbo_unhit) hrc_mid
  -- ===== 7. the loop invariant at the post-setup state =====
  have hINV : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w 0x0000000000000000#64
      (setVarHOLFinite (ofString "i") (.val (.word 0x0000000000000000#64))
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp))
          {mid with memory :=
            (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)})) :=
    ⟨ptxRelBase_with_locals hbase_post
        ((mid.locals.update (ofString "stable_lp", (.val (.word w_lp) : ValueHOL 64))).update
          (ofString "i", (.val (.word 0x0000000000000000#64) : ValueHOL 64)))
        mid.clock,
      p4Q8Chain_with_locals
        (t := {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w})
        ((mid.locals.update (ofString "stable_lp", (.val (.word w_lp) : ValueHOL 64))).update
          (ofString "i", (.val (.word 0x0000000000000000#64) : ValueHOL 64)))
        mid.clock hchain_post,
      localsFree_worldOK
        ({mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w})
        ((mid.locals.update (ofString "stable_lp", (.val (.word w_lp) : ValueHOL 64))).update
          (ofString "i", (.val (.word 0x0000000000000000#64) : ValueHOL 64)))
        mid.clock hbase_post.world,
      hcmid, hlw_al, hlw_ge, hhp_ent_lw, hcap1, hnlcap, hnl28, hwlp_nat, hlim64, hgl_mid,
      hDmid.heap_pmc,
      (hlu (ofString "out") (by decide) (by decide)).trans hDmid.out_local,
      (hlu (ofString "nl") (by decide) (by decide)).trans hnl_mid,
      (hlu (ofString "stable_logs") (by decide) (by decide)).trans hlocm,
      hlu_slp,
      (hlu (ofString "lp") (by decide) (by decide)).trans hlp_loc_mid,
      p4Q8_lookup_setVar_same _ _ _,
      pmc_wordsOK_updW mid (BitVec.ofNat 64 (lw.toNat + 8)) nl_w (w_out.toNat, 96)
        hDmid.out_words,
      hDmid.out_inside, hwout, hmarks_P, hsrc_nz_P, hsrc_logs_P, hsrc_lp_P, hsrc_len_P,
      hgeo_hdr_P, geo_arr, hsrc_ent_P,
      pmc_wordsOK_updW mid (BitVec.ofNat 64 (lw.toNat + 8)) nl_w (lw.toNat, 24) hhdr_words,
      pmc_wordsOK_updW mid (BitVec.ofNat 64 (lw.toNat + 8)) nl_w
        (lw.toNat + 24, 8 * capw.toNat) harr_words,
      Nat.zero_le _,
      fun j hj => absurd hj (Nat.not_lt_zero j),
      h.arena_pmc,
      (hlu (ofString "index") (by decide) (by decide)).trans hDmid.idx_local,
      (pmc_memW_updW_ne mid (lw.toNat + 8) lw.toNat nl_w (by omega) (by omega)
        (by omega)).trans hm0,
      pmc_memW_updW_same mid (lw.toNat + 8) nl_w,
      (pmc_memW_updW_ne mid (lw.toNat + 8) (lw.toNat + 16) nl_w (by omega) (by omega)
        (by omega)).trans hm16,
      hrc_post⟩
  -- ===== 8. the setup and the loop =====
  refine p4Q8_tailSetup (.seq (.while p4Loop38Cond p4Loop38Body) tail) hnl_mid hlocm
    hhdr_words (by omega) hw0' ?_
  exact p4Q8_loop38 hINV (fun t' i_w hL hcond => htail lw capw w_lp t' i_w hL hcond)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
