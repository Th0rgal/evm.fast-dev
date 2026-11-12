import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q5
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q6A

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

/-! # Phase 4Q5X: the g8 loop exits (instructions 31-38)

This file continues `WkPtxPhase4Q5`.  It turns the copy loop's exit into
the exit bundle `P4Q8Exit` of `WkPtxPhase4Q6A`, on both paths of the g8
segment:

* the copying path (`nl ≠ 0`, `p4Q8_exit_nz`): the loop invariant
  `P4Q8Loop` at the failed loop condition gives `i = nl`, so the copied
  prefix is the whole source list;
* the empty path (`nl = 0`, `p4Q8_exit_zero`): the loop exits at once.
  Nothing is known about the out-record's list beyond `P4Data` (it may be
  null, or non-null of unknown length), so the loop invariant cannot be
  built; the allocation and the count store are replayed against the
  general list, whose geometry comes from `P4Data.logs_ok` (header and
  entries) and the `PmcLogsLiveOwned` clause of `P4Data.logs_facts`
  (backing array). -/

/-! ## The failed loop condition -/

/-- The loop-38 condition `i < nl` evaluating to `0` gives `nl ≤ i`
(signed and unsigned order coincide below `2^28`). -/
theorem p4Q8_loop38_exit_ge {F : Type} {u : PanSemStateFiniteExact 64 F}
    {i_w nl_w : BitVec 64}
    (hi : u.locals.lookup (ofString "i") = some (.val (.word i_w)))
    (hnl : u.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hnl28 : nl_w.toNat < 2 ^ 28)
    (hc : evalAt u p4Loop38Cond = some (.val (.word 0#64))) :
    nl_w.toNat ≤ i_w.toNat := by
  obtain ⟨a, b, ha, hb, hwif⟩ := evalAt_cmp u .less
    (.var .local (ofString "i")) (.var .local (ofString "nl")) 0#64 hc
  have ha' : evalAt u (.var .local (ofString "i")) = some (.val (.word i_w)) := by
    simp [evalAt, evalHOLExact, hi]
  have hb' : evalAt u (.var .local (ofString "nl")) = some (.val (.word nl_w)) := by
    simp [evalAt, evalHOLExact, hnl]
  have hp1 : some ((.val (.word a) : ValueHOL 64)) = some (.val (.word i_w)) := ha.symm.trans ha'
  have hp2 : some ((.val (.word b) : ValueHOL 64)) = some (.val (.word nl_w)) := hb.symm.trans hb'
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hp1 hp2
  rw [hp1, hp2] at hwif
  have h2 : (2 ^ 28 : Nat) < 2 ^ 63 := by decide
  by_cases hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .less i_w nl_w = true
  · rw [if_pos hcmp] at hwif
    exact absurd hwif (by decide)
  · unfold Flapjack.Compiler.Encoders.Asm.wordCmpHOL at hcmp
    simp only at hcmp
    simp only [Flapjack.Compiler.Encoders.Asm.holAsmSignedLess] at hcmp
    split at hcmp
    · split at hcmp
      · simpa using hcmp
      · omega
    · omega

/-- With `nl = 0` and `i = 0` the copy loop exits immediately. -/
theorem p4Q8_loop38_empty {F : Type} {entry t : PanSemStateFiniteExact 64 F}
    {nl_w : BitVec 64} {rest : ProgHOL 64}
    (hi : t.locals.lookup (ofString "i") = some (.val (.word 0x0000000000000000#64)))
    (hnl : t.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hnl0 : nl_w.toNat = 0)
    (hrest : PtxRelRunStrong entry rest t) :
    PtxRelRunStrong entry (.seq (.while p4Loop38Cond p4Loop38Body) rest) t := by
  refine p4Q8_while38 (fun st => st = t) ?_ ?_ t rfl
  · intro st hst _
    rw [hst]
    exact hrest
  · intro st hst hguard _ _
    exfalso
    rw [hst] at hguard
    obtain ⟨wg, hwg, hwne⟩ := hguard
    have hlt := p4Loop31_guard_lt hi hnl (by simp) (by omega) wg hwne hwg
    omega

/-! ## The copying path -/

/-- The loop invariant at the failed loop condition is the exit bundle:
`i = nl`, so every live backing cell of the fresh list holds the matching
entry pointer of the out-record's list. -/
theorem p4Q8Exit_of_loop {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F}
    {w_out lw capw nl_w w_lp lp_w i_w : BitVec 64}
    (h : P4Q8Loop entry s_pmc w_out lw capw nl_w w_lp lp_w i_w t)
    (hcond : evalAt t p4Loop38Cond = some (.val (.word 0#64))) :
    P4Q8Exit entry s_pmc w_out lw capw nl_w t := by
  have hge := p4Q8_loop38_exit_ge h.i_local h.nl_local h.nl_28 hcond
  exact
    { base := h.base
      chain := h.chain
      code := h.code
      arena_pmc := h.arena_pmc
      heap_pmc := h.heap_pmc
      lw_al := h.lw_al
      lw_ge := h.lw_ge
      hp_ent := h.hp_ent
      cap_pos := h.cap_pos
      nl_le_cap := h.nl_le_cap
      nl_28 := h.nl_28
      lim64 := h.lim64
      heap_fr := h.heap_fr
      out_local := h.out_local
      sl_local := h.sl_local
      i_local := ⟨i_w, h.i_local⟩
      idx_local := h.idx_local
      out_words := h.out_words
      out_inside := h.out_inside
      out_below := h.out_below
      marks := h.marks
      src_logs := h.src_logs
      hdr0 := h.hdr0
      hdr8 := h.hdr8
      hdr16 := h.hdr16
      hdr_words := h.hdr_words
      arr_words := h.arr_words
      ents := fun j hj => ⟨h.src_nz, by rw [h.src_len]; exact hj, by
        rw [← h.src_lp_eq]
        exact h.copied j (by have := h.i_le; omega)⟩
      rcpt_cur := h.rcpt_cur }

/-- Instructions 31-38 on the copying path (`nl ≠ 0`): the tail
continuation receives the exit bundle. -/
theorem p4Q8_exit_nz {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out) (hc : s.code = originalRuntimeCode)
    (tail : ProgHOL 64) (nl_w lp_w : BitVec 64)
    (hnl : s.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hlp : s.locals.lookup (ofString "lp") = some (.val (.word lp_w)))
    (hd_nz : memW s (w_out.toNat + 16) ≠ 0)
    (hnl_eq : nl_w.toNat = memW s (memW s (w_out.toNat + 16) + 8))
    (hlp_eq : lp_w.toNat = memW s (memW s (w_out.toNat + 16)))
    (hLL : LogsListOK s (memW s (w_out.toNat + 16)))
    (hDF : LogsDisjFixed s (memW s (w_out.toNat + 16)))
    (hnl28 : nl_w.toNat < 2 ^ 28)
    (hrc32 : memW s (memW s (globN s "bo" + 32) + 16 * locN entry "index" + 8) < 2 ^ 40)
    (htail : ∀ (lw capw : BitVec 64) (t : PanSemStateFiniteExact 64 F),
      P4Q8Exit entry s_pmc w_out lw capw nl_w t → PtxRelRunStrong entry tail t) :
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
                (.seq (.while p4Loop38Cond p4Loop38Body) tail))))))) s :=
  p4Q8_loopEntry h hc tail nl_w lp_w hnl hlp hd_nz hnl_eq hlp_eq hLL hDF hnl28 hrc32
    (fun lw capw _ t' _ hL hcond => htail lw capw t' (p4Q8Exit_of_loop hL hcond))

/-! ## The empty path -/

/-- Instructions 31-38 on the empty path (`nl = 0`): the capacity is
clamped to `1`, the count store writes `0`, and the copy loop exits at
once.  The out-record's list is arbitrary (null, or non-null of unknown
length); its regions were allocated before the fresh blocks, so the
allocation frame and the count store leave it intact. -/
theorem p4Q8_exit_zero {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out) (hc : s.code = originalRuntimeCode)
    (tail : ProgHOL 64) (nl_w lp_w : BitVec 64)
    (hnl : s.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hlp : s.locals.lookup (ofString "lp") = some (.val (.word lp_w)))
    (hnl0 : nl_w.toNat = 0)
    (hrc32 : memW s (memW s (globN s "bo" + 32) + 16 * locN entry "index" + 8) < 2 ^ 40)
    (htail : ∀ (lw capw : BitVec 64) (t : PanSemStateFiniteExact 64 F),
      P4Q8Exit entry s_pmc w_out lw capw nl_w t → PtxRelRunStrong entry tail t) :
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
  refine p4Q8_stableLogs_alloc h hc _ nl_w lp_w hnl hlp (by omega) ?_
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
  -- ===== 1. the out-record's list at `s`: every region is allocated =====
  have hsrc_s : memW s (w_out.toNat + 16) ≠ 0 →
      Allocated s (memW s (w_out.toNat + 16), 24) ∧
      Allocated s (memW s (memW s (w_out.toNat + 16)),
        8 * memW s (memW s (w_out.toNat + 16) + 8)) ∧
      ∀ i, i < memW s (memW s (w_out.toNat + 16) + 8) →
        Inside (memW s (memW s (memW s (w_out.toNat + 16)) + 8 * i), 40) sourceBase
          (globN s "heap_ptr") := by
    intro hnz
    have hLL := h.logs_ok
    rcases hLL with h0 | ⟨_, hhd_alloc_s, _, _, hent_s⟩
    · exact absurd h0 hnz
    obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
      S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
    have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
      rw [ptxRegions_eq_bufRegions]
      exact validBufList_disj validBufList_ptxBufs hWT_e
    obtain ⟨logs, _, _, _, hfacts⟩ := h.logs_facts
    obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, _, _, _, _, _, _, _, hlive, _⟩ :=
      hfacts S_e Nd_e hWT_e hD_e
    exact ⟨hhd_alloc_s, (hlive hnz).1, fun i hi => (hent_s i hi).2.2.1⟩
  have hgeo_out : p4Q8OldGeo lw.toNat (w_out.toNat, 96) :=
    Or.inl ⟨h.out_inside.1, hwout⟩
  -- ===== 2. the `lst_new` frame on the out-record's list =====
  have hframe : ∀ a b : Nat, Allocated s (a, b) → ∀ k : Nat, a ≤ k → k + 8 ≤ a + b →
      memW mid k = memW s k := by
    intro a b hal k hk1 hk2
    unfold memW
    rw [p4Q8_alloc_frame_cell hAs hAm hhp_le hFO_mid hal hk1 hk2]
  have h16_mid : memW mid (w_out.toNat + 16) = memW s (w_out.toNat + 16) :=
    hframe w_out.toNat 96 (Or.inl h.out_inside) _ (by omega) (by omega)
  have hgeo_mid : memW mid (w_out.toNat + 16) ≠ 0 →
      p4Q8OldGeo lw.toNat (memW mid (w_out.toNat + 16), 24) ∧
      p4Q8OldGeo lw.toNat
        (memW mid (memW mid (w_out.toNat + 16)),
          8 * memW mid (memW mid (w_out.toNat + 16) + 8)) ∧
      ∀ i, i < memW mid (memW mid (w_out.toNat + 16) + 8) →
        p4Q8OldGeo lw.toNat
          (memW mid (memW mid (memW mid (w_out.toNat + 16)) + 8 * i), 40) := by
    intro hnz
    rw [h16_mid] at hnz ⊢
    obtain ⟨hA_hdr, hA_arr, hE⟩ := hsrc_s hnz
    have hhd0_mid : memW mid (memW s (w_out.toNat + 16)) =
        memW s (memW s (w_out.toNat + 16)) :=
      hframe _ 24 hA_hdr _ (by omega) (by omega)
    have hhd8_mid : memW mid (memW s (w_out.toNat + 16) + 8) =
        memW s (memW s (w_out.toNat + 16) + 8) :=
      hframe _ 24 hA_hdr _ (by omega) (by omega)
    rw [hhd0_mid, hhd8_mid]
    refine ⟨p4Q8OldGeo_of_alloc hAs hlw_eq.symm hA_hdr,
      p4Q8OldGeo_of_alloc hAs hlw_eq.symm hA_arr, ?_⟩
    intro i hi
    rw [hframe _ _ hA_arr (memW s (memW s (w_out.toNat + 16)) + 8 * i) (by omega) (by omega)]
    refine Or.inl ⟨(hE i hi).1, ?_⟩
    rw [hlw_eq]
    exact (hE i hi).2
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
  have hRh : Disj (memW mid (w_out.toNat + 16), 24) (lw.toNat, 24) := by
    by_cases hz : memW mid (w_out.toNat + 16) = 0
    · rw [hz]
      refine Or.inr (Or.inr (Or.inl ?_))
      dsimp only
      omega
    · exact p4Q8OldGeo_disj (hgeo_mid hz).1 (le_refl _) hheap_lim
  have hRa : memW mid (w_out.toNat + 16) ≠ 0 →
      Disj (memW mid (memW mid (w_out.toNat + 16)),
        8 * memW mid (memW mid (w_out.toNat + 16) + 8)) (lw.toNat, 24) :=
    fun hz => p4Q8OldGeo_disj (hgeo_mid hz).2.1 (le_refl _) hheap_lim
  have hRe : memW mid (w_out.toNat + 16) ≠ 0 →
      ∀ i, i < memW mid (memW mid (w_out.toNat + 16) + 8) →
      Disj (memW mid (memW mid (memW mid (w_out.toNat + 16)) + 8 * i), 40) (lw.toNat, 24) :=
    fun hz i hi => p4Q8OldGeo_disj ((hgeo_mid hz).2.2 i hi) (le_refl _) hheap_lim
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
  -- ===== 5. the out-record's list and marks at the post-store state =====
  have hsrc_logs_P : LogsListOK
      {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
      (memW {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w}
        (w_out.toNat + 16)) := by
    rw [h16_post]
    by_cases hz : memW mid (w_out.toNat + 16) = 0
    · exact Or.inl hz
    · obtain ⟨g1, g2, g3⟩ := hgeo_mid hz
      exact p4Q8LogsListOK_store hcell_cnt hz hDmid.logs_ok g1 g2 g3 (le_refl _) hheap_lim
        (by have := hgeo64 _ _ g1; omega) (by have := hgeo64 _ _ g2; omega)
        (fun i hi => by have := hgeo64 _ _ (g3 i hi); omega)
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
  -- ===== 6. the locals of the post-setup state =====
  have hnl_mid : mid.locals.lookup (ofString "nl") = some (.val (.word nl_w)) := by
    rw [hlocl (ofString "nl") (by decide) (by decide)]
    exact hnl
  have hlu : ∀ y : MlS, y ≠ ofString "i" → y ≠ ofString "stable_lp" →
      (setVarHOLFinite (ofString "i") (.val (.word 0x0000000000000000#64))
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp))
          {mid with memory :=
            (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)})).locals.lookup y =
      mid.locals.lookup y := by
    intro y h1 h2
    exact (p4Q8_lookup_setVar_other _ _ _ _ h1).trans (p4Q8_lookup_setVar_other _ _ _ _ h2)
  -- ===== 7. the exit bundle at the post-setup state =====
  have hExit : P4Q8Exit entry s_pmc w_out lw capw nl_w
      (setVarHOLFinite (ofString "i") (.val (.word 0x0000000000000000#64))
        (setVarHOLFinite (ofString "stable_lp") (.val (.word w_lp))
          {mid with memory :=
            (pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w)})) :=
    { base := ptxRelBase_with_locals hbase_post
        ((mid.locals.update (ofString "stable_lp", (.val (.word w_lp) : ValueHOL 64))).update
          (ofString "i", (.val (.word 0x0000000000000000#64) : ValueHOL 64)))
        mid.clock
      chain := p4Q8Chain_with_locals
        (t := {mid with memory := pmcUpdW mid.memory (BitVec.ofNat 64 (lw.toNat + 8)) nl_w})
        ((mid.locals.update (ofString "stable_lp", (.val (.word w_lp) : ValueHOL 64))).update
          (ofString "i", (.val (.word 0x0000000000000000#64) : ValueHOL 64)))
        mid.clock hchain_post
      code := hcmid
      arena_pmc := h.arena_pmc
      heap_pmc := hDmid.heap_pmc
      lw_al := hlw_al
      lw_ge := hlw_ge
      hp_ent := hhp_ent_lw
      cap_pos := hcap1
      nl_le_cap := hnlcap
      nl_28 := by omega
      lim64 := hlim64
      heap_fr := hgl_mid
      out_local := (hlu (ofString "out") (by decide) (by decide)).trans hDmid.out_local
      sl_local := (hlu (ofString "stable_logs") (by decide) (by decide)).trans hlocm
      i_local := ⟨_, p4Q8_lookup_setVar_same _ _ _⟩
      idx_local := (hlu (ofString "index") (by decide) (by decide)).trans hDmid.idx_local
      out_words := pmc_wordsOK_updW mid (BitVec.ofNat 64 (lw.toNat + 8)) nl_w (w_out.toNat, 96)
        hDmid.out_words
      out_inside := hDmid.out_inside
      out_below := hwout
      marks := hmarks_P
      src_logs := hsrc_logs_P
      hdr0 := (pmc_memW_updW_ne mid (lw.toNat + 8) lw.toNat nl_w (by omega) (by omega)
        (by omega)).trans hm0
      hdr8 := pmc_memW_updW_same mid (lw.toNat + 8) nl_w
      hdr16 := (pmc_memW_updW_ne mid (lw.toNat + 8) (lw.toNat + 16) nl_w (by omega) (by omega)
        (by omega)).trans hm16
      hdr_words := pmc_wordsOK_updW mid (BitVec.ofNat 64 (lw.toNat + 8)) nl_w (lw.toNat, 24)
        hhdr_words
      arr_words := pmc_wordsOK_updW mid (BitVec.ofNat 64 (lw.toNat + 8)) nl_w
        (lw.toNat + 24, 8 * capw.toNat) harr_words
      ents := fun j hj => absurd hj (by omega)
      rcpt_cur := hrc_post }
  -- ===== 8. the setup and the (empty) loop =====
  refine p4Q8_tailSetup (.seq (.while p4Loop38Cond p4Loop38Body) tail) hnl_mid hlocm
    hhdr_words (by omega) hw0' ?_
  exact p4Q8_loop38_empty (p4Q8_lookup_setVar_same _ _ _)
    ((hlu (ofString "nl") (by decide) (by decide)).trans hnl_mid) hnl0
    (htail lw capw _ hExit)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
