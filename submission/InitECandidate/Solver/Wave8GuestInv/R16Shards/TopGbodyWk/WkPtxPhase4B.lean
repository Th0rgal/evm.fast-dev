import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4A

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

/-! # Phase 4 step engines (`WkPtxPhase4B`)

Generic transport lemmas shared by every phase-4 instruction: `Q`/`R`
congruence for `WorldStep`, a cell-level replacement for
`PtxBlockOutUnhit` (needed for `lst_push`, whose writes land inside
`blockOutObjects` arrays), and the resulting `P4Data` step engine. -/

/-! ## `Q`- and `R`-congruence for `WorldStep` -/

theorem worldStep_noExtra {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {post : PanSemStateFiniteExact 64 F}
    (h : WorldStep R gw keep Q s r post) :
    WorldStep R gw keep NoExtra s r post := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro S Nd hWT hD
  obtain ⟨S', Nd', hsub, hW', hOG, hFO, _⟩ := h5 S Nd hWT hD
  exact ⟨S', Nd', hsub, hW', hOG, hFO, trivial⟩

theorem worldStepScBo_noExtra {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {post : PanSemStateFiniteExact 64 F}
    (h : WorldStepScBo R gw keep Q s r post) :
    WorldStepScBo R gw keep NoExtra s r post :=
  ⟨⟨worldStep_noExtra h.1.1, h.1.2⟩, h.2⟩

theorem worldStep_congr_R {F : Type}
    {R R' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {post : PanSemStateFiniteExact 64 F}
    (hRs : R s = R' s)
    (h : WorldStep R gw keep Q s r post) :
    WorldStep R' gw keep Q s r post := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro rec hr hn off hoff hno
    refine h4 rec hr hn off hoff ?_
    intro i hi
    have hiR : i ∈ R s := hi
    rw [hRs] at hiR
    exact hno i hiR
  · intro S Nd hWT hD
    have hD2 : IvlsDisj (R' s) (worldTypedIvls s S Nd) := hD
    rw [← hRs] at hD2
    obtain ⟨S', Nd', hsub, hW', hOG, hFO, hQ⟩ := h5 S Nd hWT hD2
    refine ⟨S', Nd', hsub, hW', hOG, ?_, hQ⟩
    have hFO2 : FrameOutside s post (worldOwned s S Nd ++ R s ++ [freeGap s]) (heapFree s) := hFO
    rw [hRs] at hFO2
    exact hFO2

theorem worldStepScBo_congr_R {F : Type}
    {R R' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {post : PanSemStateFiniteExact 64 F}
    (hRs : R s = R' s)
    (h : WorldStepScBo R gw keep Q s r post) :
    WorldStepScBo R' gw keep Q s r post :=
  ⟨⟨worldStep_congr_R hRs h.1.1, h.1.2⟩, h.2⟩

/-! ## Cell-level block-out facts -/

/-- The block-out facts `PtxRelBase` needs after a step, stated cell by cell
instead of via `PtxBlockOutUnhit`.  This is what survives an `lst_push`
step, whose writes land inside `blockOutObjects` arrays. -/
structure PtxBoCells {F : Type} (txDone : Bool)
    (entry s post : PanSemStateFiniteExact 64 F) : Prop where
  bo_eq : globN post "bo" = globN s "bo"
  rcpt_backing : memW post (memW post (globN post "bo" + 72)) ≠ 0
  log_backing : memW post (memW post (globN post "bo" + 40)) ≠ 0
  rcpt_len_eq : memW post (memW post (globN post "bo" + 72) + 8) =
    memW s (memW s (globN s "bo" + 72) + 8)
  slices_prev : ∀ off ∈ ([24, 32] : List Nat), ∀ i < locN entry "index",
    memW post (memW post (globN post "bo" + off) + 16 * i + 8) =
      memW s (memW s (globN s "bo" + off) + 16 * i + 8)
  tx_slice_cur : txDone = true →
    memW post (memW post (globN post "bo" + 24) + 16 * locN entry "index" + 8) < 2 ^ 40

theorem ptxBoCells_of_blockOutUnhit {F : Type} {txDone : Bool}
    {entry s post : PanSemStateFiniteExact 64 F} {B : BufList}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : PtxRelBase txDone entry s)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hkeep : PtxKeepSub keep)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hbo_keep : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (hstep : WorldStep (bufRegions B) gw keep Q s r post)
    (hbo_unhit : PtxBlockOutUnhit s post) :
    PtxBoCells txDone entry s post := by
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hstep.2.2.1 _ hbo_gw)
  have hbo_s_entry : globN s "bo" = globN entry "bo" :=
    globN_eq_of_lookup (h.globals (ofString "bo") (by decide))
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e, S_e, Nd_e, hWT_e, _⟩ :=
    h.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  have hbo_nz_s : globN s "bo" ≠ 0 := by rw [hbo_s_entry]; exact hbo_nz_e
  obtain ⟨Sc, Nc, _, hWT_w, _, _⟩ := h.typing S_e Nd_e hWT_e hD_e
  have hbo_field_s : ∀ off ∈ ([24, 32, 40, 72, 80] : List Nat),
      off % 8 = 0 → off + 8 ≤ 88 → memW post (globN s "bo" + off) = memW s (globN s "bo" + off) := by
    intro off hoff hoff8 hlt
    rcases hbo_keep with hk1 | hk2
    · exact ptx_bo_field_eq_of_step hB hWT_w hstep.2.2.2.1 hk1 hbo_nz_s
        (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢;
            rcases hoff with rfl | rfl | rfl | rfl | rfl <;> simp) hoff8 hlt
    · exact ptx_bo_field_eq_of_step hB hWT_w hstep.2.2.2.1 hk2 hbo_nz_s
        (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢;
            rcases hoff with rfl | rfl | rfl | rfl | rfl <;> simp) hoff8 hlt
  have hbo24_s : memW s (globN s "bo" + 24) = memW entry (globN entry "bo" + 24) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo32_s : memW s (globN s "bo" + 32) = memW entry (globN entry "bo" + 32) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo40_s : memW s (globN s "bo" + 40) = memW entry (globN entry "bo" + 40) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo72_s : memW s (globN s "bo" + 72) = memW entry (globN entry "bo" + 72) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo80_s : memW s (globN s "bo" + 80) = memW entry (globN entry "bo" + 80) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo40_nz_s : memW s (globN s "bo" + 40) ≠ 0 := by rw [hbo40_s]; exact hbo40_nz_e
  have hbo72_nz_s : memW s (globN s "bo" + 72) ≠ 0 := by rw [hbo72_s]; exact hbo72_nz_e
  have hbo40_post : memW post (globN post "bo" + 40) = memW s (globN s "bo" + 40) := by
    rw [hbo_eq]; exact hbo_field_s 40 (by simp) (by decide) (by omega)
  have hbo72_post : memW post (globN post "bo" + 72) = memW s (globN s "bo" + 72) := by
    rw [hbo_eq]; exact hbo_field_s 72 (by simp) (by decide) (by omega)
  have hlog_hdr0 : memW post (memW post (globN post "bo" + 40)) =
      memW s (memW s (globN s "bo" + 40)) := by
    rw [hbo40_post]
    have hm : (memW s (globN s "bo" + 40), 24) ∈ blockOutObjects s := by
      simp [blockOutObjects, hbo_nz_s, hbo40_nz_s]
    simpa using memW_eq_of_ptxBlockOutUnhit h.world.1 hWT_w hbo_unhit hm (off := 0) (by decide) (by decide)
  have hrcpt_hdr0 : memW post (memW post (globN post "bo" + 72)) =
      memW s (memW s (globN s "bo" + 72)) := by
    rw [hbo72_post]
    simpa using ptx_receipt_header_eq_of_blockOutUnhit h.world.1 hWT_w hbo_unhit hbo_nz_s hbo72_nz_s (off := 0) (by simp)
  have hrcpt_hdr8 : memW post (memW post (globN post "bo" + 72) + 8) =
      memW s (memW s (globN s "bo" + 72) + 8) := by
    rw [hbo72_post]
    exact ptx_receipt_header_eq_of_blockOutUnhit h.world.1 hWT_w hbo_unhit hbo_nz_s hbo72_nz_s (by simp)
  have hsl_eq : ∀ off ∈ ([24, 32] : List Nat), ∀ k, k ≤ locN entry "index" →
      memW post (memW post (globN post "bo" + off) + 16 * k + 8) =
        memW s (memW s (globN s "bo" + off) + 16 * k + 8) := by
    intro off hoff k hk
    have hoff_in : off ∈ ([24, 32, 40, 72, 80] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl <;> simp
    have hbo_off_eq : memW post (globN post "bo" + off) = memW s (globN s "bo" + off) := by
      rw [hbo_eq]
      apply hbo_field_s off hoff_in
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl <;> decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl <;> omega
    rw [hbo_off_eq]
    have hp_nz : memW s (globN s "bo" + off) ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl
      · rw [hbo24_s]; exact hbo24_nz_e
      · rw [hbo32_s]; exact hbo32_nz_e
    apply ptx_slice_length_eq_of_blockOutUnhit h.world.1 hWT_w hbo_unhit hbo_nz_s hoff hp_nz
    rw [hbo80_s]; omega
  refine ⟨hbo_eq, by rw [hrcpt_hdr0]; exact h.rcpt_backing,
    by rw [hlog_hdr0]; exact h.log_backing, hrcpt_hdr8,
    fun off hoff k hk => hsl_eq off hoff k (Nat.le_of_lt hk), ?_⟩
  intro ht
  rw [hsl_eq 24 (by simp) (locN entry "index") le_rfl]
  exact h.tx_slice_cur ht

/-! ## The `PtxRelBase` cells step -/

theorem ptxRelBase_step_cells {F : Type} {txDone : Bool}
    {entry s post : PanSemStateFiniteExact 64 F} {B : BufList}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : PtxRelBase txDone entry s)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hkeep : PtxKeepSub keep)
    (hstep : WorldStep (bufRegions B) gw keep Q s r post)
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hfmp : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (hcells : PtxBoCells txDone entry s post) :
    PtxRelBase txDone entry post := by
  have hws_entry := ptxRelBase_step_worldStep h hB hBsub hgw hkeep hstep
  obtain ⟨⟨_, hbo_nz_e, _, _, _⟩, _, _, _, S_e, Nd_e, hWT_e, _⟩ := h.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨Sc, Nc, _, hWT_w, _, _⟩ := h.typing S_e Nd_e hWT_e hD_e
  obtain ⟨S_wp, Nd_wp, _, hWT_wp, _, _, _⟩ :=
    hstep.2.2.2.2 Sc Nc hWT_w (validBufList_disj hB hWT_w)
  have hworld_post : WorldOK post :=
    ⟨hstep.1, S_wp, (worldTyped_iff_with post S_wp).2 ⟨Nd_wp, hWT_wp⟩⟩
  refine ⟨h.ready_entry, h.arena_entry, le_trans h.frame_entry hfmp,
    le_trans hsp h.scratch_entry, hworld_post, hws_entry.2.1, hws_entry.2.2.1,
    hws_entry.2.2.2.1, hcells.rcpt_backing, hcells.log_backing,
    hcells.rcpt_len_eq.trans h.rcpt_len_eq,
    fun off hoff k hk => (hcells.slices_prev off hoff k hk).trans
      (h.slices_prev off hoff k hk),
    hcells.tx_slice_cur, ?_⟩
  intro S0 Nd0 hWT0 hD0
  obtain ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn, _⟩ := hws_entry.2.2.2.2 S0 Nd0 hWT0 hD0
  exact ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn⟩

/-! ## The `P4Data` cells engine -/

/-- Transport `P4Data` across any step given as a `WorldStep` at `s` plus
cell-level block-out facts.  The caller frame is restored (locals of `s`,
clock of the step's exit). -/
theorem p4Data_step_of_worldStep_cells {F : Type}
    {entry s s_pmc post : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : P4Data entry s s_pmc w_out)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hsys_gw : ofString "vm_system_address" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hstep : WorldStep (bufRegions B) gw keep Q s r post)
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hcells : PtxBoCells true entry s post) :
    P4Data entry {post with locals := s.locals, clock := post.clock} s_pmc w_out := by
  have hfmp : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" :=
    Nat.le_of_eq (globN_eq_of_lookup (hstep.2.2.1 _ hfmp_gw)).symm
  have hsys : globN post "vm_system_address" = globN s "vm_system_address" :=
    globN_eq_of_lookup (hstep.2.2.1 _ hsys_gw)
  have hgrow : AllocatorGrows s post := ⟨hstep.2.1, hsp⟩
  have hAs : ArenaOK s := h.base.world.1.2
  have hAp : ArenaOK post := hstep.1.2
  have hgS : GuestInv s := h.base.world.1.1
  have hgP : GuestInv post := hstep.1.1
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e, S_e, Nd_e, hWT_e, _⟩ :=
    h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := h.logs_facts
  obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8, hty9⟩ :=
    hty S_e Nd_e hWT_e hD_e
  obtain ⟨S_n, N_n, hsub_n, hWT_n, hOG_n, hFO_n, hQ_n⟩ :=
    hstep.2.2.2.2 S_cur Nd_cur hWT_s (validBufList_disj hB hWT_s)
  have hold0 : ∀ j ∈ worldOwned s S_cur Nd_cur, j.2 = 0 → j.1 % 8 = 0 :=
    R13Shards.worldOwned_zero_aligned hWT_s
  have hR0 : ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 :=
    ptx_bufRegions_zero_aligned hB hWT_s.2.2.1
  have hout_u : R13Shards.IvlUnhit s post (w_out.toNat, 96) :=
    (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0 hR0 hOG_n hFO_n
      h.out_words.1 h.out_words.2.1 h.out_inside hty7
      (ptx_disj_bufRegions_of_disj_worldOwned hB hty7)).2.2
  have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (R13Shards.ivl_allocated_bound hAs (Or.inl h.out_inside)).2
  have hout_mem : ∀ off ∈ ([80, 88] : List Nat),
      memW post (w_out.toNat + off) = memW s (w_out.toNat + off) := by
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl
    · apply R13Shards.memW_eq_of_ivlUnhit hout_u
      · have := h.out_words.1; omega
      · exact hout_hi
      · constructor <;> omega
    · apply R13Shards.memW_eq_of_ivlUnhit hout_u
      · have := h.out_words.1; omega
      · exact hout_hi
      · constructor <;> omega
  have hout_list : memW post (w_out.toNat + 16) = memW s (w_out.toNat + 16) := by
    apply R13Shards.memW_eq_of_ivlUnhit hout_u
    · have := h.out_words.1; omega
    · exact hout_hi
    · constructor <;> omega
  have hout_list_surv : memW s (w_out.toNat + 16) ≠ 0 →
      LogsListOK post (memW s (w_out.toNat + 16)) ∧
      PmcLogsLiveOwned post S_n N_n (memW s (w_out.toNat + 16)) := by
    intro hnz
    obtain ⟨hRh, hRa, hRe⟩ := pmcLogs_bufDisj hB hty8 hnz
    exact ⟨PtxP34.logsLiveOwned_list_survives hAs hAp hgS hgP hgrow h.logs_ok hty8
      hold0 hR0 hOG_n hFO_n hRh hRa hRe,
      PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow h.logs_ok hty8 hsys
      hold0 hR0 hOG_n hFO_n hRh hRa hRe⟩
  have hlogs_surv : logs ≠ 0 → LogsListOK post logs ∧ PmcLogsLiveOwned post S_n N_n logs := by
    intro hnz
    obtain ⟨hRh, hRa, hRe⟩ := pmcLogs_bufDisj hB hty9 hnz
    exact ⟨PtxP34.logsLiveOwned_list_survives hAs hAp hgS hgP hgrow hl_ok hty9
      hold0 hR0 hOG_n hFO_n hRh hRa hRe,
      PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow hl_ok hty9 hsys
      hold0 hR0 hOG_n hFO_n hRh hRa hRe⟩
  refine ⟨ptxRelBase_with_locals
      (ptxRelBase_step_cells h.base hB hBsub hgw hkeep hstep hsp hfmp hcells) s.locals post.clock,
    h.arena_pmc, le_trans h.heap_pmc hstep.2.1, h.out_local,
    R13Shards.wordsOK_transfer hgS hgP h.out_words,
    (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0 hR0 hOG_n hFO_n
      h.out_words.1 h.out_words.2.1 h.out_inside hty7
      (ptx_disj_bufRegions_of_disj_worldOwned hB hty7)).1,
    ?_, ?_, h.shapes, h.tx_local, h.idx_local, ?_⟩
  · intro h80_nz
    have h80_nz' : memW s (w_out.toNat + 80) ≠ 0 := by
      rw [← hout_mem 80 (by simp)]; exact h80_nz
    obtain ⟨h80_8, h88_8, h88_le, h80_8b, h80_sc⟩ := h.marks h80_nz'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show memW post (w_out.toNat + 80) % 8 = 0
      rw [hout_mem 80 (by simp)]; exact h80_8
    · show memW post (w_out.toNat + 88) % 8 = 0
      rw [hout_mem 88 (by simp)]; exact h88_8
    · show globN s_pmc "frame_mem_ptr" ≤ memW post (w_out.toNat + 88)
      rw [hout_mem 88 (by simp)]; exact h88_le
    · show memW post (w_out.toNat + 88) ≤ memW post (w_out.toNat + 80)
      rw [hout_mem 88 (by simp), hout_mem 80 (by simp)]; exact h80_8b
    · show memW post (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr"
      rw [hout_mem 80 (by simp)]; exact h80_sc
  · show LogsListOK post (memW post (w_out.toNat + 16))
    rw [hout_list]
    by_cases hnz : memW s (w_out.toNat + 16) = 0
    · rw [hnz]; exact Or.inl rfl
    · exact (hout_list_surv hnz).1
  · refine ⟨logs, ?_, ?_, ?_, ?_⟩
    · rcases hll with hll | hll
      · exact Or.inl hll
      · exact Or.inr hll
    · by_cases hnz : logs = 0
      · exact Or.inl hnz
      · have h1 := (hlogs_surv hnz).1
        exact (R13Shards.logsListOK_with_locals post s.locals post.clock logs).2 h1
    · by_cases hnz : logs = 0
      · exact Or.inl hnz
      · exact pmcLogsLiveOwned_disjFixed (hlogs_surv hnz).2
    · intro S0 Nd0 hWT0 hD0
      obtain ⟨S_pmc', Nd_pmc', S_cur', Nd_cur', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        hty S0 Nd0 hWT0 hD0
      obtain ⟨S_n', N_n', hsub', hWT_n', hOG_n', hFO_n', hQ_n'⟩ :=
        hstep.2.2.2.2 S_cur' Nd_cur' h3 (validBufList_disj hB h3)
      have hold0' : ∀ j ∈ worldOwned s S_cur' Nd_cur', j.2 = 0 → j.1 % 8 = 0 :=
        R13Shards.worldOwned_zero_aligned h3
      have hR0' : ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 :=
        ptx_bufRegions_zero_aligned hB h3.2.2.1
      have hout_u' : R13Shards.IvlUnhit s post (w_out.toNat, 96) :=
        (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0' hR0' hOG_n' hFO_n'
          h.out_words.1 h.out_words.2.1 h.out_inside h7
          (ptx_disj_bufRegions_of_disj_worldOwned hB h7)).2.2
      have hout_list' : memW post (w_out.toNat + 16) = memW s (w_out.toNat + 16) := by
        apply R13Shards.memW_eq_of_ivlUnhit hout_u'
        · have := h.out_words.1; omega
        · exact hout_hi
        · constructor <;> omega
      have hout_list_surv' : memW s (w_out.toNat + 16) ≠ 0 →
          PmcLogsLiveOwned post S_n' N_n' (memW s (w_out.toNat + 16)) := by
        intro hnz
        obtain ⟨hRh, hRa, hRe⟩ := pmcLogs_bufDisj hB h8 hnz
        exact PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow h.logs_ok h8 hsys
          hold0' hR0' hOG_n' hFO_n' hRh hRa hRe
      have hlogs_surv' : logs ≠ 0 → PmcLogsLiveOwned post S_n' N_n' logs := by
        intro hnz
        obtain ⟨hRh, hRa, hRe⟩ := pmcLogs_bufDisj hB h9 hnz
        exact PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow hl_ok h9 hsys
          hold0' hR0' hOG_n' hFO_n' hRh hRa hRe
      refine ⟨S_pmc', Nd_pmc', S_n', N_n', h1, fun t ht => hsub' t (h2 t ht),
        (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post s.locals post.clock S_n' N_n').2 hWT_n',
        ptx_ownedGrows_trans h.heap_pmc hstep.2.1 h4 hOG_n',
        ptx_ownedGrows_trans h.base.heap_entry hstep.2.1 h5 hOG_n',
        ptx_frameOutside_trans h.base.arena_entry ⟨hgS, hAs⟩ h.base.heap_entry h.base.frame_entry
          h.base.scratch_entry h5 (ptxBufs_sub_entry h.base.globals hBsub) h6 hFO_n',
        (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0' hR0' hOG_n' hFO_n'
          h.out_words.1 h.out_words.2.1 h.out_inside h7
          (ptx_disj_bufRegions_of_disj_worldOwned hB h7)).2.1, ?_, ?_⟩
      · show PmcLogsLiveOwned post S_n' N_n' (memW post (w_out.toNat + 16))
        rw [hout_list']
        by_cases hnz : memW s (w_out.toNat + 16) = 0
        · rw [hnz]; exact pmcLogsLiveOwned_zero _ _ _
        · exact hout_list_surv' hnz
      · show PmcLogsLiveOwned post S_n' N_n' logs
        by_cases hnz : logs = 0
        · rw [hnz]; exact pmcLogsLiveOwned_zero _ _ _
        · exact hlogs_surv' hnz

/-! ## Run-level combinators -/

theorem p4RelRunStrong_skip {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (htail : PtxRelRunStrong entry tail s) :
    PtxRelRunStrong entry (.seq .skip tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hres ⊢
  exact htail hres

/-- `dec` step: the caller supplies the `P4Data` restore for the
variable's new value and the continuation. -/
theorem p4Run_dec {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (name : MlS) (sh : ShapeHOL) (e : ExpHOL 64) (tail : ProgHOL 64)
    (htail : ∀ v : ValueHOL 64,
      evalAt s e = some v → shapeOfHOLExact v = sh →
      PtxRelRunStrong entry tail (setVarHOLFinite name v s)) :
    PtxRelRunStrong entry (.dec name sh e tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hev] at hres ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hres ⊢
      have hsh_eq : shapeOfHOLExact v = sh :=
        (shapeEqHOL_eq_true sh (shapeOfHOLExact v)).1 hsh |>.symm
      have hmid := htail v hev hsh_eq hres
      exact ptxWorldStep_strong_with_locals_right'
        (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState (setVarHOLFinite name v s) tail).2.locals
          (name, s.locals.lookup name))
        (evaluateHOLFiniteState (setVarHOLFinite name v s) tail).2.clock hmid
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-- `assign` step (local kind): the validity test is case-split; the
invalid branch makes the program error out, contradicting `Resumes`. -/
theorem p4Run_assign {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (name : MlS) (e : ExpHOL 64) (tail : ProgHOL 64)
    (htail : ∀ v : ValueHOL 64,
      evalAt s e = some v →
      PtxRelRunStrong entry tail (setVarHOLFinite name v s)) :
    PtxRelRunStrong entry (.seq (.assign .local name e) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hres ⊢
  dsimp only at hres ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [hev] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hev] at hres ⊢
    by_cases hvalid : isValidValueHOLFinite s .local name v = true
    · simp only [hvalid, ↓reduceIte] at hres ⊢
      exact htail v hev hres
    · simp only [hvalid, Bool.false_eq_true, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-- `ite` step. -/
theorem p4Run_ite {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (cond : ExpHOL 64) (bt bf : ProgHOL 64) (tail : ProgHOL 64)
    (ht : PtxRelRunStrong entry (.seq bt tail) s)
    (hf : PtxRelRunStrong entry (.seq bf tail) s) :
    PtxRelRunStrong entry (.seq (.ite cond bt bf) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
  dsimp only at hres ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | v
  · simp [hev] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · cases hv : v with
    | val w =>
      cases hw : w with
      | word b =>
        simp only [hev, hv, hw] at hres ⊢
        by_cases hb : b = (0 : BitVec 64)
        · simp only [hb, ↓reduceIte] at hres ⊢
          have hf'un : Resumes (evaluateHOLFiniteState s (ProgHOL.seq bf tail)).1 →
              WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry
                (evaluateHOLFiniteState s (ProgHOL.seq bf tail)).1
                (evaluateHOLFiniteState s (ProgHOL.seq bf tail)).2 := hf
          rw [evaluateHOLFiniteState_seq_line780] at hf'un
          dsimp only at hf'un
          exact hf'un hres
        · simp only [hb, ↓reduceIte] at hres ⊢
          have ht'un : Resumes (evaluateHOLFiniteState s (ProgHOL.seq bt tail)).1 →
              WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry
                (evaluateHOLFiniteState s (ProgHOL.seq bt tail)).1
                (evaluateHOLFiniteState s (ProgHOL.seq bt tail)).2 := ht
          rw [evaluateHOLFiniteState_seq_line780] at ht'un
          dsimp only at ht'un
          exact ht'un hres
    | rStruct _ | nStruct _ _ =>
      simp [hev, hv] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-! ### The generic scBo `decCall` runner -/

theorem p4Run_decCall_scBo {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hsys_gw : ofString "vm_system_address" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (name : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hwk : WorldKeepsScBo P (bufRegions B) gw keep Q fname)
    (hPent : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      P (callEntryStateHOLFinite s callee))
    (hnout : name ≠ ofString "out") (hntx : name ≠ ofString "tx")
    (hnidx : name ≠ ofString "index") (hnlogs : name ≠ ofString "logs")
    (hshn : ∀ nm ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] : List String), ofString nm ≠ name)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      shapeOfHOLExact v = sh →
      P4Data entry (setVarHOLFinite name v { post with locals := s.locals }) s_pmc w_out →
      post.code = originalRuntimeCode →
      PtxRelRunStrong entry tail (setVarHOLFinite name v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall name sh fname args tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    have ha_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs := by
      simpa [evalListHOLFinite] using ha
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (rb, post) := hb
        rw [hb] at hmeta
        simp only [hb] at hres ⊢
        cases rb with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr =>
          cases cr with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hspec := hwk.at_lookup s hc vs body callee ret hl (hPent callee)
              (by rw [hb']; simp)
            rw [hb'] at hspec
            have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.exception eid ev)) post :=
              R13Shards.worldStep_with_locals (hspec hres).1.1 s.locals s.clock
            have hex := ptxRelBase_exception_worldStep h.base hB hBsub hgw hkeep hstep_s
            exact ptxWorldStep_strong_with_locals_right' .empty post.clock hex
          | returned v =>
            dsimp only at hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret) = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact v) sh = true := ((Bool.and_eq_true _ _).mp hsh).1
              have hsh_eq : shapeOfHOLExact v = sh := (shapeEqHOL_eq_true _ _).1 hsh1
              have hspec := hwk.at_lookup s hc vs body callee ret hl (hPent callee)
                (by rw [hb']; simp)
              rw [hb'] at hspec
              have hscbo := hspec (Or.inl ⟨v, rfl⟩)
              have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.returned v)) post :=
                R13Shards.worldStep_with_locals hscbo.1.1 s.locals s.clock
              have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                globN_eq_of_lookup (hstep_s.2.2.1 _ hfmp_gw)
              have hfmp : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" :=
                Nat.le_of_eq hfmp_eq.symm
              have hcells : PtxBoCells true entry s post :=
                ptxBoCells_of_blockOutUnhit h.base hB hBsub hgw hkeep hbo_gw hbo_keep hstep_s
                  (hscbo.2 (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))))
              have hdata_post : P4Data entry { post with locals := s.locals, clock := post.clock } s_pmc w_out :=
                p4Data_step_of_worldStep_cells h hB hBsub hgw hfmp_gw hsys_gw hkeep
                  hstep_s hscbo.1.2 hcells
              have hdata_res : P4Data entry
                  (setVarHOLFinite name v { post with locals := s.locals }) s_pmc w_out :=
                p4Data_setVar hnout hntx hnidx hnlogs hshn hdata_post
              have hmid := htail vs body callee ret v post ha_fin hl hb' hsh_eq hdata_res
                (hmeta.trans hc) hres
              exact ptxWorldStep_strong_with_locals_right'
                (HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) tail).2.locals
                  (name, s.locals.lookup name))
                (evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) tail).2.clock hmid
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-! ### The generic scBo `call` runners -/

theorem p4Run_call0_scBo {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hsys_gw : ofString "vm_system_address" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hwk : WorldKeepsScBo P (bufRegions B) gw keep Q fname)
    (hPent : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      P (callEntryStateHOLFinite s callee))
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      WorldStep (bufRegions B) gw keep Q (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      P4Data entry { post with locals := s.locals } s_pmc w_out →
      post.code = originalRuntimeCode →
      PtxRelRunStrong entry tail { post with locals := s.locals }) :
    PtxRelRunStrong entry (.seq (.call (some (none, none)) fname args) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    have ha_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs := by
      simpa [evalListHOLFinite] using ha
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (rb, post) := hb
        rw [hb] at hmeta
        simp only [hb] at hres ⊢
        cases rb with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr =>
          cases cr with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hspec := hwk.at_lookup s hc vs body callee ret hl (hPent callee)
              (by rw [hb']; simp)
            rw [hb'] at hspec
            have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.exception eid ev)) post :=
              R13Shards.worldStep_with_locals (hspec hres).1.1 s.locals s.clock
            have hex := ptxRelBase_exception_worldStep h.base hB hBsub hgw hkeep hstep_s
            exact ptxWorldStep_strong_with_locals_right' .empty post.clock hex
          | returned v =>
            dsimp only at hres ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              have hspec := hwk.at_lookup s hc vs body callee ret hl (hPent callee)
                (by rw [hb']; simp)
              rw [hb'] at hspec
              have hscbo := hspec (Or.inl ⟨v, rfl⟩)
              have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.returned v)) post :=
                R13Shards.worldStep_with_locals hscbo.1.1 s.locals s.clock
              have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                globN_eq_of_lookup (hstep_s.2.2.1 _ hfmp_gw)
              have hfmp : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" :=
                Nat.le_of_eq hfmp_eq.symm
              have hcells : PtxBoCells true entry s post :=
                ptxBoCells_of_blockOutUnhit h.base hB hBsub hgw hkeep hbo_gw hbo_keep hstep_s
                  (hscbo.2 (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))))
              have hdata_post : P4Data entry { post with locals := s.locals, clock := post.clock } s_pmc w_out :=
                p4Data_step_of_worldStep_cells h hB hBsub hgw hfmp_gw hsys_gw hkeep
                  hstep_s hscbo.1.2 hcells
              exact htail vs body callee ret v post ha_fin hl hb' hscbo.1.1 hdata_post
                (hmeta.trans hc) hres
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-! ### The scBo `call` runner with a local result binding -/

theorem p4Run_call_local_scBo {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hsys_gw : ofString "vm_system_address" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (name : MlS) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hwk : WorldKeepsScBo P (bufRegions B) gw keep Q fname)
    (hPent : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      P (callEntryStateHOLFinite s callee))
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      P4Data entry { post with locals := s.locals } s_pmc w_out →
      post.code = originalRuntimeCode →
      PtxRelRunStrong entry tail (setVarHOLFinite name v { post with locals := s.locals })) :
    PtxRelRunStrong entry
      (.seq (.call (some (some (.local, name), none)) fname args) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    have ha_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs := by
      simpa [evalListHOLFinite] using ha
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (rb, post) := hb
        rw [hb] at hmeta
        simp only [hb] at hres ⊢
        cases rb with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr =>
          cases cr with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hspec := hwk.at_lookup s hc vs body callee ret hl (hPent callee)
              (by rw [hb']; simp)
            rw [hb'] at hspec
            have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.exception eid ev)) post :=
              R13Shards.worldStep_with_locals (hspec hres).1.1 s.locals s.clock
            have hex := ptxRelBase_exception_worldStep h.base hB hBsub hgw hkeep hstep_s
            exact ptxWorldStep_strong_with_locals_right' .empty post.clock hex
          | returned v =>
            dsimp only at hres ⊢
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              by_cases hvalid : isValidValueHOLExact s.toExact .local name v = true
              · simp only [hvalid, ↓reduceIte] at hres ⊢
                have hspec := hwk.at_lookup s hc vs body callee ret hl (hPent callee)
                  (by rw [hb']; simp)
                rw [hb'] at hspec
                have hscbo := hspec (Or.inl ⟨v, rfl⟩)
                have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.returned v)) post :=
                  R13Shards.worldStep_with_locals hscbo.1.1 s.locals s.clock
                have hcells : PtxBoCells true entry s post :=
                  ptxBoCells_of_blockOutUnhit h.base hB hBsub hgw hkeep hbo_gw hbo_keep hstep_s
                    (hscbo.2 (Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))))
                have hdata_post : P4Data entry { post with locals := s.locals, clock := post.clock } s_pmc w_out :=
                  p4Data_step_of_worldStep_cells h hB hBsub hgw hfmp_gw hsys_gw hkeep
                    hstep_s hscbo.1.2 hcells
                exact htail vs body callee ret v post ha_fin hl hb' hdata_post
                  (hmeta.trans hc) hres
              · simp only [hvalid, Bool.false_eq_true, ↓reduceIte] at hres
                exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-! ### The `store` runner -/

theorem p4Run_store {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (dst src : ExpHOL 64) (tail : ProgHOL 64)
    (htail : ∀ (a : BitVec 64) (v : ValueHOL 64)
      (mem' : RiscV.Word 64 → HolWordLab 64),
      evalAt s dst = some (.val (.word a)) →
      evalAt s src = some v →
      @panMemStoresHOL 64 _ a (flattenHOL v) s.memaddrs
        (fun address => Classical.propDecidable (s.memaddrs address)) s.memory = some mem' →
      PtxRelRunStrong entry tail { s with memory := mem' }) :
    PtxRelRunStrong entry (.seq (.store dst src) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres ⊢
  dsimp only at hres ⊢
  rcases hed : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · simp [hed] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · cases dv with
      | val w =>
        cases hw : w with
        | word a =>
          rw [hw] at hed
          simp only [hed, hw] at hres ⊢
          rcases hes : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src with _ | v
          · simp [hes] at hres
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          · simp only [hes] at hres ⊢
            rcases hmem : @panMemStoresHOL 64 _ a (flattenHOL v) s.memaddrs (fun address => Classical.propDecidable (s.memaddrs address)) s.memory with _ | mem'
            · simp [hmem] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hmem] at hres ⊢
              exact htail a v mem' hed hes hmem hres
      | rStruct _ | nStruct _ _ =>
        simp [hed] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
