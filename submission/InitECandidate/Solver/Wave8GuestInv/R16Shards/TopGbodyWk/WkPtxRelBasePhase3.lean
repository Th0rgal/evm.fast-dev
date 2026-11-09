import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkEncodeTxBounded
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeReceipt

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

structure PtxRelBase {F : Type} (txDone : Bool)
    (entry s : PanSemStateFiniteExact 64 F) : Prop where
  ready_entry : TxReadyStrong entry
  arena_entry : ArenaReady entry
  frame_entry : globN entry "frame_mem_ptr" ≤ globN s "frame_mem_ptr"
  scratch_entry : globN s "scratch_ptr" ≤ globN entry "scratch_ptr"
  world : WorldOK s
  heap_entry : globN entry "heap_ptr" ≤ globN s "heap_ptr"
  globals : GlobalsKept ptxGlobals entry s
  records : RecordsKept ptxRegions ptxKeep entry s
  rcpt_backing : memW s (memW s (globN s "bo" + 72)) ≠ 0
  log_backing : memW s (memW s (globN s "bo" + 40)) ≠ 0
  rcpt_len_eq : memW s (memW s (globN s "bo" + 72) + 8) =
    memW entry (memW entry (globN entry "bo" + 72) + 8)
  slices_prev : ∀ off ∈ ([24, 32] : List Nat), ∀ i < locN entry "index",
    memW s (memW s (globN s "bo" + off) + 16 * i + 8) =
      memW entry (memW entry (globN entry "bo" + off) + 16 * i + 8)
  tx_slice_cur : txDone = true →
    memW s (memW s (globN s "bo" + 24) + 16 * locN entry "index" + 8) < 2 ^ 40
  typing : ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
    IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
    ∃ S_cur Nd_cur,
      (∀ t ∈ S0, t ∈ S_cur) ∧
      WorldTypedWith s S_cur Nd_cur ∧
      OwnedGrows entry s (worldOwned entry S0 Nd0) (worldOwned s S_cur Nd_cur) ∧
      FrameOutside entry s (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry)

theorem ptxRelBase_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hready : TxReadyStrong s) (hb : TxBacking s) :
    PtxRelBase false s s := by
  refine ⟨hready, hready.1.1.1, le_rfl, le_rfl, hready.1.1, le_rfl,
    fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, hb.2, hb.1, rfl,
    fun _ _ _ _ => rfl, (fun h => by cases h), ?_⟩
  intro S0 Nd0 hWT0 _
  exact ⟨S0, Nd0, fun _ ht => ht, hWT0,
    fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩),
    fun _ _ _ => rfl⟩

theorem ptxRelBase_with_locals {F : Type} {txDone : Bool}
    {entry s : PanSemStateFiniteExact 64 F}
    (h : PtxRelBase txDone entry s)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) :
    PtxRelBase txDone entry { s with locals := L, clock := ck } := by
  refine ⟨h.ready_entry, h.arena_entry, h.frame_entry, h.scratch_entry,
    localsFree_worldOK s L ck h.world, h.heap_entry, h.globals, h.records,
    h.rcpt_backing, h.log_backing, h.rcpt_len_eq, h.slices_prev, h.tx_slice_cur, ?_⟩
  intro S0 Nd0 hWT0 hD0
  obtain ⟨Sc, Nc, hsub, hWc, hOG, hFO⟩ := h.typing S0 Nd0 hWT0 hD0
  exact ⟨Sc, Nc, hsub,
    (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s L ck Sc Nc).2 hWc, hOG, hFO⟩

theorem ptxRelBase_step_worldStep {F : Type} {txDone : Bool}
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
    (hstep : WorldStep (bufRegions B) gw keep Q s r post) :
    WorldStep ptxRegions ptxGlobals ptxKeep NoExtra entry r post := by
  have hRsub := ptxBufs_sub_entry h.globals hBsub
  refine ⟨hstep.1, le_trans h.heap_entry hstep.2.1, ?_, ?_, ?_⟩
  · intro k hk
    have hkg : k ∉ gw.map ofString := by
      intro hm
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
      exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
    exact (h.globals k hk).trans (hstep.2.2.1 k hkg)
  · intro rec hr hn off hoff hno
    obtain ⟨offs, hkr, hko⟩ := hkeep rec hr
    have heq : globN s rec.1 = globN entry rec.1 := by
      have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
        simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · decide
        · decide
        · simp at hoff
        · decide
      exact globN_eq_of_lookup (h.globals (ofString rec.1) hni)
    have hks := hstep.2.2.2.1 (rec.1, offs) hkr (by simpa only [heq] using hn)
      off (hko off hoff) (by
        intro i hi
        simpa only [heq] using hno i (hRsub i hi))
    rw [heq] at hks
    exact hks.trans (h.records rec hr hn off hoff hno)
  · intro S Nd hWT hD
    obtain ⟨Sc, Nc, hsub, hWc, hOG, hFO⟩ := h.typing S Nd hWT hD
    obtain ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn, _⟩ :=
      hstep.2.2.2.2 Sc Nc hWc (validBufList_disj hB hWc)
    refine ⟨Sn, Nn, fun t ht => hsubn t (hsub t ht), hWn,
      ptx_ownedGrows_trans h.heap_entry hstep.2.1 hOG hOGn, ?_, trivial⟩
    exact ptx_frameOutside_trans h.arena_entry h.world.1 h.heap_entry
      h.frame_entry h.scratch_entry hOG hRsub hFO hFOn

theorem ptxRelBase_exception_worldStep {F : Type} {txDone : Bool}
    {entry s post : PanSemStateFiniteExact 64 F} {B : BufList}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {eid : MlS} {v : ValueHOL 64}
    (h : PtxRelBase txDone entry s)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hkeep : PtxKeepSub keep)
    (hstep : WorldStep (bufRegions B) gw keep Q s (some (.exception eid v)) post) :
    WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices
      entry (some (.exception eid v)) post := by
  have hb := ptxRelBase_step_worldStep h hB hBsub hgw hkeep hstep
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
  intro S Nd hWT hD
  obtain ⟨Sn, Nn, hsub, hWn, hOG, hFO, _⟩ := hb.2.2.2.2 S Nd hWT hD
  exact ⟨Sn, Nn, hsub, hWn, hOG, hFO,
    (by intro val hv; cases hv), (by intro val hv; cases hv)⟩

theorem ptxRelBase_step_of_blockOutUnhit {F : Type} {txDone : Bool}
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
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hfmp : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (hbo_unhit : PtxBlockOutUnhit s post) :
    PtxRelBase txDone entry post := by
  have hws_entry := ptxRelBase_step_worldStep h hB hBsub hgw hkeep hstep
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
  obtain ⟨S_wp, Nd_wp, _, hWT_wp, _, _, _⟩ :=
    hstep.2.2.2.2 Sc Nc hWT_w (validBufList_disj hB hWT_w)
  have hworld_post : WorldOK post :=
    ⟨hstep.1, S_wp, (worldTyped_iff_with post S_wp).2 ⟨Nd_wp, hWT_wp⟩⟩
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
  refine ⟨h.ready_entry, h.arena_entry, le_trans h.frame_entry hfmp, le_trans hsp h.scratch_entry,
    hworld_post, hws_entry.2.1, hws_entry.2.2.1, hws_entry.2.2.2.1,
    by rw [hrcpt_hdr0]; exact h.rcpt_backing,
    by rw [hlog_hdr0]; exact h.log_backing,
    hrcpt_hdr8.trans h.rcpt_len_eq,
    fun off hoff k hk => (hsl_eq off hoff k (Nat.le_of_lt hk)).trans (h.slices_prev off hoff k hk),
    fun ht => by rw [hsl_eq 24 (by simp) (locN entry "index") le_rfl]; exact h.tx_slice_cur ht,
    ?_⟩
  intro S0 Nd0 hWT0 hD0
  obtain ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn, _⟩ := hws_entry.2.2.2.2 S0 Nd0 hWT0 hD0
  exact ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn⟩



def RetMessageOutputMarksBo : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd =>
    RetMessageOutputMarks s r post S Nd ∧ (NonExResult r → PtxBlockOutUnhit s post)

def PmcMarksBoStrong : Prop :=
  WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
    RetMessageOutputMarksBo (ofString "process_message_call")

def PtxAfterPhase2 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  let s_msg := setVarHOLFinite (ofString "msg") (.val (.word (BitVec.ofNat 64 (locN s "m")))) s
  PtxRelBase true entry s ∧
  globN s "bn_expw" = globN entry "bn_expw" ∧
  globN s "bn_gamma" = globN entry "bn_gamma" ∧
  Inside (locN s "m", 176) (globN entry "heap_ptr") (globN s "heap_ptr") ∧
  R13Shards.PtxMessageReady s ∧
  PtxPhase4LocalShapes s ∧
  s.locals.lookup (ofString "tx") = entry.locals.lookup (ofString "tx") ∧
  s.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index") ∧
  (∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
    IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
    ∃ Sc Nc,
      (∀ t ∈ S0, t ∈ Sc) ∧
      R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s_msg Sc Nc ∧
      OwnedGrows entry s (worldOwned entry S0 Nd0) (worldOwned s Sc Nc) ∧
      FrameOutside entry s (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry))

structure PtxAfterPhase3Data {F : Type}
    (entry s s_pmc : PanSemStateFiniteExact 64 F) (w_out : BitVec 64) : Prop where
  base : PtxRelBase true entry s
  arena_pmc : ArenaReady s_pmc
  heap_pmc : globN s_pmc "heap_ptr" ≤ globN s "heap_ptr"
  out_local : s.locals.lookup (ofString "out") = some (.val (.word w_out))
  out_words : WordsOK s (w_out.toNat, 96)
  out_inside : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr")
  marks : memW s (w_out.toNat + 80) ≠ 0 →
    memW s (w_out.toNat + 80) % 8 = 0 ∧
    memW s (w_out.toNat + 88) % 8 = 0 ∧
    globN s_pmc "frame_mem_ptr" ≤ memW s (w_out.toNat + 88) ∧
    memW s (w_out.toNat + 88) ≤ memW s (w_out.toNat + 80) ∧
    memW s (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr"
  logs_ok : LogsListOK s (memW s (w_out.toNat + 16))
  shapes : PtxPhase4LocalShapes s
  tx_local : s.locals.lookup (ofString "tx") = entry.locals.lookup (ofString "tx")
  idx_local : s.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index")
  typing3 : ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
    IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
    ∃ S_pmc Nd_pmc S_cur Nd_cur,
      WorldTypedWith s_pmc S_pmc Nd_pmc ∧
      (∀ t ∈ S0, t ∈ S_cur) ∧
      WorldTypedWith s S_cur Nd_cur ∧
      OwnedGrows s_pmc s (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s S_cur Nd_cur) ∧
      OwnedGrows entry s (worldOwned entry S0 Nd0) (worldOwned s S_cur Nd_cur) ∧
      FrameOutside entry s (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) ∧
      (∀ o ∈ worldOwned s S_cur Nd_cur, Disj (w_out.toNat, 96) o) ∧
      PmcLogsLiveOwned s S_cur Nd_cur (memW s (w_out.toNat + 16))

def PtxAfterPhase3 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ s_pmc w_out, PtxAfterPhase3Data entry s s_pmc w_out

theorem pmcBufs_sub_ptx : ∀ p ∈ pmcBufs, p ∈ ptxBufs := by
  intro p hp
  simp only [pmcBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ptxBufs]

theorem pmcGlobals_sub_ptx : ∀ g ∈ pmcGlobals, g ∈ ptxGlobals := by
  intro g hg
  simp only [pmcGlobals, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ptxKeepSub_pmcKeep : PtxKeepSub pmcKeep := by
  intro rec hrec
  simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
  rcases hrec with rfl | rfl | rfl | rfl
  · exact ⟨[0, 8, 16, 24, 32], by simp [pmcKeep], fun _ h => h⟩
  · refine ⟨[0, 8, 16, 24, 32, 40, 48, 72], by simp [pmcKeep], ?_⟩
    intro off hoff; simp at hoff ⊢; omega
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64], by simp [pmcKeep], fun _ h => False.elim (by simp at h)⟩
  · refine ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp [pmcKeep], ?_⟩
    intro off hoff; simp at hoff ⊢; omega

theorem pmcBufs_sub_entry_of_bn {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (hG : GlobalsKept ptxGlobals entry s)
    (hexpw : globN s "bn_expw" = globN entry "bn_expw")
    (hgamma : globN s "bn_gamma" = globN entry "bn_gamma") :
    ∀ i ∈ bufRegions pmcBufs s, i ∈ ptxRegions entry := by
  rw [ptxRegions_eq_bufRegions]
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
  have hptx : p ∈ ptxBufs := pmcBufs_sub_ptx p hp
  have hgeq : globN s p.1 = globN entry p.1 := by
    simp only [pmcBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact globN_eq_of_lookup (hG (ofString "b2_v") (by decide))
    · exact hexpw
    · exact hgamma
    · exact globN_eq_of_lookup (hG (ofString "evm_key_buf") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "keccak_pad") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "keccak_st") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "mpt_nib_scratch") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "pre_hdr_buf") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "rmd_h") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "rmd_pad") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "rmd_x") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "sha_pad") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "sha_st") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "sk_buf") (by decide))
    · exact globN_eq_of_lookup (hG (ofString "u256_ws") (by decide))
  refine List.mem_map.2 ⟨p, hptx, ?_⟩
  simp only [bufferRegion, hgeq]

theorem ptx_frameOutside_trans_msg {F : Type}
    {entry s post : PanSemStateFiniteExact 64 F} {old cur R0 R : List Ivl} {msgIvl : Ivl}
    (hA0 : ArenaReady entry) (hAs : ArenaReady s)
    (hhp : globN entry "heap_ptr" ≤ globN s "heap_ptr")
    (hfp : globN entry "frame_mem_ptr" ≤ globN s "frame_mem_ptr")
    (hsp : globN s "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hog : OwnedGrows entry s old cur)
    (hmsg_fresh : Inside msgIvl (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hR : ∀ i ∈ R, i = msgIvl ∨ i ∈ R0)
    (h01 : FrameOutside entry s (old ++ R0 ++ [freeGap entry]) (heapFree entry))
    (h12 : FrameOutside s post (cur ++ R ++ [freeGap s]) (heapFree s)) :
    FrameOutside entry post (old ++ R0 ++ [freeGap entry]) (heapFree entry) := by
  intro a ha hhf
  apply Eq.trans (h12 a ?_ ?_) (h01 a ha hhf)
  · intro i hi ⟨hc1, hc2⟩
    rcases List.mem_append.1 hi with hi | hi
    · rcases List.mem_append.1 hi with hi | hi
      · rcases hog i hi with rfl | ⟨j, hj, hin⟩ | hin
        · dsimp at hc2; omega
        · exact ha j (List.mem_append_left _ (List.mem_append_left _ hj))
            ⟨by dsimp [Inside] at hin; omega, by dsimp [Inside] at hin; omega⟩
        · have hlim := hAs.2.2.1
          exact hhf ⟨by dsimp [heapFree, Inside] at hin ⊢; omega,
            by dsimp [heapFree, Inside] at hin ⊢; omega⟩
      · rcases hR i hi with rfl | hi0
        · have hlim := hAs.2.2.1
          exact hhf ⟨by dsimp [heapFree, Inside] at hmsg_fresh ⊢; omega,
            by dsimp [heapFree, Inside] at hmsg_fresh ⊢; omega⟩
        · exact ha i (List.mem_append_left _ (List.mem_append_right _ hi0)) ⟨hc1, hc2⟩
    · simp only [List.mem_singleton] at hi
      subst i
      have h0 := hA0.2.2.2.2.1
      have h1 := hAs.2.2.2.2.1
      exact ha (freeGap entry) (List.mem_append_right _ (by simp))
        ⟨by dsimp [freeGap] at hc1 ⊢; omega, by dsimp [freeGap] at hc2 ⊢; omega⟩
  · intro ⟨hc1, hc2⟩
    have hlim := hAs.2.2.1
    exact hhf ⟨by dsimp [heapFree] at hc1 ⊢; omega, by dsimp [heapFree] at hc2 ⊢; omega⟩


theorem ptxWorldStep_strong_with_locals_right' {F : Type}
    {entry post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry r post) :
    WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry r { post with locals := L, clock := k } :=
  WkBal.worldStep_with_locals_right L k
    (fun _ _ hQ =>
      ⟨retTransactionLogs_congr_memory_heap_bo_ptx rfl rfl rfl rfl hQ.1,
        ptxRetSlices_congr_memory_heap_bo rfl rfl rfl rfl hQ.2⟩) h

theorem pmc_recordsKept_to_entry {F : Type}
    {entry s cal post : PanSemStateFiniteExact 64 F}
    (hbase : PtxRelBase true entry s)
    (hexpw : globN s "bn_expw" = globN entry "bn_expw")
    (hgamma : globN s "bn_gamma" = globN entry "bn_gamma")
    (hmsg_in : Inside (locN s "m", 176) (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hcal_mem : cal.memory = s.memory)
    (hcal_glob : cal.globals = s.globals)
    (hmsg_loc : locN cal "msg" = locN s "m")
    (hrec : RecordsKept pmcRegions pmcKeep cal post) :
    RecordsKept ptxRegions ptxKeep entry post := by
  have hBsub := pmcBufs_sub_entry_of_bn hbase.globals hexpw hgamma
  obtain ⟨⟨_, _, _, _, _⟩, _, _, _, S_e, Nd_e, hWT_e, _⟩ := hbase.ready_entry
  intro rec hr hn off hoff hno
  obtain ⟨offs, hkr, hko⟩ := ptxKeepSub_pmcKeep rec hr
  have heq : globN s rec.1 = globN entry rec.1 := by
    have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
      simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · decide
      · decide
      · simp at hoff
      · decide
    exact globN_eq_of_lookup (hbase.globals (ofString rec.1) hni)
  have hcal_rec : globN cal rec.1 = globN s rec.1 := by simp [globN, hcal_glob]
  have hn_cal : globN cal rec.1 ≠ 0 := by rw [hcal_rec, heq]; exact hn
  have hrec_sz : ∃ sz, (rec.1, sz) ∈ globalBuffers ∧ off + 8 ≤ sz := by
    simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨40, by decide, ?_⟩; simp at hoff; omega
    · refine ⟨80, by decide, ?_⟩; simp at hoff; omega
    · simp at hoff
    · refine ⟨88, by decide, ?_⟩; simp at hoff; omega
  obtain ⟨sz, hgb, hoff_sz⟩ := hrec_sz
  have hfix_rec : (globN entry rec.1, sz) ∈ fixedObjects entry := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.2 ⟨(rec.1, sz), hgb, by simp [hn]⟩
  rcases hWT_e.2.2.1.1 _ hfix_rec with hz_rec | ⟨hal_rec, _⟩
  · dsimp at hz_rec; omega
  · have hmsg_no : ¬ CellHits (globN entry rec.1 + off) (locN s "m", 176) := by
      intro hch
      dsimp [CellHits] at hch
      dsimp [Allocated, Inside] at hal_rec hmsg_in
      have hlim_s : globN s "heap_ptr" ≤ heapLimit := hbase.world.1.2.2.1
      have hsep : heapLimit ≤ scratchStart := by decide
      have hsc_lo : scratchStart ≤ globN entry "scratch_ptr" :=
        Nat.le_trans hbase.arena_entry.2.2.2.1 hbase.arena_entry.2.2.2.2.1
      rcases hal_rec with ⟨_, hhi⟩ | ⟨hlo, _⟩ <;> omega
    have hks := hrec (rec.1, offs) hkr hn_cal off (hko off hoff) (by
      intro i hi
      change i ∈ (locN cal "msg", 176) :: bufRegions pmcBufs cal at hi
      rcases List.mem_cons.1 hi with rfl | hi_buf
      · rw [hcal_rec, heq, hmsg_loc]; exact hmsg_no
      · have hi_s : i ∈ bufRegions pmcBufs s := by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi_buf
          have hbuf_eq : bufferRegion s p = bufferRegion cal p := by
            unfold bufferRegion
            have hg : globN s p.1 = globN cal p.1 := by simp [globN, hcal_glob]
            rw [hg]
          exact List.mem_map.2 ⟨p, hp, hbuf_eq⟩
        rw [hcal_rec, heq]
        exact hno i (hBsub i hi_s))
    rw [hcal_rec, heq] at hks
    rw [hks]
    have hmem_eq : memW cal (globN entry rec.1 + off) = memW s (globN entry rec.1 + off) := by
      simp [memW, hcal_mem]
    exact hmem_eq.trans (hbase.records rec hr hn off hoff hno)

theorem ptxPhase3_eq (tail : ProgHOL 64) :
    R13Shards.ptxPhase3 tail =
      .decCall (ofString "out") .one (ofString "process_message_call")
        [.var .local (ofString "m")] tail := by
  unfold R13Shards.ptxPhase3 R13Shards.ptxCode
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    FrontendCodecComputation.declToHOLStructural,
    FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spineAt, R13Shards.spinePlug]

theorem pmcRegions_disj_worldTypedIvls {F : Type}
    {cal : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hMA : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt cal S Nd) :
    IvlsDisj (pmcRegions cal) (worldTypedIvls cal S Nd) := by
  intro i hi j hj
  change i ∈ (locN cal "msg", 176) :: bufRegions pmcBufs cal at hi
  rcases List.mem_cons.1 hi with rfl | hi_buf
  · exact hMA.2.2.2.2.2.2.2.2.2.2.2.1 j (R13Shards.worldTypedIvls_sub_worldOwned hj)
  · exact validBufList_disj validBufList_pmcBufs hMA.2.1 i hi_buf j hj

theorem pmcTables_mem_of_msgReadyAt {F : Type}
    {cal : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hMA : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt cal S Nd) :
    ∀ t ∈ pmcTables cal, t ∈ S := by
  intro t ht
  change t ∈ [memW cal (locN cal "msg" + 152), memW cal (locN cal "msg" + 160)] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact hMA.2.2.1
  · exact hMA.2.2.2.1

theorem ptxPhase3_relCut_strong (hpmc : PmcMarksBoStrong) :
    PtxRelCutStrong R13Shards.ptxPhase3 PtxAfterPhase2 PtxAfterPhase3 := by
  intro F entry tail htail s hc hA2 hres
  obtain ⟨hbase, hexpw, hgamma, hmsg_in, hMR_ptx, hshapes, htx_loc, hidx_loc, htyp2⟩ := hA2
  rw [ptxPhase3_eq] at hres ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rcases ha_pmc : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "m")] with _ | vs_pmc
  · simp only [ha_pmc] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [ha_pmc] at hres ⊢
    rcases hl_pmc : lookupCodeHOLFinite s.code.lookup (ofString "process_message_call") vs_pmc
        with _ | ⟨body_pmc, callee_pmc, ret_pmc⟩
    · simp only [hl_pmc] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl_pmc] at hres ⊢
      by_cases hclk : s.clock = 0
      · simp only [hclk, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hclk, ↓reduceIte] at hres ⊢
        set cal := callEntryStateHOLFinite s callee_pmc
        have hmsg_lu : callee_pmc.lookup (ofString "msg") =
            some (.val (.word (BitVec.ofNat 64 (locN s "m")))) :=
          R16Shards.PtxP34.lookup_pmc_msg_value s vs_pmc body_pmc callee_pmc ret_pmc hc ha_pmc hl_pmc
        let s_msg := setVarHOLFinite (ofString "msg") (.val (.word (BitVec.ofNat 64 (locN s "m")))) s
        have hs_msg_lu : s_msg.locals.lookup (ofString "msg") =
            some (.val (.word (BitVec.ofNat 64 (locN s "m")))) := by
          simp [s_msg, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
        have hmsg_loc : locN cal "msg" = locN s "m" := by
          have hloc_smsg : locN s_msg "msg" = (BitVec.ofNat 64 (locN s "m")).toNat := by
            simp [locN, hs_msg_lu]
          have hloc_cal : locN cal "msg" = (BitVec.ofNat 64 (locN s "m")).toNat := by
            simp [locN, cal, callEntryStateHOLFinite, hmsg_lu]
          have hm_lt : locN s "m" < 2 ^ 64 := by
            have := (ivl_allocated_bound hbase.world.1.2 (Or.inl ⟨Nat.le_trans hbase.arena_entry.2.1 hmsg_in.1, hmsg_in.2⟩)).2
            dsimp at this; omega
          rw [hloc_cal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt]
        have hMR_cal : MsgReady cal :=
          R16Shards.PtxP34.entry_pmc s vs_pmc body_pmc callee_pmc ret_pmc hc hMR_ptx ha_pmc hl_pmc
        rcases hrun_pmc : evaluateHOLFiniteState cal body_pmc with ⟨res_pmc, post_pmc⟩
        simp only [hrun_pmc] at hres ⊢
        have hBsub := pmcBufs_sub_entry_of_bn hbase.globals hexpw hgamma
        have hRsub_cal : ∀ i ∈ pmcRegions cal,
            i = (locN s "m", 176) ∨ i ∈ ptxRegions entry := by
          intro i hi
          change i ∈ (locN cal "msg", 176) :: bufRegions pmcBufs cal at hi
          rcases List.mem_cons.1 hi with rfl | hi_buf
          · left; rw [hmsg_loc]
          · right
            apply hBsub i
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi_buf
            have hbuf_eq : bufferRegion s p = bufferRegion cal p := by
              unfold bufferRegion; rfl
            exact List.mem_map.2 ⟨p, hp, hbuf_eq⟩
        cases res_pmc with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some br_pmc =>
          cases br_pmc with
          | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid eval =>
            dsimp only at hres ⊢
            unfold PmcMarksBoStrong WorldKeepsIn at hpmc
            have hstep_pmc := FunSpec.at_lookup hpmc s hc vs_pmc body_pmc callee_pmc ret_pmc hl_pmc
              hMR_cal (by rw [hrun_pmc]; simp)
            rw [hrun_pmc] at hstep_pmc
            have hwsi := hstep_pmc hres
            have hg_entry : GlobalsKept ptxGlobals entry post_pmc := by
              intro k hk
              have hkg : k ∉ pmcGlobals.map ofString := by
                intro hm
                obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
                exact hk (List.mem_map.2 ⟨g, pmcGlobals_sub_ptx g hg, rfl⟩)
              exact (hbase.globals k hk).trans (hwsi.2.2.1 k hkg)
            have hrec_entry : RecordsKept ptxRegions ptxKeep entry post_pmc :=
              pmc_recordsKept_to_entry (cal := cal) hbase hexpw hgamma hmsg_in rfl rfl hmsg_loc hwsi.2.2.2.1
            have hex_ws : WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices
                entry (some (.exception eid eval)) post_pmc := by
              refine ⟨hwsi.1, le_trans hbase.heap_entry hwsi.2.1, hg_entry, hrec_entry, ?_⟩
              intro S0 Nd0 hWT0 hD0
              obtain ⟨Sc, Nc, hsub0, hMA_smsg, hOG0, hFO0⟩ := htyp2 S0 Nd0 hWT0 hD0
              have hMA_cal : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt cal Sc Nc :=
                R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                  (s := s_msg) (hmsg_lu.trans hs_msg_lu.symm) hMA_smsg
              obtain ⟨Sn, Nn, hsubn, hWTn, hOGn, hFOn, _⟩ :=
                hwsi.2.2.2.2 Sc Nc hMA_cal.2.1
                  (pmcTables_mem_of_msgReadyAt hMA_cal)
                  (pmcRegions_disj_worldTypedIvls hMA_cal)
              refine ⟨Sn, Nn, fun t ht => hsubn t (hsub0 t ht), hWTn,
                ptx_ownedGrows_trans hbase.heap_entry hwsi.2.1 hOG0 hOGn, ?_,
                (by intro val hv; cases hv), (by intro val hv; cases hv)⟩
              exact ptx_frameOutside_trans_msg hbase.arena_entry hbase.world.1
                hbase.heap_entry hbase.frame_entry hbase.scratch_entry
                hOG0 hmsg_in hRsub_cal hFO0 hFOn
            exact ptxWorldStep_strong_with_locals_right' (emptyLocalsHOLFinite post_pmc).locals post_pmc.clock hex_ws
          | returned val_pmc =>
            dsimp only at hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact val_pmc) .one &&
                shapeEqHOL (shapeOfHOLExact val_pmc) ret_pmc) = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              unfold PmcMarksBoStrong WorldKeepsIn at hpmc
              have hstep_pmc := FunSpec.at_lookup hpmc s hc vs_pmc body_pmc callee_pmc ret_pmc hl_pmc
                hMR_cal (by rw [hrun_pmc]; simp)
              rw [hrun_pmc] at hstep_pmc
              have hwsi := hstep_pmc (Or.inl ⟨val_pmc, rfl⟩)
              set s_res := setVarHOLFinite (ofString "out") val_pmc { post_pmc with locals := s.locals }
              have hs_res_code : s_res.code = originalRuntimeCode := hwsi.1.1.code
              -- Extract w_out and typing from S_e, Nd_e first:
              obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e, S_e, Nd_e, hWT_e, _⟩ :=
                hbase.ready_entry
              have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
                rw [ptxRegions_eq_bufRegions]
                exact validBufList_disj validBufList_ptxBufs hWT_e
              obtain ⟨Sc_e, Nc_e, _, hMA_e_smsg, _, _⟩ := htyp2 S_e Nd_e hWT_e hD_e
              have hMA_e_cal : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt cal Sc_e Nc_e :=
                R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                  (s := s_msg) (hmsg_lu.trans hs_msg_lu.symm) hMA_e_smsg
              obtain ⟨Sn_e, Nn_e, _, hWT_post_e, _, _, hQ_e⟩ :=
                hwsi.2.2.2.2 Sc_e Nc_e hMA_e_cal.2.1
                  (pmcTables_mem_of_msgReadyAt hMA_e_cal)
                  (pmcRegions_disj_worldTypedIvls hMA_e_cal)
              obtain ⟨⟨hrmo_e, hrmo_logs_e⟩, hmarks_e⟩ := hQ_e.1
              have hbo_unhit : PtxBlockOutUnhit cal post_pmc :=
                hQ_e.2 (Or.inr (Or.inr (Or.inr ⟨val_pmc, rfl⟩)))
              obtain ⟨w_out, rfl, hw_out_words, hw_out_in, _, hlogs_ok_post⟩ :=
                hrmo_e val_pmc rfl
              obtain ⟨w_out_m, hw_eq_m, _, hsc_le_end, hmarks_imp⟩ := hmarks_e.2.2 (.val (.word w_out)) rfl
              have hw_m_eq : w_out_m = w_out := by injection hw_eq_m with h1; injection h1 with h2; exact h2.symm
              subst w_out_m
              have hg_entry : GlobalsKept ptxGlobals entry post_pmc := by
                intro k hk
                have hkg : k ∉ pmcGlobals.map ofString := by
                  intro hm
                  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
                  exact hk (List.mem_map.2 ⟨g, pmcGlobals_sub_ptx g hg, rfl⟩)
                exact (hbase.globals k hk).trans (hwsi.2.2.1 k hkg)
              have hrec_entry : RecordsKept ptxRegions ptxKeep entry post_pmc :=
                pmc_recordsKept_to_entry (cal := cal) hbase hexpw hgamma hmsg_in rfl rfl hmsg_loc hwsi.2.2.2.1
              have hW_post : WorldOK post_pmc :=
                ⟨hwsi.1, Sn_e, (worldTyped_iff_with post_pmc Sn_e).2 ⟨Nn_e, hWT_post_e⟩⟩
              -- Transport blockOut fields from s (= cal) to post_pmc via hrec_entry and hbo_unhit:
              have hbo_s_entry : globN s "bo" = globN entry "bo" :=
                globN_eq_of_lookup (hbase.globals (ofString "bo") (by decide))
              have hbo_post_entry : globN post_pmc "bo" = globN entry "bo" :=
                globN_eq_of_lookup (hg_entry (ofString "bo") (by decide))
              have hbo_nz_s : globN s "bo" ≠ 0 := by rw [hbo_s_entry]; exact hbo_nz_e
              have hWT_s_e : WorldTypedWith s Sc_e Nc_e :=
                (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals cal s.locals s.clock Sc_e Nc_e).2 hMA_e_cal.2.1
              have hbo_unhit_s : PtxBlockOutUnhit s post_pmc := hbo_unhit
              have hbo24_s : memW s (globN s "bo" + 24) = memW entry (globN entry "bo" + 24) :=
                ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
              have hbo32_s : memW s (globN s "bo" + 32) = memW entry (globN entry "bo" + 32) :=
                ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
              have hbo40_s : memW s (globN s "bo" + 40) = memW entry (globN entry "bo" + 40) :=
                ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
              have hbo72_s : memW s (globN s "bo" + 72) = memW entry (globN entry "bo" + 72) :=
                ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
              have hbo80_s : memW s (globN s "bo" + 80) = memW entry (globN entry "bo" + 80) :=
                ptx_entry_bo_field_eq hWT_e hbase.globals hbase.records hbo_nz_e (by simp) (by omega)
              have hbo24_p : memW post_pmc (globN post_pmc "bo" + 24) = memW entry (globN entry "bo" + 24) :=
                ptx_entry_bo_field_eq hWT_e hg_entry hrec_entry hbo_nz_e (by simp) (by omega)
              have hbo32_p : memW post_pmc (globN post_pmc "bo" + 32) = memW entry (globN entry "bo" + 32) :=
                ptx_entry_bo_field_eq hWT_e hg_entry hrec_entry hbo_nz_e (by simp) (by omega)
              have hbo40_p : memW post_pmc (globN post_pmc "bo" + 40) = memW entry (globN entry "bo" + 40) :=
                ptx_entry_bo_field_eq hWT_e hg_entry hrec_entry hbo_nz_e (by simp) (by omega)
              have hbo72_p : memW post_pmc (globN post_pmc "bo" + 72) = memW entry (globN entry "bo" + 72) :=
                ptx_entry_bo_field_eq hWT_e hg_entry hrec_entry hbo_nz_e (by simp) (by omega)
              have hbo40_nz_s : memW s (globN s "bo" + 40) ≠ 0 := by rw [hbo40_s]; exact hbo40_nz_e
              have hbo72_nz_s : memW s (globN s "bo" + 72) ≠ 0 := by rw [hbo72_s]; exact hbo72_nz_e
              have hlog_hdr0 : memW post_pmc (memW post_pmc (globN post_pmc "bo" + 40)) =
                  memW s (memW s (globN s "bo" + 40)) := by
                rw [hbo40_p, ← hbo40_s]
                have hm : (memW s (globN s "bo" + 40), 24) ∈ blockOutObjects s := by
                  simp [blockOutObjects, hbo_nz_s, hbo40_nz_s]
                simpa using memW_eq_of_ptxBlockOutUnhit hbase.world.1 hWT_s_e hbo_unhit_s hm (off := 0) (by decide) (by decide)
              have hrcpt_hdr0 : memW post_pmc (memW post_pmc (globN post_pmc "bo" + 72)) =
                  memW s (memW s (globN s "bo" + 72)) := by
                rw [hbo72_p, ← hbo72_s]
                simpa using ptx_receipt_header_eq_of_blockOutUnhit hbase.world.1 hWT_s_e hbo_unhit_s hbo_nz_s hbo72_nz_s (off := 0) (by simp)
              have hrcpt_hdr8 : memW post_pmc (memW post_pmc (globN post_pmc "bo" + 72) + 8) =
                  memW s (memW s (globN s "bo" + 72) + 8) := by
                rw [hbo72_p, ← hbo72_s]
                exact ptx_receipt_header_eq_of_blockOutUnhit hbase.world.1 hWT_s_e hbo_unhit_s hbo_nz_s hbo72_nz_s (by simp)
              have hsl_eq : ∀ off ∈ ([24, 32] : List Nat), ∀ k, k ≤ locN entry "index" →
                  memW post_pmc (memW post_pmc (globN post_pmc "bo" + off) + 16 * k + 8) =
                    memW s (memW s (globN s "bo" + off) + 16 * k + 8) := by
                intro off hoff k hk
                have hbo_off_eq : memW post_pmc (globN post_pmc "bo" + off) = memW s (globN s "bo" + off) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  rcases hoff with rfl | rfl
                  · rw [hbo24_p, hbo24_s]
                  · rw [hbo32_p, hbo32_s]
                rw [hbo_off_eq]
                have hp_nz : memW s (globN s "bo" + off) ≠ 0 := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  rcases hoff with rfl | rfl
                  · rw [hbo24_s]; exact hbo24_nz_e
                  · rw [hbo32_s]; exact hbo32_nz_e
                apply ptx_slice_length_eq_of_blockOutUnhit hbase.world.1 hWT_s_e hbo_unhit_s hbo_nz_s hoff hp_nz
                rw [hbo80_s]; omega
              have hbase_post : PtxRelBase true entry post_pmc := by
                refine ⟨hbase.ready_entry, hbase.arena_entry,
                  le_trans hbase.frame_entry hmarks_e.1,
                  le_trans hmarks_e.2.1 hbase.scratch_entry,
                  hW_post, le_trans hbase.heap_entry hwsi.2.1, hg_entry, hrec_entry,
                  by rw [hrcpt_hdr0]; exact hbase.rcpt_backing,
                  by rw [hlog_hdr0]; exact hbase.log_backing,
                  hrcpt_hdr8.trans hbase.rcpt_len_eq,
                  fun off hoff k hk => (hsl_eq off hoff k (Nat.le_of_lt hk)).trans (hbase.slices_prev off hoff k hk),
                  fun ht => by rw [hsl_eq 24 (by simp) (locN entry "index") le_rfl]; exact hbase.tx_slice_cur ht,
                  ?_⟩
                intro S0 Nd0 hWT0 hD0
                obtain ⟨Sc, Nc, hsub0, hMA_smsg, hOG0, hFO0⟩ := htyp2 S0 Nd0 hWT0 hD0
                have hMA_cal : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt cal Sc Nc :=
                  R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                    (s := s_msg) (hmsg_lu.trans hs_msg_lu.symm) hMA_smsg
                obtain ⟨Sn, Nn, hsubn, hWTn, hOGn, hFOn, _⟩ :=
                  hwsi.2.2.2.2 Sc Nc hMA_cal.2.1
                    (pmcTables_mem_of_msgReadyAt hMA_cal)
                    (pmcRegions_disj_worldTypedIvls hMA_cal)
                refine ⟨Sn, Nn, fun t ht => hsubn t (hsub0 t ht), hWTn,
                  ptx_ownedGrows_trans hbase.heap_entry hwsi.2.1 hOG0 hOGn, ?_⟩
                exact ptx_frameOutside_trans_msg hbase.arena_entry hbase.world.1
                  hbase.heap_entry hbase.frame_entry hbase.scratch_entry
                  hOG0 hmsg_in hRsub_cal hFO0 hFOn
              have hbase_res : PtxRelBase true entry s_res :=
                ptxRelBase_with_locals hbase_post s_res.locals post_pmc.clock
              have hout_lu_res : s_res.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
                simp [s_res, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
              have htx_lu_res : s_res.locals.lookup (ofString "tx") = entry.locals.lookup (ofString "tx") := by
                have h1 : s_res.locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := by
                  simp [s_res, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                    show ofString "out" ≠ ofString "tx" by decide]
                exact h1.trans htx_loc
              have hidx_lu_res : s_res.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index") := by
                have h1 : s_res.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
                  simp [s_res, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                    show ofString "out" ≠ ofString "index" by decide]
                exact h1.trans hidx_loc
              have hA3_res : PtxAfterPhase3 entry s_res := by
                refine ⟨cal, w_out, ⟨hbase_res, hMR_cal.1, hwsi.2.1, hout_lu_res,
                  hw_out_words, hw_out_in, ?_,
                  (R13Shards.logsListOK_with_locals post_pmc s_res.locals post_pmc.clock _).2 hlogs_ok_post,
                  ptxPhase4LocalShapes_resume s post_pmc (.val (.word w_out)) hshapes,
                  htx_lu_res, hidx_lu_res, ?_⟩⟩
                · intro h80_nz
                  obtain ⟨h80_sc, h88_eq, h88_le, h80_8, _⟩ := hmarks_imp h80_nz
                  have hfmp8 : globN cal "frame_mem_ptr" % 8 = 0 := hMR_cal.1.2.2.2.2.2.2.2.1
                  have h88_eq' : memW s_res (w_out.toNat + 88) = globN cal "frame_mem_ptr" := h88_eq
                  exact ⟨h80_8, by rw [h88_eq']; exact hfmp8, Nat.le_of_eq h88_eq'.symm, h88_le, h80_sc⟩
                · intro S0 Nd0 hWT0 hD0
                  obtain ⟨Sc, Nc, hsub0, hMA_smsg, hOG0, hFO0⟩ := htyp2 S0 Nd0 hWT0 hD0
                  have hMA_cal : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt cal Sc Nc :=
                    R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                      (s := s_msg) (hmsg_lu.trans hs_msg_lu.symm) hMA_smsg
                  obtain ⟨Sn, Nn, hsubn, hWTn, hOGn, hFOn, hQn⟩ :=
                    hwsi.2.2.2.2 Sc Nc hMA_cal.2.1
                      (pmcTables_mem_of_msgReadyAt hMA_cal)
                      (pmcRegions_disj_worldTypedIvls hMA_cal)
                  obtain ⟨⟨hrmo_n, hrmo_logs_n⟩, _⟩ := hQn.1
                  obtain ⟨w_n1, hw_eq1, _, _, hdisj_out_n, _⟩ := hrmo_n (.val (.word w_out)) rfl
                  have hw1 : w_n1 = w_out := by injection hw_eq1 with h1; injection h1 with h2; exact h2.symm
                  subst w_n1
                  obtain ⟨w_n2, hw_eq2, hlogs_live_n⟩ := hrmo_logs_n (.val (.word w_out)) rfl
                  have hw2 : w_n2 = w_out := by injection hw_eq2 with h1; injection h1 with h2; exact h2.symm
                  subst w_n2
                  refine ⟨Sc, Nc, Sn, Nn, hMA_cal.2.1, fun t ht => hsubn t (hsub0 t ht),
                    (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post_pmc s_res.locals post_pmc.clock Sn Nn).2 hWTn,
                    hOGn,
                    ptx_ownedGrows_trans hbase.heap_entry hwsi.2.1 hOG0 hOGn,
                    ptx_frameOutside_trans_msg hbase.arena_entry hbase.world.1
                      hbase.heap_entry hbase.frame_entry hbase.scratch_entry
                      hOG0 hmsg_in hRsub_cal hFO0 hFOn,
                    fun o ho => hdisj_out_n _ (by simp) o ho,
                    hlogs_live_n⟩
              rcases hrun_tail : evaluateHOLFiniteState s_res tail with ⟨res_t, post_t⟩
              have htail_step := htail s_res hs_res_code hA3_res
              unfold PtxRelRunStrong at htail_step
              rw [hrun_tail] at htail_step
              simp only [hrun_tail] at hres ⊢
              cases res_t with
              | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              | some br_t =>
                cases br_t with
                | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | exception eid eval =>
                  exact ptxWorldStep_strong_with_locals_right'
                    (HolFiniteMapExact.resVarEq post_t.locals (ofString "out", s.locals.lookup (ofString "out")))
                    post_t.clock (htail_step hres)
                | returned val_t =>
                  exact ptxWorldStep_strong_with_locals_right'
                    (HolFiniteMapExact.resVarEq post_t.locals (ofString "out", s.locals.lookup (ofString "out")))
                    post_t.clock (htail_step (Or.inl ⟨val_t, rfl⟩))
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
