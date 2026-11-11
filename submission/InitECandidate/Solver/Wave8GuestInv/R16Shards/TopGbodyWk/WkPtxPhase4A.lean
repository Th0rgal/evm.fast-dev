import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase34R11
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_max
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_udiv_small5

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

/-! # Phase 4 mid-spine invariant (`WkPtxPhase4A`)

`P4Data` extends the phase-3 cut data with the fields Phase 4 needs.  The
`logs` field tracks the address of the log list currently referenced by the
`"logs"` local; before instruction 21 that local does not exist and the
witness `0` makes every logs fact vacuous. -/

structure P4Data {F : Type}
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
  logs_facts : ∃ logs : Nat, (locN s "logs" = logs ∨ logs = 0) ∧
    LogsListOK s logs ∧ LogsDisjFixed s logs ∧
    (∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
      IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
      ∃ S_pmc Nd_pmc S_cur Nd_cur,
        WorldTypedWith s_pmc S_pmc Nd_pmc ∧
        (∀ t ∈ S0, t ∈ S_cur) ∧
        WorldTypedWith s S_cur Nd_cur ∧
        OwnedGrows s_pmc s (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s S_cur Nd_cur) ∧
        OwnedGrows entry s (worldOwned entry S0 Nd0) (worldOwned s S_cur Nd_cur) ∧
        FrameOutside entry s (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) ∧
        (∀ o ∈ worldOwned s S_cur Nd_cur, Disj (w_out.toNat, 96) o) ∧
        PmcLogsLiveOwned s S_cur Nd_cur (memW s (w_out.toNat + 16)) ∧
        PmcLogsLiveOwned s S_cur Nd_cur logs)

/-! ## Bootstrapping `P4Data` from the phase-3 cut -/

theorem p4Data_of_afterPhase3 {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : PtxAfterPhase3Data entry s s_pmc w_out) :
    P4Data entry s s_pmc w_out where
  base := h.base
  arena_pmc := h.arena_pmc
  heap_pmc := h.heap_pmc
  out_local := h.out_local
  out_words := h.out_words
  out_inside := h.out_inside
  marks := h.marks
  logs_ok := h.logs_ok
  shapes := h.shapes
  tx_local := h.tx_local
  idx_local := h.idx_local
  logs_facts := ⟨0, Or.inr rfl, Or.inl rfl, Or.inl rfl, fun S0 Nd0 hW hD => by
    obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      h.typing3 S0 Nd0 hW hD
    exact ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, h1, h2, h3, h4, h5, h6, h7, h8,
      pmcLogsLiveOwned_zero s S_cur Nd_cur⟩⟩

/-! ## Local-frame transport -/

theorem ptxPhase4LocalShapes_setVar {F : Type}
    {s : PanSemStateFiniteExact 64 F} {nm : MlS} {v : ValueHOL 64}
    (hn : ∀ name ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] : List String), ofString name ≠ nm)
    (h : PtxPhase4LocalShapes s) :
    PtxPhase4LocalShapes (setVarHOLFinite nm v s) := by
  have hlu : ∀ name : String, ofString name ≠ nm →
      (setVarHOLFinite nm v s).locals.lookup (ofString name) = s.locals.lookup (ofString name) := by
    intro name hne
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
  refine ⟨?_, ?_, ?_⟩
  · intro name hn'
    rw [hlu name (hn name (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn' ⊢
      rcases hn' with rfl | rfl | rfl | rfl | rfl <;> simp))]
    exact h.1 name hn'
  · rw [hlu "price" (hn "price" (by decide))]
    exact h.2.1
  · rw [hlu "intrinsic" (hn "intrinsic" (by decide))]
    exact h.2.2

theorem p4Data_with_locals {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat)
    (hout : L.lookup (ofString "out") = some (.val (.word w_out)))
    (htx : L.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (hidx : L.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (hlogs : L.lookup (ofString "logs") = s.locals.lookup (ofString "logs"))
    (hsh : PtxPhase4LocalShapes {s with locals := L, clock := ck})
    (h : P4Data entry s s_pmc w_out) :
    P4Data entry {s with locals := L, clock := ck} s_pmc w_out := by
  have hlogsN : locN {s with locals := L, clock := ck} "logs" = locN s "logs" := by
    simp only [locN, hlogs]
  refine ⟨ptxRelBase_with_locals h.base L ck, h.arena_pmc, h.heap_pmc, hout,
    h.out_words, h.out_inside, h.marks,
    (R13Shards.logsListOK_with_locals s L ck (memW s (w_out.toNat + 16))).2 h.logs_ok,
    hsh, htx.trans h.tx_local,
    hidx.trans h.idx_local, ?_⟩
  obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := h.logs_facts
  refine ⟨logs, ?_, hl_ok, hl_dj, ?_⟩
  · rcases hll with h | h
    · left; rw [hlogsN, h]
    · exact Or.inr h
  · intro S0 Nd0 hW hD
    obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      hty S0 Nd0 hW hD
    refine ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, h1, h2, ?_, h4, h5, h6, h7, h8, h9⟩
    exact (R13Shards.worldTypedWith_with_locals s L ck S_cur Nd_cur).2 h3

/-- A `dec`/`assign` of a local that Phase 4's invariant does not track
preserves `P4Data`. -/
theorem p4Data_setVar {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {nm : MlS} {v : ValueHOL 64}
    (hnout : nm ≠ ofString "out") (hntx : nm ≠ ofString "tx")
    (hnidx : nm ≠ ofString "index") (hnlogs : nm ≠ ofString "logs")
    (hshn : ∀ name ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used",
      "price", "intrinsic"] : List String), ofString name ≠ nm)
    (h : P4Data entry s s_pmc w_out) :
    P4Data entry (setVarHOLFinite nm v s) s_pmc w_out := by
  have hlu : ∀ name : String, ofString name ≠ nm →
      (s.locals.update (nm, v)).lookup (ofString name) = s.locals.lookup (ofString name) := by
    intro name hne
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
  refine p4Data_with_locals (s.locals.update (nm, v)) s.clock ?_ ?_ ?_ ?_ ?_ h
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hnout]
    exact h.out_local
  · exact hlu "tx" (Ne.symm hntx)
  · exact hlu "index" (Ne.symm hnidx)
  · exact hlu "logs" (Ne.symm hnlogs)
  · exact ptxPhase4LocalShapes_setVar hshn h.shapes

/-! ## Generic callee-step transport

One lemma transports the whole `P4Data` invariant across any guest call whose
spec is a `WorldStepScBo`: the caller frame is restored (locals of `s`, clock
of the callee exit), the phase-4 fields survive because the out region and
the tracked log lists are disjoint from the callee's buffer footprint. -/

theorem pmcLogs_bufDisj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} {B : BufList}
    (hB : ValidBufList B)
    (hd : PmcLogsLiveOwned s S Nd logs) (hnz : logs ≠ 0) :
    (∀ j ∈ bufRegions B s, Disj (logs, 24) j) ∧
    (∀ j ∈ bufRegions B s, Disj (memW s logs, 8 * memW s (logs + 8)) j) ∧
    (∀ i, i < memW s (logs + 8) →
      ∀ j ∈ bufRegions B s, Disj (memW s (memW s logs + 8 * i), 40) j) := by
  refine ⟨ptx_disj_bufRegions_of_disj_worldOwned hB ((hd hnz).2.1 _ (by simp)),
    ptx_disj_bufRegions_of_disj_worldOwned hB ((hd hnz).2.1 _ (by simp)), ?_⟩
  intro i hi
  have hmem : (memW s (memW s logs + 8 * i), 40) ∈
      logOwnedIvls s (memW s (memW s logs + 8 * i)) := by
    simp [logOwnedIvls, logRecordIvls]
  exact ptx_disj_bufRegions_of_disj_worldOwned hB ((hd hnz).2.2 i hi _ hmem)

theorem p4Data_step_of_worldStepScBo {F : Type}
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
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hbo_keep : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (hscbo : WorldStepScBo (bufRegions B) gw keep Q s r post)
    (hnr : NonExResult r) :
    P4Data entry {post with locals := s.locals, clock := post.clock} s_pmc w_out := by
  have hstep : WorldStep (bufRegions B) gw keep Q s r post := hscbo.1.1
  have hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := hscbo.1.2
  have hbo_unhit : PtxBlockOutUnhit s post := hscbo.2 hnr
  have hfmp : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" :=
    Nat.le_of_eq (globN_eq_of_lookup (hstep.2.2.1 _ hfmp_gw)).symm
  have hsys : globN post "vm_system_address" = globN s "vm_system_address" :=
    globN_eq_of_lookup (hstep.2.2.1 _ hsys_gw)
  have hgrow : AllocatorGrows s post := ⟨hstep.2.1, hsp⟩
  have hAs : ArenaOK s := h.base.world.1.2
  have hAp : ArenaOK post := hstep.1.2
  have hgS : GuestInv s := h.base.world.1.1
  have hgP : GuestInv post := hstep.1.1
  -- One fixed entry typing and the phase-4 typing at `s` it induces.
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e, S_e, Nd_e, hWT_e, _⟩ :=
    h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨logs, hll, hl_ok, hl_dj, hty⟩ := h.logs_facts
  obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hty1, hty2, hWT_s, hty4, hty5, hty6, hty7, hty8, hty9⟩ :=
    hty S_e Nd_e hWT_e hD_e
  -- The callee step's typing at the phase-4 typing of `s`.
  obtain ⟨S_n, N_n, hsub_n, hWT_n, hOG_n, hFO_n, hQ_n⟩ :=
    hstep.2.2.2.2 S_cur Nd_cur hWT_s (validBufList_disj hB hWT_s)
  have hold0 : ∀ j ∈ worldOwned s S_cur Nd_cur, j.2 = 0 → j.1 % 8 = 0 :=
    R13Shards.worldOwned_zero_aligned hWT_s
  have hR0 : ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 :=
    ptx_bufRegions_zero_aligned hB hWT_s.2.2.1
  -- The out region is untouched, stays inside the heap and stays disjoint.
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
  -- Surviving facts for the tracked log lists.
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
      (ptxRelBase_step_of_blockOutUnhit h.base hB hBsub hgw hkeep hbo_gw hbo_keep
        hstep hsp hfmp hbo_unhit) s.locals post.clock,
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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
