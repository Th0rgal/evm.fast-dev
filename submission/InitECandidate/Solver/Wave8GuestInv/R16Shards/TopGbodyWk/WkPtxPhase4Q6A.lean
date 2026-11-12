import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q2

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

/-! # Phase 4Q6A: the g8 loop-exit bundle and the stable-logs chain

The copy loop (loop 38) exits at a state where the fresh `stable_logs`
list is complete: its header cells hold the backing base, the count and
the capacity, and its first `nl` backing cells hold the source list's
entry pointers.  `P4Q8Exit` packages exactly what the final push
(instruction 39) and its slot store need; both the copying path
(`nl ≠ 0`) and the empty path (`nl = 0`, where nothing is known about the
out-record's list beyond `P4Data.logs_ok`) establish it.

`p4Q8ChainX` is the typing chain of the tail: the `PtxAfterPhase4Data`
typing conjuncts with the `StableLogsHeapDisj` fact of the fresh list
stated against the SAME witnesses, so that it can be threaded through the
push callee and the slot store. -/

/-- `TxEnv` from the base invariant and the kept `index` local. -/
theorem p4Q8_txEnv_of_base {F : Type}
    {entry t : PanSemStateFiniteExact 64 F}
    (h : PtxRelBase true entry t)
    (hidx_local : t.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index")) :
    TxEnv t := by
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, hjcap_e, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := h.ready_entry
  have hbo24 := ptx_entry_bo_field_eq (off := 24) hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo32 := ptx_entry_bo_field_eq (off := 32) hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo40 := ptx_entry_bo_field_eq (off := 40) hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo72 := ptx_entry_bo_field_eq (off := 72) hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo80 := ptx_entry_bo_field_eq (off := 80) hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo_s : globN t "bo" = globN entry "bo" :=
    globN_eq_of_lookup (h.globals (ofString "bo") (by decide))
  have hidx : locN t "index" = locN entry "index" := by
    simp only [locN, hidx_local]
  exact ⟨
    by rw [hbo_s]; exact hbo_nz_e,
    by rw [hbo24]; exact hbo24_nz_e,
    by rw [hbo32]; exact hbo32_nz_e,
    by rw [hbo40]; exact hbo40_nz_e,
    by rw [hbo72]; exact hbo72_nz_e,
    by rw [hidx, hbo80]; exact hidx_lt_e,
    by rw [globN_eq_of_lookup (h.globals (ofString "journal_cap") (by decide))]; exact hjcap_e⟩

/-- The loop-38 exit bundle at state `t`: the fresh list `lw` (capacity
`capw`, count `nl_w`) is complete.  `ents` ties each live backing cell to
the matching entry pointer of the out-record's list (vacuous on the empty
path); `rcpt_cur` is the current receipt slice bound established by the
receipt store of instruction 27. -/
structure P4Q8Exit {F : Type} (entry s_pmc : PanSemStateFiniteExact 64 F)
    (w_out lw capw nl_w : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop where
  base : PtxRelBase true entry t
  chain : p4Q8Chain entry s_pmc w_out lw capw t
  code : t.code = originalRuntimeCode
  arena_pmc : ArenaReady s_pmc
  heap_pmc : globN s_pmc "heap_ptr" ≤ globN t "heap_ptr"
  -- constant geometry
  lw_al : lw.toNat % 8 = 0
  lw_ge : sourceBase ≤ lw.toNat
  hp_ent : globN entry "heap_ptr" ≤ lw.toNat
  cap_pos : 1 ≤ capw.toNat
  nl_le_cap : nl_w.toNat ≤ capw.toNat
  nl_28 : nl_w.toNat < 2 ^ 28
  lim64 : lw.toNat + 24 + 8 * capw.toNat ≤ 2 ^ 64
  heap_fr : globN t "heap_ptr" = lw.toNat + 24 + 8 * capw.toNat
  -- locals
  out_local : t.locals.lookup (ofString "out") = some (.val (.word w_out))
  sl_local : t.locals.lookup (ofString "stable_logs") = some (.val (.word lw))
  i_local : ∃ w : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word w))
  idx_local : t.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index")
  -- the out-record (inside the heap, strictly below `lw`)
  out_words : WordsOK t (w_out.toNat, 96)
  out_inside : Inside (w_out.toNat, 96) sourceBase (globN t "heap_ptr")
  out_below : w_out.toNat + 96 ≤ lw.toNat
  marks : memW t (w_out.toNat + 80) ≠ 0 →
    memW t (w_out.toNat + 80) % 8 = 0 ∧
    memW t (w_out.toNat + 88) % 8 = 0 ∧
    globN s_pmc "frame_mem_ptr" ≤ memW t (w_out.toNat + 88) ∧
    memW t (w_out.toNat + 88) ≤ memW t (w_out.toNat + 80) ∧
    memW t (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr"
  -- the source logs list (the out-record's list)
  src_logs : LogsListOK t (memW t (w_out.toNat + 16))
  -- the fresh list
  hdr0 : memW t lw.toNat = lw.toNat + 24
  hdr8 : memW t (lw.toNat + 8) = nl_w.toNat
  hdr16 : memW t (lw.toNat + 16) = capw.toNat
  hdr_words : WordsOK t (lw.toNat, 24)
  arr_words : WordsOK t (lw.toNat + 24, 8 * capw.toNat)
  ents : ∀ j, j < nl_w.toNat →
    memW t (w_out.toNat + 16) ≠ 0 ∧
    j < memW t (memW t (w_out.toNat + 16) + 8) ∧
    memW t (lw.toNat + 24 + 8 * j) =
      memW t (memW t (memW t (w_out.toNat + 16)) + 8 * j)
  -- the current receipt slice (written by instruction 27)
  rcpt_cur : memW t (memW t (globN t "bo" + 32) + 16 * locN entry "index" + 8) < 2 ^ 40

/-- The typing chain of the g8 tail.  For every entry typing it exposes
witnesses satisfying every `PtxAfterPhase4Data.typing` conjunct except
`PtxRetSlices`, with the `StableLogsHeapDisj` fact stated for the fresh
list `lw` itself. -/
def p4Q8ChainX {F : Type} (entry s_pmc : PanSemStateFiniteExact 64 F)
    (w_out lw : BitVec 64) (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
    IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
    ∃ S N Sp Np,
      (∀ t' ∈ S0, t' ∈ S) ∧
      WorldTypedWith t S N ∧
      WorldTypedWith s_pmc Sp Np ∧
      OwnedGrows s_pmc t (worldOwned s_pmc Sp Np) (worldOwned t S N) ∧
      OwnedGrows entry t (worldOwned entry S0 Nd0) (worldOwned t S N) ∧
      FrameOutside entry t (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry])
        (heapFree entry) ∧
      (∀ o ∈ worldOwned t S N, Disj (w_out.toNat, 96) o) ∧
      StableLogsHeapDisj t (worldOwned t S N) lw.toNat

/-- The tail chain survives pure locals/clock updates. -/
theorem p4Q8ChainX_with_locals {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw : BitVec 64}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : p4Q8ChainX entry s_pmc w_out lw t) :
    p4Q8ChainX entry s_pmc w_out lw {t with locals := L, clock := k} := by
  intro S0 Nd0 hWT0 hD0
  obtain ⟨S, N, Sp, Np, hsub, hWTt, hWTp, hOGp, hOGe, hFO, hout, hslhd⟩ :=
    h S0 Nd0 hWT0 hD0
  refine ⟨S, N, Sp, Np, hsub, ?_, hWTp, hOGp, hOGe, hFO, hout, hslhd⟩
  exact (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals t L k S N).2 hWTt

/-- The tail chain at the loop exit: the fresh list is a stable copy of
the out-record's list, disjoint from every owned interval. -/
theorem p4Q8ChainX_of_exit {F : Type}
    {entry s_pmc t : PanSemStateFiniteExact 64 F} {w_out lw capw nl_w : BitVec 64}
    (h : P4Q8Exit entry s_pmc w_out lw capw nl_w t) :
    p4Q8ChainX entry s_pmc w_out lw t := by
  intro S0 Nd0 hWT0 hD0
  obtain ⟨S, N, Sp, Np, hsub, hWTt, hWTp, hOGp, hOGe, hFO, hout, hfresh, hlist⟩ :=
    h.chain S0 Nd0 hWT0 hD0
  refine ⟨S, N, Sp, Np, hsub, hWTt, hWTp, hOGp, hOGe, hFO, hout, ?_⟩
  have hlw_ge := h.lw_ge
  have hfr := h.heap_fr
  have hcap := h.cap_pos
  have hnlc := h.nl_le_cap
  have h0 := h.hdr0
  have h8 := h.hdr8
  have h16 := h.hdr16
  -- each live entry of the fresh list is a live entry of the source list
  have hent : ∀ i, i < nl_w.toNat →
      memW t (w_out.toNat + 16) ≠ 0 ∧ i < memW t (memW t (w_out.toNat + 16) + 8) ∧
      memW t (memW t lw.toNat + 8 * i) =
        memW t (memW t (memW t (w_out.toNat + 16)) + 8 * i) := by
    intro i hi
    obtain ⟨hnz, hlt, heq⟩ := h.ents i hi
    refine ⟨hnz, hlt, ?_⟩
    rw [h0]
    exact heq
  refine ⟨⟨Or.inr ⟨h.hdr_words, Or.inl ⟨hlw_ge, by show lw.toNat + 24 ≤ _; omega⟩, ?_, ?_, ?_⟩,
    Or.inr ⟨⟨hlw_ge, by show lw.toNat + 24 ≤ _; omega⟩, ?_⟩⟩, fun _ => ⟨?_, ?_, ?_⟩⟩
  · rw [h8]; exact h.nl_28
  · rw [h8, h16]; exact hnlc
  · intro i hi
    rw [h8] at hi
    obtain ⟨hnz, hlt, heq⟩ := hent i hi
    refine ⟨?_, ?_⟩
    · rw [h0]
      exact h.arr_words.2.2 i (by show i < 8 * capw.toNat / 8; omega)
    · rw [heq]
      exact ((h.src_logs.resolve_left hnz).2.2.2.2 i hlt).2
  · rw [h0, h16]
    exact ⟨by show sourceBase ≤ lw.toNat + 24; omega,
      by show lw.toNat + 24 + 8 * capw.toNat ≤ _; omega⟩
  · intro o ho
    exact hfresh (lw.toNat, 24) (by simp) o ho
  · intro o ho
    rw [h0, h16]
    exact hfresh (lw.toNat + 24, 8 * capw.toNat) (by simp) o ho
  · intro i hi
    rw [h8] at hi
    obtain ⟨hnz, hlt, heq⟩ := hent i hi
    rw [heq]
    have hown := (hlist hnz).2.2 i hlt
    refine ⟨fun o ho => hown _ ?_ o ho, hown⟩
    simp [logOwnedIvls, logRecordIvls]

/-- The tail chain survives a WorldStep at the empty region family (the
final `lst_push` callee and the slot store). -/
theorem p4Q8ChainX_worldStep {F : Type}
    {entry s_pmc t post : PanSemStateFiniteExact 64 F} {w_out lw : BitVec 64}
    {gw : List String} {r : Option (PanSemResultExact 64)}
    (h : p4Q8ChainX entry s_pmc w_out lw t)
    (hW : WorldOK t)
    (hhp_pmc : globN s_pmc "heap_ptr" ≤ globN t "heap_ptr")
    (hhp_ent : globN entry "heap_ptr" ≤ globN t "heap_ptr")
    (hfp_ent : globN entry "frame_mem_ptr" ≤ globN t "frame_mem_ptr")
    (hsp_ent : globN t "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hAR_ent : ArenaReady entry)
    (hw_out8 : w_out.toNat % 8 = 0)
    (hout_inside : Inside (w_out.toNat, 96) sourceBase (globN t "heap_ptr"))
    (hstep : WorldStep (fun _ => []) gw stdKeep NoExtra t r post)
    (hgw : gw = [] ∨ gw = ["heap_ptr"]) :
    p4Q8ChainX entry s_pmc w_out lw post := by
  have hsys : globN post "vm_system_address" = globN t "vm_system_address" := by
    rcases hgw with rfl | rfl
    · exact globN_eq_of_lookup (hstep.2.2.1 (ofString "vm_system_address") (by simp))
    · exact globN_eq_of_lookup (hstep.2.2.1 (ofString "vm_system_address") (by decide))
  have hAs : ArenaOK t := hW.1.2
  have hgS : GuestInv t := hW.1.1
  have hwout96 : w_out.toNat + 96 ≤ globN t "heap_ptr" := hout_inside.2
  intro S0 Nd0 hWT0 hD0
  obtain ⟨S, N, Sp, Np, hsub, hWTt, hWTp, hOGp, hOGe, hFO, hout, hslhd⟩ :=
    h S0 Nd0 hWT0 hD0
  have hR_disj : IvlsDisj ((fun _ => []) t) (worldTypedIvls t S N) := by
    intro o ho
    cases ho
  obtain ⟨S', N', hsub', hWT', hOG', hFO', -⟩ :=
    hstep.2.2.2.2 S N hWTt hR_disj
  have hold0 : ∀ j ∈ worldOwned t S N, j.2 = 0 → j.1 % 8 = 0 :=
    R13Shards.worldOwned_zero_aligned hWTt
  have hR0 : ∀ j ∈ ([] : List Ivl), j.2 = 0 → j.1 % 8 = 0 := by
    intro j hj
    cases hj
  refine ⟨S', N', Sp, Np, fun t' ht' => hsub' t' (hsub t' ht'), hWT', hWTp, ?_, ?_, ?_, ?_, ?_⟩
  · exact ptx_ownedGrows_trans hhp_pmc hstep.2.1 hOGp hOG'
  · exact ptx_ownedGrows_trans hhp_ent hstep.2.1 hOGe hOG'
  · exact ptx_frameOutside_trans hAR_ent ⟨hgS, hAs⟩ hhp_ent hfp_ent hsp_ent hOGe
      (by intro i hi; cases hi) hFO hFO'
  · intro o ho
    rcases hOG' o ho with rfl | ⟨j, hj, hin⟩ | hin
    · exact Or.inr (Or.inl rfl)
    · exact disj_of_inside_right hin (hout j hj)
    · obtain ⟨h1, h2⟩ := hin
      refine Or.inr (Or.inr (Or.inl ?_))
      show w_out.toNat + 96 ≤ o.1
      omega
  · exact stableLogsHeapDisj_step (R := []) hW.1 hstep.1 hstep.2.1 hold0 hR0 hOG' hFO' hsys hslhd
      (fun _ => ⟨fun _ ho => absurd ho List.not_mem_nil, fun _ ho => absurd ho List.not_mem_nil,
        fun _ _ _ ho => absurd ho List.not_mem_nil⟩)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
