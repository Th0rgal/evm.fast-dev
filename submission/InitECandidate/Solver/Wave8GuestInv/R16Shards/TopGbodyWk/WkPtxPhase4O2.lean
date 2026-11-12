import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4O1

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

/-! ## G. Transports across the receipt-encoding callee

`p4Run_decCall_encode_receipt` (4D) hands the continuation `LogsListOK` at
the callee's return state, but not `LogsDisjFixed` nor the out-list/fresh-
list disjunction: the callee may write inside the keccak work intervals and
grow the heap pointer, and `P4Data`'s `logs_facts` witness degrades to `0`
across the callee step.  The lemmas below carry both facts across the
callee directly: every logs interval is either an allocated interval
disjoint from the keccak work intervals (hence unhit, by `HeapByteEff`), or
a low cell below `sourceBase` (never in the ordinary domain), and
`fixedObjects` is stable (`p4O_callee_fixed_eq`). -/

/-- Allocated intervals survive the callee: the heap only grows upwards and
scratch only downwards, so `Inside` bounds are preserved on either side. -/
theorem p4O_alloc_callee {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"])
    {iv : Ivl} (hal : Allocated s iv) : Allocated mid iv := by
  rcases hal with h | h
  · exact Or.inl ⟨h.1, h.2.trans heff.hp_le⟩
  · exact Or.inr ⟨heff.sp_le.trans h.1, h.2⟩

/-- The low cells below `sourceBase` survive the callee: a changed low cell
would have to be in the source's ordinary domain, which starts at
`sourceBase`. -/
theorem p4O_lowCell_callee {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"])
    {c : Nat} (hc : c < 17) :
    mid.memory (BitVec.ofNat 64 c) = s.memory (BitVec.ofNat 64 c) := by
  by_contra hne
  have hdom : s.memaddrs (BitVec.ofNat 64 c) := heff.out_dom _ hne
  rw [hAR.1.memaddrs, ordinaryDomain_iff] at hdom
  have hsb : 16 < sourceBase := by decide
  have htk : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [htk] at hdom
  omega

theorem p4O_lowMemW_callee {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"])
    {c : Nat} (hc : c < 17) : memW mid c = memW s c := by
  simp only [memW, p4O_lowCell_callee hAR heff hc]

theorem p4O_wordAt_low_callee {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"])
    {c : Nat} (hc : c < 17) (hw : WordAt s c) : WordAt mid c := by
  obtain ⟨w, hdom, hcell⟩ := hw
  refine ⟨w, ?_, ?_⟩
  · rw [heff.memaddrs]; exact hdom
  · rw [p4O_lowCell_callee hAR heff hc]; exact hcell

/-- `LogsDisjFixed` survives the callee: the header and backing-array cells
lie in the (allocated, keccak-disjoint) header interval, every owned log
record is allocated inside the heap and disjoint from the keccak intervals
(via the `fixedObjects` separation `LogsDisjFixed` already provides), and
`fixedObjects` itself is stable. -/
theorem p4O_logsDisjFixed_callee {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) (hE : TxEnv s) (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"]) {wl : Nat}
    (hLL : LogsListOK s wl) (hDF : LogsDisjFixed s wl) :
    LogsDisjFixed mid wl := by
  rcases hDF with h0 | ⟨hal_back, hIvls⟩
  · exact Or.inl h0
  rcases hLL with hz | ⟨hw_hdr, hal_hdr, hcap, hlen, hent⟩
  · rw [hz]; exact Or.inl rfl
  -- the system-address global and the fixed objects are stable
  have hsys : globN mid "vm_system_address" = globN s "vm_system_address" :=
    globN_eq_of_lookup (heff.globals (ofString "vm_system_address") (by decide))
  have hfix_eq : fixedObjects mid = fixedObjects s :=
    p4O_callee_fixed_eq hWT hE hAR heff
  -- the header interval avoids the keccak work intervals
  have hd_hdr : ∀ j ∈ receiptKeccakIvls s, Disj (wl, 24) j := fun j hj =>
    hIvls _ (List.mem_append.2 (Or.inl (List.mem_cons.2 (Or.inl rfl)))) j
      (p4O_keccak_fixed s hj)
  have hu_hdr : IvlUnhit s mid (wl, 24) :=
    p4O_ivlUnhit_callee hAR heff hal_hdr hw_hdr.1 hw_hdr.2.1 hd_hdr
  have hhi_hdr : (wl, 24).1 + (wl, 24).2 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 hal_hdr).2
  have hwa8 : wl % 8 = 0 := hw_hdr.1
  have c0 : memW mid wl = memW s wl :=
    memW_eq_of_ivlUnhit (a := wl) hu_hdr hw_hdr.1 hhi_hdr
      (p4O_cellIn (a := wl) (n := 24) (c := 0) (by omega))
  have c8 : memW mid (wl + 8) = memW s (wl + 8) :=
    memW_eq_of_ivlUnhit (a := wl + 8) hu_hdr (by omega) hhi_hdr
      (p4O_cellIn (a := wl) (n := 24) (c := 8) (by omega))
  -- the backing-array cells survive
  have hd_back : ∀ j ∈ receiptKeccakIvls s, Disj (memW s wl, 8 * memW s (wl + 8)) j :=
    fun j hj => hIvls _ (List.mem_append.2 (Or.inl (List.mem_cons.2
      (Or.inr (List.mem_cons.2 (Or.inl rfl)))))) j (p4O_keccak_fixed s hj)
  have hpb1 : (memW s wl, 8 * memW s (wl + 8)).1 = memW s wl := rfl
  have hpb2 : (memW s wl, 8 * memW s (wl + 8)).2 = 8 * memW s (wl + 8) := rfl
  have hb : ∀ i : Nat, i < memW s (wl + 8) →
      memW mid (memW s wl + 8 * i) = memW s (memW s wl + 8 * i) := by
    intro i _
    exact p4O_memW_kept hAR heff hal_back hd_back (by omega) (by omega)
  -- every owned log record is unhit by the callee
  have hrec_mem : ∀ i : Nat, i < memW s (wl + 8) →
      (memW s (memW s wl + 8 * i), 40) ∈ logOwnedIvls s (memW s (memW s wl + 8 * i)) := by
    intro i _
    unfold logOwnedIvls
    refine List.mem_filter.2 ⟨by simp [logRecordIvls], ?_⟩
    simp only [bne_iff_ne, ne_eq, Prod.mk.injEq, not_and]
    intro _ h40; omega
  have hu_rec : ∀ i : Nat, i < memW s (wl + 8) →
      IvlUnhit s mid (memW s (memW s wl + 8 * i), 40) := by
    intro i hi
    have hflat : (memW s (memW s wl + 8 * i), 40) ∈
        (List.range (memW s (wl + 8))).flatMap
          (fun idx => logOwnedIvls s (memW s (memW s wl + 8 * idx))) :=
      List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hrec_mem i hi⟩
    have hd : ∀ j ∈ receiptKeccakIvls s, Disj (memW s (memW s wl + 8 * i), 40) j :=
      fun j hj => hIvls _ (List.mem_append.2 (Or.inr hflat)) j (p4O_keccak_fixed s hj)
    exact p4O_ivlUnhit_callee hAR heff (Or.inl (hent i hi).2.2.1)
      (hent i hi).2.1.1 (hent i hi).2.1.2.1 hd
  refine Or.inr ⟨?_, ?_⟩
  · rw [c0, c8]
    exact p4O_alloc_callee heff hal_back
  · rw [hfix_eq, c0, c8]
    intro o ho j hj
    rcases List.mem_append.1 ho with hA | hB
    · rcases List.mem_cons.1 hA with h1 | h2
      · exact hIvls _ (List.mem_append.2 (Or.inl (List.mem_cons.2 (Or.inl h1)))) j hj
      · rcases List.mem_cons.1 h2 with h1 | h3
        · exact hIvls _ (List.mem_append.2 (Or.inl (List.mem_cons.2
            (Or.inr (List.mem_cons.2 (Or.inl h1)))))) j hj
        · exact absurd h3 (by simp)
    · obtain ⟨i, hi, ho2⟩ := List.mem_flatMap.1 hB
      have hi' : i < memW s (wl + 8) := List.mem_range.1 hi
      rw [hb i hi'] at ho2
      rw [pmc_logOwnedIvls_eq_of_unhit hAR.2 (hent i hi').2 (hu_rec i hi') hsys] at ho2
      exact hIvls _ (List.mem_append.2 (Or.inr (List.mem_flatMap.2
        ⟨i, List.mem_range.2 hi', ho2⟩))) j hj

/-- The out-list/fresh-list disjunction survives the callee.  The out record
is disjoint from every fixed object (hence from the keccak work intervals),
so its `+16` word is preserved; a fresh list header is preserved through
the header interval's unhit (live case) or the low cells (null case), and
the heap pointer only grows. -/
theorem p4O_disj_callee {F : Type} {entry s mid s_pmc : PanSemStateFiniteExact 64 F}
    {w_out wl : BitVec 64}
    (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"])
    (hD : P4Data entry s s_pmc w_out)
    (hLL : LogsListOK s wl.toNat) (hDF : LogsDisjFixed s wl.toNat)
    (hdisj : wl.toNat = memW s (w_out.toNat + 16) ∨
      (memW s (wl.toNat) = wl.toNat + 24 ∧ memW s (wl.toNat + 8) = 0 ∧
        WordAt s (wl.toNat) ∧ WordAt s (wl.toNat + 8) ∧
        wl.toNat + 32 ≤ globN s "heap_ptr")) :
    wl.toNat = memW mid (w_out.toNat + 16) ∨
      (memW mid (wl.toNat) = wl.toNat + 24 ∧ memW mid (wl.toNat + 8) = 0 ∧
        WordAt mid (wl.toNat) ∧ WordAt mid (wl.toNat + 8) ∧
        wl.toNat + 32 ≤ globN mid "heap_ptr") := by
  -- the out record is unhit by the callee
  have hout_disj := p4O_out_disj hD
  have hout_u : IvlUnhit s mid (w_out.toNat, 96) :=
    p4O_ivlUnhit_callee hAR heff (Or.inl hD.out_inside) hD.out_words.1 hD.out_words.2.1
      (fun j hj => hout_disj j (p4O_keccak_fixed s hj))
  have hout_hi : (w_out.toNat, 96).1 + (w_out.toNat, 96).2 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 (Or.inl hD.out_inside)).2
  have hout8 : w_out.toNat % 8 = 0 := hD.out_words.1
  have hout16 : memW mid (w_out.toNat + 16) = memW s (w_out.toNat + 16) :=
    memW_eq_of_ivlUnhit (a := w_out.toNat + 16) hout_u (by omega) hout_hi
      (p4O_cellIn (a := w_out.toNat) (n := 96) (c := 16) (by omega))
  by_cases hwl0 : wl.toNat = 0
  · rw [hwl0] at hdisj ⊢
    rcases hdisj with hkeep | ⟨hm0, hm8, hw0, hw8, hhp⟩
    · exact Or.inl (hkeep.trans hout16.symm)
    · refine Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (p4O_lowMemW_callee hAR heff (c := 0) (by omega)).trans hm0
      · exact (p4O_lowMemW_callee hAR heff (c := 8) (by omega)).trans hm8
      · exact p4O_wordAt_low_callee hAR heff (by omega) hw0
      · exact p4O_wordAt_low_callee hAR heff (by omega) hw8
      · exact hhp.trans heff.hp_le
  · -- the live list: the header interval is unhit
    rcases hLL with hz | ⟨hw_hdr, hal_hdr, hcap, hlen, hent⟩
    · exact absurd hz hwl0
    rcases hDF with hz2 | ⟨hal_back, hIvls⟩
    · exact absurd hz2 hwl0
    have hd_hdr : ∀ j ∈ receiptKeccakIvls s, Disj (wl.toNat, 24) j := fun j hj =>
      hIvls _ (List.mem_append.2 (Or.inl (List.mem_cons.2 (Or.inl rfl)))) j
        (p4O_keccak_fixed s hj)
    have hu_hdr : IvlUnhit s mid (wl.toNat, 24) :=
      p4O_ivlUnhit_callee hAR heff hal_hdr hw_hdr.1 hw_hdr.2.1 hd_hdr
    have hhi_hdr : (wl.toNat, 24).1 + (wl.toNat, 24).2 ≤ 2 ^ 64 :=
      (ivl_allocated_bound hAR.2 hal_hdr).2
    have hpw1 : (wl.toNat, 24).1 = wl.toNat := rfl
    have hpw2 : (wl.toNat, 24).2 = 24 := rfl
    have hwa8 : wl.toNat % 8 = 0 := hw_hdr.1
    have c0 : memW mid (wl.toNat) = memW s (wl.toNat) :=
      memW_eq_of_ivlUnhit (a := wl.toNat) hu_hdr hw_hdr.1 hhi_hdr
        (p4O_cellIn (a := wl.toNat) (n := 24) (c := 0) (by omega))
    have c8 : memW mid (wl.toNat + 8) = memW s (wl.toNat + 8) :=
      memW_eq_of_ivlUnhit (a := wl.toNat + 8) hu_hdr (by omega) hhi_hdr
        (p4O_cellIn (a := wl.toNat) (n := 24) (c := 8) (by omega))
    rcases hdisj with hkeep | ⟨hm0, hm8, hw0, hw8, hhp⟩
    · exact Or.inl (hkeep.trans hout16.symm)
    have hwA : WordAt mid (wl.toNat) := by
      obtain ⟨w, hdom_s, hcell_s⟩ := hw0
      refine ⟨w, ?_, ?_⟩
      · rw [heff.memaddrs]; exact hdom_s
      · have hround : (BitVec.ofNat 64 wl.toNat).toNat = wl.toNat := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hch : CellHits (BitVec.ofNat 64 wl.toNat).toNat (wl.toNat, 24) := by
          rw [hround]
          exact ⟨by omega, by omega⟩
        rw [hu_hdr (BitVec.ofNat 64 wl.toNat) (by rw [hround]; exact hwa8) hch]
        exact hcell_s
    have hwB : WordAt mid (wl.toNat + 8) := by
      obtain ⟨w, hdom_s, hcell_s⟩ := hw8
      refine ⟨w, ?_, ?_⟩
      · rw [heff.memaddrs]; exact hdom_s
      · have hround : (BitVec.ofNat 64 (wl.toNat + 8)).toNat = wl.toNat + 8 := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        have hch : CellHits (BitVec.ofNat 64 (wl.toNat + 8)).toNat (wl.toNat, 24) := by
          rw [hround]
          exact ⟨by omega, by omega⟩
        rw [hu_hdr (BitVec.ofNat 64 (wl.toNat + 8)) (by rw [hround]; omega) hch]
        exact hcell_s
    exact Or.inr ⟨c0.trans hm0, c8.trans hm8, hwA, hwB, hhp.trans heff.hp_le⟩

/-! ## H. Store-destination evaluations

The store destinations are `bo[0x20] + 16 * index (+ 8)`: a load from the
receipt-slices array base (block-out element 1) plus the scaled index (plus
the second half's `+8`).  Both evaluate to words whose natural values are
pinned by the cells and locals. -/

/-- The first slice store's destination evaluates to the array cell address. -/
theorem p4O_encDstEval {F : Type} {u : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady u) {S Nd : List Nat} (hWT : WorldTypedWith u S Nd) (hE : TxEnv u)
    {idxw : BitVec 64} (hidxl : u.locals.lookup (ofString "index") = some (.val (.word idxw)))
    {x : BitVec 64}
    (hev : evalAt u (.op .add [(.load .one (.op .add [.var .global (ofString "bo"),
      (.const 0x0000000000000020#64)])),
      (.panop .mul [(.var .local (ofString "index")),
        (.const 0x0000000000000010#64)])]) = some (.val (.word x))) :
    x.toNat = memW u (globN u "bo" + 32) + 16 * locN u "index" := by
  -- the receipt-slices array is block-out element 1
  have hT : TablesTyped u S := hWT.1
  have hF : FixedTyped u := hWT.2.2.1
  have hbo7 := (blockOutObjects_eq_list hE hT).2.2
  have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo7]; rfl
  have hget1 : (blockOutObjects u)[1] =
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo7]
  have harr_mem : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := by
    have h := List.getElem_mem (l := blockOutObjects u) (n := 1)
      (h := by rw [hbo_len]; decide)
    rw [hget1] at h
    exact h
  have harr_fix := p4O_fixed_mem_blockOut harr_mem
  have harr_alloc : Allocated u (memW u (globN u "bo" + 32),
      16 * memW u (globN u "bo" + 80) + 16) := by
    rcases hF.1 _ harr_fix with h0 | ⟨hal, _⟩
    · have h1 : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).2 =
          16 * memW u (globN u "bo" + 80) + 16 := rfl
      rw [h1] at h0
      omega
    · exact hal
  have harr_hi : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).1 +
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).2 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 harr_alloc).2
  have hp1 : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).1 =
      memW u (globN u "bo" + 32) := rfl
  have hp2 : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).2 =
      16 * memW u (globN u "bo" + 80) + 16 := rfl
  -- the bo global and the bo+32 cell
  obtain ⟨halloc_bo, hwords_bo⟩ := bo_words hF hE.bo_nz
  have hbo264 : globN u "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hAR.2 halloc_bo).2
  obtain ⟨bw, hgl, hbwn⟩ := p4Loop31_boWord hE.bo_nz (by omega)
  have hc20 : (0x0000000000000020#64 : BitVec 64).toNat = 32 := rfl
  have hc10 : (0x0000000000000010#64 : BitVec 64).toNat = 16 := rfl
  have hb32 : BitVec.ofNat 64 (globN u "bo" + 32) = bw + 0x0000000000000020#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hadd : (bw + 0x0000000000000020#64).toNat = bw.toNat + 32 := by
      rw [BitVec.toNat_add, hc20]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hadd, hbwn]
    exact Nat.mod_eq_of_lt (by omega)
  have hw32 : WordAt u (globN u "bo" + 32) := by
    have h4 : WordAt u (globN u "bo" + 8 * 4) := hwords_bo.2.2 4 (show 4 < 88 / 8 by decide)
    have heq : globN u "bo" + 8 * 4 = globN u "bo" + 32 := by ring
    rwa [heq] at h4
  obtain ⟨w32, hdom', hcell'⟩ := hw32
  rw [hb32] at hdom' hcell'
  -- the index local
  have hidxn : locN u "index" = idxw.toNat := by simp [locN, hidxl]
  have hidx_lt : idxw.toNat < memW u (globN u "bo" + 80) := by
    rw [← hidxn]; exact hE.idx_lt
  -- the evaluation
  have hcomp : evalAt u (.op .add [(.load .one (.op .add [.var .global (ofString "bo"),
      (.const 0x0000000000000020#64)])),
      (.panop .mul [(.var .local (ofString "index")),
        (.const 0x0000000000000010#64)])]) =
      some (.val (.word (w32 + idxw * 0x0000000000000010#64))) := by
    have hz1 : (0x0000000000000020#64 : BitVec 64) + 0 = 0x0000000000000020#64 :=
      BitVec.add_zero _
    have hz2 : (idxw * 0x0000000000000010#64 : BitVec 64) + 0 =
        idxw * 0x0000000000000010#64 := BitVec.add_zero _
    simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hgl, hidxl, valueIsWord,
      valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map, ↓reduceIte,
      List.foldr, BitVec.add_zero, Bool.and_self, memLoadHOLExact, isWfShapeExactHOL,
      hz1, hz2, hdom', hcell']
  have hval : (.val (.word (w32 + idxw * 0x0000000000000010#64)) : ValueHOL 64) = .val (.word x) :=
    Option.some.inj (hcomp.symm.trans hev)
  injection hval with h1
  injection h1 with h2
  subst h2
  -- the toNat arithmetic
  have hmul : (idxw * 0x0000000000000010#64 : BitVec 64).toNat = idxw.toNat * 16 := by
    rw [BitVec.toNat_mul, hc10]
    exact Nat.mod_eq_of_lt (by omega)
  have hw32n : w32.toNat = memW u (globN u "bo" + 32) := by
    unfold memW
    rw [hb32, hcell']
  rw [BitVec.toNat_add, hmul, hw32n, hidxn]
  omega

/-- The second slice store's destination evaluates to the same cell plus 8. -/
theorem p4O_encDstEval8 {F : Type} {u : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady u) {S Nd : List Nat} (hWT : WorldTypedWith u S Nd) (hE : TxEnv u)
    {idxw : BitVec 64} (hidxl : u.locals.lookup (ofString "index") = some (.val (.word idxw)))
    {x : BitVec 64}
    (hev : evalAt u (.op .add [(.load .one (.op .add [.var .global (ofString "bo"),
      (.const 0x0000000000000020#64)])),
      (.panop .mul [(.var .local (ofString "index")),
        (.const 0x0000000000000010#64)]),
      (.const 0x0000000000000008#64)]) = some (.val (.word x))) :
    x.toNat = memW u (globN u "bo" + 32) + 16 * locN u "index" + 8 := by
  -- the receipt-slices array is block-out element 1
  have hT : TablesTyped u S := hWT.1
  have hF : FixedTyped u := hWT.2.2.1
  have hbo7 := (blockOutObjects_eq_list hE hT).2.2
  have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo7]; rfl
  have hget1 : (blockOutObjects u)[1] =
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo7]
  have harr_mem : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := by
    have h := List.getElem_mem (l := blockOutObjects u) (n := 1)
      (h := by rw [hbo_len]; decide)
    rw [hget1] at h
    exact h
  have harr_fix := p4O_fixed_mem_blockOut harr_mem
  have harr_alloc : Allocated u (memW u (globN u "bo" + 32),
      16 * memW u (globN u "bo" + 80) + 16) := by
    rcases hF.1 _ harr_fix with h0 | ⟨hal, _⟩
    · have h1 : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).2 =
          16 * memW u (globN u "bo" + 80) + 16 := rfl
      rw [h1] at h0
      omega
    · exact hal
  have harr_hi : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).1 +
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).2 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 harr_alloc).2
  have hp1 : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).1 =
      memW u (globN u "bo" + 32) := rfl
  have hp2 : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).2 =
      16 * memW u (globN u "bo" + 80) + 16 := rfl
  -- the bo global and the bo+32 cell
  obtain ⟨halloc_bo, hwords_bo⟩ := bo_words hF hE.bo_nz
  have hbo264 : globN u "bo" + 88 ≤ 2 ^ 64 := (ivl_allocated_bound hAR.2 halloc_bo).2
  obtain ⟨bw, hgl, hbwn⟩ := p4Loop31_boWord hE.bo_nz (by omega)
  have hc20 : (0x0000000000000020#64 : BitVec 64).toNat = 32 := rfl
  have hc10 : (0x0000000000000010#64 : BitVec 64).toNat = 16 := rfl
  have hc8 : (0x0000000000000008#64 : BitVec 64).toNat = 8 := rfl
  have hb32 : BitVec.ofNat 64 (globN u "bo" + 32) = bw + 0x0000000000000020#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hadd : (bw + 0x0000000000000020#64).toNat = bw.toNat + 32 := by
      rw [BitVec.toNat_add, hc20]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hadd, hbwn]
    exact Nat.mod_eq_of_lt (by omega)
  have hw32 : WordAt u (globN u "bo" + 32) := by
    have h4 : WordAt u (globN u "bo" + 8 * 4) := hwords_bo.2.2 4 (show 4 < 88 / 8 by decide)
    have heq : globN u "bo" + 8 * 4 = globN u "bo" + 32 := by ring
    rwa [heq] at h4
  obtain ⟨w32, hdom', hcell'⟩ := hw32
  rw [hb32] at hdom' hcell'
  -- the index local
  have hidxn : locN u "index" = idxw.toNat := by simp [locN, hidxl]
  have hidx_lt : idxw.toNat < memW u (globN u "bo" + 80) := by
    rw [← hidxn]; exact hE.idx_lt
  -- the evaluation
  have hcomp : evalAt u (.op .add [(.load .one (.op .add [.var .global (ofString "bo"),
      (.const 0x0000000000000020#64)])),
      (.panop .mul [(.var .local (ofString "index")),
        (.const 0x0000000000000010#64)]),
      (.const 0x0000000000000008#64)]) =
      some (.val (.word (w32 + (idxw * 0x0000000000000010#64 + 0x0000000000000008#64)))) := by
    have hz1 : (0x0000000000000020#64 : BitVec 64) + 0 = 0x0000000000000020#64 :=
      BitVec.add_zero _
    have hz2 : (0x0000000000000008#64 : BitVec 64) + 0 = 0x0000000000000008#64 :=
      BitVec.add_zero _
    simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hgl, hidxl, valueIsWord,
      valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map, ↓reduceIte,
      List.foldr, BitVec.add_zero, Bool.and_self, memLoadHOLExact, isWfShapeExactHOL,
      hz1, hz2, hdom', hcell']
  have hval : (.val (.word (w32 + (idxw * 0x0000000000000010#64 +
      0x0000000000000008#64))) : ValueHOL 64) = .val (.word x) :=
    Option.some.inj (hcomp.symm.trans hev)
  injection hval with h1
  injection h1 with h2
  subst h2
  -- the toNat arithmetic
  have hmul : (idxw * 0x0000000000000010#64 : BitVec 64).toNat = idxw.toNat * 16 := by
    rw [BitVec.toNat_mul, hc10]
    exact Nat.mod_eq_of_lt (by omega)
  have hmul8 : (idxw * 0x0000000000000010#64 + 0x0000000000000008#64 : BitVec 64).toNat =
      idxw.toNat * 16 + 8 := by
    rw [BitVec.toNat_add, hmul, hc8]
    exact Nat.mod_eq_of_lt (by omega)
  have hw32n : w32.toNat = memW u (globN u "bo" + 32) := by
    unfold memW
    rw [hb32, hcell']
  rw [BitVec.toNat_add, hmul8, hw32n, hidxn]
  omega

/-! ## I. Instruction 24 (the receipt encoding) and the two slice stores -/

/-- The `bo+32` receipt-slices array field is the entry one. -/
theorem p4O_bo32_entry {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out) :
    memW s (globN s "bo" + 32) = memW entry (globN entry "bo" + 32) := by
  obtain ⟨⟨_, hbo_nz_e, _, _, _⟩, _, _, _, S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
  exact ptx_entry_bo_field_eq hWT_e h.base.globals h.base.records hbo_nz_e (by simp) (by omega)

/-- The second receipt store leaves the stored word in the current receipt
slice's length cell (stated against the entry `index`). -/
theorem p4O_rcptCur_of_store {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    {x b : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (h' : P4Data entry ({s with memory := mem'} : PanSemStateFiniteExact 64 F) s_pmc w_out)
    (hx_eq : x.toNat = memW s (globN s "bo" + 32) + 16 * locN s "index" + 8)
    (hval : mem' x = HolWordLab.word b) (hb : b.toNat < 2 ^ 40) :
    memW ({s with memory := mem'} : PanSemStateFiniteExact 64 F)
      (memW ({s with memory := mem'} : PanSemStateFiniteExact 64 F)
        (globN ({s with memory := mem'} : PanSemStateFiniteExact 64 F) "bo" + 32) +
        16 * locN entry "index" + 8) < 2 ^ 40 := by
  have h32 := p4O_bo32_entry h
  have h32' := p4O_bo32_entry h'
  have hidx : locN s "index" = locN entry "index" := by simp only [locN, h.idx_local]
  have haddr : memW ({s with memory := mem'} : PanSemStateFiniteExact 64 F)
      (globN ({s with memory := mem'} : PanSemStateFiniteExact 64 F) "bo" + 32) +
      16 * locN entry "index" + 8 = x.toNat := by
    rw [h32', hx_eq, h32, hidx]
  rw [haddr]
  have hcell : memW ({s with memory := mem'} : PanSemStateFiniteExact 64 F) x.toNat =
      b.toNat := by
    unfold memW
    dsimp only
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hval]
  omega

/-- Instructions 24-26: `dec rc := encode_receipt(tx[0], succeeded, bo[0x10],
logs)`, then the two receipt words are stored into the `bo+32` receipt-slices
array at `16 * index + {0, 8}`.  The logs-list facts (`LogsListOK` is given
by the 4D runner; `LogsDisjFixed` and the out/fresh disjunction are carried
across the callee by §G) survive both stores by `p4O_sliceStore_logs`. -/
theorem p4Run_g6 {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (succw wl : BitVec 64)
    (hsw : s.locals.lookup (ofString "succeeded") = some (.val (.word succw)))
    (hll : s.locals.lookup (ofString "logs") = some (.val (.word wl)))
    (hLL : LogsListOK s wl.toNat) (hDF : LogsDisjFixed s wl.toNat)
    (hdisj : wl.toNat = memW s (w_out.toNat + 16) ∨
      (memW s (wl.toNat) = wl.toNat + 24 ∧ memW s (wl.toNat + 8) = 0 ∧
        WordAt s (wl.toNat) ∧ WordAt s (wl.toNat + 8) ∧
        wl.toNat + 32 ≤ globN s "heap_ptr"))
    (rest : ProgHOL 64)
    (htail : ∀ (s' : PanSemStateFiniteExact 64 F) (wl' succw' : BitVec 64),
      P4Data entry s' s_pmc w_out →
      s'.code = originalRuntimeCode →
      s'.locals.lookup (ofString "logs") = some (.val (.word wl')) →
      s'.locals.lookup (ofString "succeeded") = some (.val (.word succw')) →
      LogsListOK s' wl'.toNat →
      LogsDisjFixed s' wl'.toNat →
      (wl'.toNat = memW s' (w_out.toNat + 16) ∨
        (memW s' (wl'.toNat) = wl'.toNat + 24 ∧
          memW s' (wl'.toNat + 8) = 0 ∧
          WordAt s' (wl'.toNat) ∧ WordAt s' (wl'.toNat + 8) ∧
          wl'.toNat + 32 ≤ globN s' "heap_ptr")) →
      memW s' (memW s' (globN s' "bo" + 32) + 16 * locN entry "index" + 8) < 2 ^ 40 →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.decCall (ofString "rc") (.comb [.one, .one]) (ofString "encode_receipt")
        [(.load .one (.op .add [(.var .local (ofString "tx")),
          (.const 0x0000000000000000#64)])),
         (.var .local (ofString "succeeded")),
         (.load .one (.op .add [(.var .global (ofString "bo")),
          (.const 0x0000000000000010#64)])),
         (.var .local (ofString "logs"))]
        (.seq (.store (.op .add [(.load .one (.op .add [.var .global (ofString "bo"),
          (.const 0x0000000000000020#64)])),
          (.panop .mul [(.var .local (ofString "index")),
            (.const 0x0000000000000010#64)])]) (.rfield 0 (.var .local (ofString "rc"))))
        (.seq (.store (.op .add [(.load .one (.op .add [.var .global (ofString "bo"),
          (.const 0x0000000000000020#64)])),
          (.panop .mul [(.var .local (ofString "index")),
            (.const 0x0000000000000010#64)]),
          (.const 0x0000000000000008#64)]) (.rfield 1 (.var .local (ofString "rc"))))
          rest))) s := by
  -- entry-side facts
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, hjcap_e, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, hTAL_OK⟩ := h.base.ready_entry
  have hTAL_e : TxAccessListAt entry S_e Nd_e (locN entry "tx") := hTAL_OK
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨S_c, N_c, hsub_c, hWT_c, hOG_c, hFO⟩ := h.base.typing S_e Nd_e hWT_e hD_e
  have hAR_e : ArenaReady entry := h.base.arena_entry
  have hgE : GuestInv entry := h.base.arena_entry.1
  have hgS : GuestInv s := h.base.world.1.1
  -- source-side world facts (for the callee transports)
  obtain ⟨S0, Nd0, hWT0, hE0, hAR0, hbo264_0⟩ := p4Head_boFacts h
  -- the tx local and the tx cell word
  obtain ⟨txw', htxl⟩ := h.shapes.1 "tx" (by simp)
  have htxl_e : entry.locals.lookup (ofString "tx") = some (.val (.word txw')) :=
    h.tx_local.symm.trans htxl
  have hle : locN entry "tx" = txw'.toNat := by simp [locN, htxl_e]
  have hle_lt : locN entry "tx" < 2 ^ 64 := by
    obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8f, ha9⟩ := hAR_e.2
    have hlim : heapLimit = scratchStart := by decide
    have hhl64 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
    have hlo := hTAL_e.1.2.1.1
    have hhi := hTAL_e.1.2.1.2
    omega
  have hround_tx : BitVec.ofNat 64 (locN entry "tx") = txw' := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hle]
    exact Nat.mod_eq_of_lt txw'.isLt
  obtain ⟨txw, htxdom', htxcell'⟩ := p4O_txWordAt hWT_e hTAL_e hAR_e hFO hgE hgS
  rw [hround_tx] at htxdom' htxcell'
  -- the bo+16 cell word (the third argument)
  obtain ⟨halloc_bo, hwords_bo⟩ := bo_words hWT0.2.2.1 hE0.bo_nz
  obtain ⟨bw, hgl, hbwn⟩ := p4Loop31_boWord hE0.bo_nz (by omega)
  have hc10 : (0x0000000000000010#64 : BitVec 64).toNat = 16 := rfl
  have hb16 : BitVec.ofNat 64 (globN s "bo" + 16) = bw + 0x0000000000000010#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hadd : (bw + 0x0000000000000010#64).toNat = bw.toNat + 16 := by
      rw [BitVec.toNat_add, hc10]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hadd, hbwn]
    exact Nat.mod_eq_of_lt (by omega)
  have hw16 : WordAt s (globN s "bo" + 16) := by
    have h2 : WordAt s (globN s "bo" + 8 * 2) := hwords_bo.2.2 2 (show 2 < 88 / 8 by decide)
    have heq : globN s "bo" + 8 * 2 = globN s "bo" + 16 := by ring
    rwa [heq] at h2
  obtain ⟨cgasw, hbod16, hboc16⟩ := hw16
  rw [hb16] at hbod16 hboc16
  -- the argument evaluation
  have harg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [(.load .one (.op .add [(.var .local (ofString "tx")),
        (.const 0x0000000000000000#64)])),
       (.var .local (ofString "succeeded")),
       (.load .one (.op .add [(.var .global (ofString "bo")),
        (.const 0x0000000000000010#64)])),
       (.var .local (ofString "logs"))] =
      some [.val (.word txw), .val (.word succw), .val (.word cgasw), .val (.word wl)] := by
    have hz1 : (0x0000000000000000#64 : BitVec 64) + 0 = 0x0000000000000000#64 :=
      BitVec.add_zero _
    have hz2 : txw' + (0x0000000000000000#64 : BitVec 64) = txw' := BitVec.add_zero _
    have hz3 : (0x0000000000000010#64 : BitVec 64) + 0 = 0x0000000000000010#64 :=
      BitVec.add_zero _
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact, evalHOLExact, htxl, hsw, hll, hgl, valueIsWord, valueWord,
      wordOpHOL, wordOp, List.all, List.map, Option.map, ↓reduceIte, List.foldr,
      BitVec.add_zero, Bool.and_self, memLoadHOLExact, isWfShapeExactHOL,
      htxdom', htxcell', hbod16, hboc16, hz1, hz2, hz3]
  -- the callee
  refine p4Run_decCall_encode_receipt h hc _ txw succw cgasw wl _ harg hLL hDF ?_
  intro a b mid ha61 hb61 hb40 hrc hlok heff hLLm hDm hcm
  -- the logs facts at mid (callee transports)
  have hDFm : LogsDisjFixed mid wl.toNat :=
    p4O_logsDisjFixed_callee hWT0 hE0 hAR0 heff hLL hDF
  have hdisjm := p4O_disj_callee hAR0 heff h hLL hDF hdisj
  -- store 1: the first receipt word
  refine p4Run_store _ _ _ ?_
  intro x1 v1 mem1 hed1 hes1 hmem1
  obtain ⟨Sm, Ndm, hWTm, hEm, hARm, hbo264m⟩ := p4Head_boFacts hDm
  obtain ⟨idxm, hidxlm⟩ := hDm.shapes.1 "index" (by simp)
  have hx1_eq : x1.toNat = memW mid (globN mid "bo" + 32) +
      16 * locN mid "index" + 0 := by
    have h0 := p4O_encDstEval hARm hWTm hEm hidxlm hed1
    omega
  have hv1 : v1 = .val (.word a) :=
    (Option.some.inj ((p4O_rcField0 hrc).symm.trans hes1)).symm
  have hflat1 : flattenHOL v1 = [HolWordLab.word a] := by rw [hv1]; simp [flattenHOL]
  rw [hflat1] at hmem1
  obtain ⟨hdom1, hval1, hm1⟩ := panMemStoresHOL_word_spec hmem1
  have hDm1 : P4Data entry ({mid with memory := mem1} : PanSemStateFiniteExact 64 F)
      s_pmc w_out :=
    p4Data_of_bo_slice_store hDm (hj := Or.inl rfl) hdom1 hx1_eq hm1
  obtain ⟨hLL1, hDF1, hdisj1⟩ := p4O_sliceStore_logs hDm hWTm hEm hARm (Or.inl rfl) hm1 hx1_eq
    hLLm hDFm hdisjm
  -- store 2: the second receipt word
  refine p4Run_store _ _ _ ?_
  intro x2 v2 mem2 hed2 hes2 hmem2
  obtain ⟨S2, Nd2, hWT2, hE2, hAR2, hbo264_2⟩ := p4Head_boFacts hDm1
  obtain ⟨idx2, hidxl2⟩ := hDm1.shapes.1 "index" (by simp)
  have hx2_eq : x2.toNat = memW ({mid with memory := mem1} : PanSemStateFiniteExact 64 F)
      (globN ({mid with memory := mem1} : PanSemStateFiniteExact 64 F) "bo" + 32) +
      16 * locN ({mid with memory := mem1} : PanSemStateFiniteExact 64 F) "index" + 8 :=
    p4O_encDstEval8 hAR2 hWT2 hE2 hidxl2 hed2
  have hv2 : v2 = .val (.word b) :=
    (Option.some.inj ((p4O_rcField1 hrc).symm.trans hes2)).symm
  have hflat2 : flattenHOL v2 = [HolWordLab.word b] := by rw [hv2]; simp [flattenHOL]
  rw [hflat2] at hmem2
  obtain ⟨hdom2, hval2, hm2⟩ := panMemStoresHOL_word_spec hmem2
  have hDm2 : P4Data entry ({{mid with memory := mem1} with memory := mem2} :
      PanSemStateFiniteExact 64 F) s_pmc w_out :=
    p4Data_of_bo_slice_store hDm1 (hj := Or.inr rfl) hdom2 hx2_eq hm2
  obtain ⟨hLL2, hDF2, hdisj2⟩ := p4O_sliceStore_logs hDm1 hWT2 hE2 hAR2 (Or.inr rfl) hm2 hx2_eq
    hLL1 hDF1 hdisj1
  -- the final tail
  have hllu2 : ({{mid with memory := mem1} with memory := mem2} :
      PanSemStateFiniteExact 64 F).locals.lookup (ofString "logs") =
      some (.val (.word wl)) := (hlok _ (by decide)).trans hll
  have hswu2 : ({{mid with memory := mem1} with memory := mem2} :
      PanSemStateFiniteExact 64 F).locals.lookup (ofString "succeeded") =
      some (.val (.word succw)) := (hlok _ (by decide)).trans hsw
  exact htail _ wl succw hDm2 hcm hllu2 hswu2 hLL2 hDF2 hdisj2
    (p4O_rcptCur_of_store hDm1 hDm2 hx2_eq hval2 hb40)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
