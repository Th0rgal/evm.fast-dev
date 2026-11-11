import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4H

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

/-! # Phase 4I: the loop-31 semantic cores

The isolated semantic facts that `p4Loop31_baseStored` and
`p4Run_loop31Engine` still need: the callee-global facts (`hsp`, `hfmp`,
`bo_eq`, heap growth, `ArenaReady post`), the `PtxBoCells`-assemblies for
the callee step and for the single-cell slot-store, the store-domain fact
(the `w`-argument), and the single-cell-store `ArenaReady` transport. -/

/-- The non-`heap_ptr` globals are kept across the lst_push callee, so the
scratch and frame pointers are in fact unchanged, `bo` is unchanged, the
heap grows and the callee's post state is arena-ready. -/
theorem p4Loop31_calleeGlobals {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w w_l : BitVec 64}
    (hcallee : WorldStep (fun _ => []) ["heap_ptr"] stdKeep RetListSlotStrong
      (callEntryStateHOLFinite u ((HolFiniteMapExact.empty.update
        (ofString "l", .val (.word w_l))).update (ofString "esz", .val (.word 8))))
      (some (.returned (.val (.word w)))) post) :
    globN post "scratch_ptr" ≤ globN u "scratch_ptr" ∧
    globN u "frame_mem_ptr" ≤ globN post "frame_mem_ptr" ∧
    globN post "bo" = globN u "bo" ∧
    globN u "heap_ptr" ≤ globN post "heap_ptr" ∧
    ArenaReady post := by
  have hstep := p4Loop31_calleeStepAtU hcallee
  have hsp : globN post "scratch_ptr" = globN u "scratch_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr")
      (by decide : ofString "scratch_ptr" ∉ ["heap_ptr"].map ofString))
  have hfmp : globN post "frame_mem_ptr" = globN u "frame_mem_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "frame_mem_ptr")
      (by decide : ofString "frame_mem_ptr" ∉ ["heap_ptr"].map ofString))
  have hbo : globN post "bo" = globN u "bo" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "bo")
      (by decide : ofString "bo" ∉ ["heap_ptr"].map ofString))
  exact ⟨le_of_eq hsp, le_of_eq hfmp.symm, hbo, hstep.2.1, hstep.1⟩

/-- Cell preservation under the callee's write-set shape: a cell address `k`
below `2^64` that misses the pushed list header and the free heap is
unchanged. -/
theorem p4Loop31_memW_of_miss {F : Type}
    {u post : PanSemStateFiniteExact 64 F} {w_l : BitVec 64} {k : Nat}
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) →
      post.memory a = u.memory a)
    (hk64 : k < 2 ^ 64)
    (h1 : ¬ CellHits k (w_l.toNat, 24))
    (h2 : ¬ CellHits k (InitECandidate.Solver.Wave8Contracts.M08.heapFree u)) :
    memW post k = memW u k := by
  have hw : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; omega
  unfold memW
  rw [hmem (BitVec.ofNat 64 k) (by rw [hw]; exact h1) (by rw [hw]; exact h2)]

/-- The loop-31 `hcells` core: the block-out cell facts across the lst_push
callee, assembled field by field from the preserved bo-cells and the
`w`-argument (the pushed slot lies at or above `sourceBase`, above the
list's old data, so the new data pointer is nonzero). -/
theorem p4Loop31_hcells {F : Type}
    {entry u post : PanSemStateFiniteExact 64 F} {w w_l : BitVec 64}
    (hbase : PtxRelBase true entry u)
    (hbo_eq : globN post "bo" = globN u "bo")
    (hl40 : w_l.toNat = memW u (globN u "bo" + 40))
    (hslot : w.toNat = memW post w_l.toNat + 8 * memW u (w_l.toNat + 8))
    (hw_ge : sourceBase ≤ w.toNat)
    (hlenb : 8 * memW u (w_l.toNat + 8) < sourceBase)
    (hbo_pres : ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN u "bo" + off) = memW u (globN u "bo" + off))
    (hl72_head : memW post (memW u (globN u "bo" + 72)) = memW u (memW u (globN u "bo" + 72)))
    (hl72_len : memW post (memW u (globN u "bo" + 72) + 8) =
      memW u (memW u (globN u "bo" + 72) + 8))
    (hslice_pres : ∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      memW post (memW u (globN u "bo" + off) + 16 * i + 8) =
        memW u (memW u (globN u "bo" + off) + 16 * i + 8)) :
    PtxBoCells true entry u post := by
  have hbo24 : memW post (globN u "bo" + 24) = memW u (globN u "bo" + 24) :=
    hbo_pres 24 (by decide)
  have hbo40 : memW post (globN u "bo" + 40) = memW u (globN u "bo" + 40) :=
    hbo_pres 40 (by decide)
  have hbo72 : memW post (globN u "bo" + 72) = memW u (globN u "bo" + 72) :=
    hbo_pres 72 (by decide)
  have hdata_nz : memW post w_l.toNat ≠ 0 := by omega
  refine ⟨hbo_eq, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbo_eq, hbo72, hl72_head]
    exact hbase.rcpt_backing
  · rw [hbo_eq, hbo40, ← hl40]
    exact hdata_nz
  · rw [hbo_eq, hbo72, hl72_len]
  · intro off hoff i hi
    have hoff' := hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff'
    rcases hoff' with rfl | rfl
    · rw [hbo_eq, hbo_pres 24 (by decide), hslice_pres 24 hoff i (Nat.le_of_lt hi)]
    · rw [hbo_eq, hbo_pres 32 (by decide), hslice_pres 32 hoff i (Nat.le_of_lt hi)]
  · intro _
    rw [hbo_eq, hbo24,
      hslice_pres 24 (by decide) (locN entry "index") (Nat.le_refl _)]
    exact hbase.tx_slice_cur rfl

/-- A successful single-word store at `a` needs `a` in the ordinary domain
and yields exactly the pointwise update function. -/
theorem p4Loop31_storeWordEff {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a : BitVec 64} {v : HolWordLab 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ a [v] s.memaddrs
      (fun address => Classical.propDecidable (s.memaddrs address)) s.memory = some mem') :
    s.memaddrs a ∧
    mem' = (fun current => if current = a then v else s.memory current) := by
  constructor
  · by_cases hdom : s.memaddrs a
    · exact hdom
    · simp only [panMemStoresHOL, panMemStoreHOL, if_neg hdom] at hst
      exact absurd hst (by simp)
  · simp only [panMemStoresHOL, panMemStoreHOL] at hst
    by_cases hdom : s.memaddrs a
    · rw [if_pos hdom] at hst
      exact (Option.some.inj hst).symm
    · rw [if_neg hdom] at hst
      exact absurd hst (by simp)

/-- The `w`-argument: an arena-ready state's ordinary domain starts at
`sourceBase`. -/
theorem p4Loop31_storeWArg {F : Type} {s : PanSemStateFiniteExact 64 F} {a : BitVec 64}
    (hAR : ArenaReady s) (hdom : s.memaddrs a) : sourceBase ≤ a.toNat := by
  have h1 : ordinaryDomain a := by
    rw [← hAR.1.memaddrs]; exact hdom
  exact ((ordinaryDomain_iff a).mp h1).2.1

/-- `ArenaReady` is invariant under single-cell memory updates. -/
theorem p4Loop31_arenaStored {F : Type} {s : PanSemStateFiniteExact 64 F}
    {mem' : RiscV.Word 64 → HolWordLab 64} (hAR : ArenaReady s) :
    ArenaReady {s with memory := mem'} :=
  ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, hAR.2⟩

/-- Cell preservation under a single-cell store: the cell at `k` survives
when its word address differs from the stored address. -/
theorem p4Loop31_memW_of_storeMiss {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {mem' : RiscV.Word 64 → HolWordLab 64} {k : Nat}
    (hmem' : ∀ a, a ≠ x → mem' a = s.memory a)
    (hk : BitVec.ofNat 64 k ≠ x) :
    memW {s with memory := mem'} k = memW s k := by
  have h1 : ({s with memory := mem'} : PanSemStateFiniteExact 64 F).memory
      (BitVec.ofNat 64 k) = mem' (BitVec.ofNat 64 k) := rfl
  unfold memW
  rw [h1, hmem' (BitVec.ofNat 64 k) hk]

/-- The loop-31 `hcells2` core: the block-out cell facts across the
single-cell slot-store, assembled from the preserved bo-cells (the stored
cell is the pushed slot, disjoint from all bo-record and list cells). -/
theorem p4Loop31_hcellsStore {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hb : PtxRelBase true entry s)
    (hmem' : ∀ a, a ≠ w → mem' a = s.memory a)
    (hmiss_bo : ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      BitVec.ofNat 64 (globN s "bo" + off) ≠ w)
    (hmiss_l72p : BitVec.ofNat 64 (memW s (globN s "bo" + 72)) ≠ w)
    (hmiss_l72len : BitVec.ofNat 64 (memW s (globN s "bo" + 72) + 8) ≠ w)
    (hmiss_l40 : BitVec.ofNat 64 (memW s (globN s "bo" + 40)) ≠ w)
    (hmiss_slices : ∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      BitVec.ofNat 64 (memW s (globN s "bo" + off) + 16 * i + 8) ≠ w) :
    PtxBoCells true entry s {s with memory := mem'} := by
  have hg : globN ({s with memory := mem'} : PanSemStateFiniteExact 64 F) "bo"
      = globN s "bo" := rfl
  have hbo72 : memW {s with memory := mem'} (globN s "bo" + 72) =
      memW s (globN s "bo" + 72) :=
    p4Loop31_memW_of_storeMiss hmem' (hmiss_bo 72 (by decide))
  have hbo24 : memW {s with memory := mem'} (globN s "bo" + 24) =
      memW s (globN s "bo" + 24) :=
    p4Loop31_memW_of_storeMiss hmem' (hmiss_bo 24 (by decide))
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg, hbo72, p4Loop31_memW_of_storeMiss hmem' hmiss_l72p]
    exact hb.rcpt_backing
  · rw [hg, p4Loop31_memW_of_storeMiss hmem' (hmiss_bo 40 (by decide)),
      p4Loop31_memW_of_storeMiss hmem' hmiss_l40]
    exact hb.log_backing
  · rw [hg, hbo72, p4Loop31_memW_of_storeMiss hmem' hmiss_l72len]
  · intro off hoff i hi
    have hoff' := hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff'
    rcases hoff' with rfl | rfl
    · rw [hg, p4Loop31_memW_of_storeMiss hmem' (hmiss_bo 24 (by decide)),
        p4Loop31_memW_of_storeMiss hmem' (hmiss_slices 24 hoff i (Nat.le_of_lt hi))]
    · rw [hg, p4Loop31_memW_of_storeMiss hmem' (hmiss_bo 32 (by decide)),
        p4Loop31_memW_of_storeMiss hmem' (hmiss_slices 32 hoff i (Nat.le_of_lt hi))]
  · intro _
    rw [hg, hbo24, p4Loop31_memW_of_storeMiss hmem'
      (hmiss_slices 24 (by decide) (locN entry "index") (Nat.le_refl _))]
    exact hb.tx_slice_cur rfl

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
