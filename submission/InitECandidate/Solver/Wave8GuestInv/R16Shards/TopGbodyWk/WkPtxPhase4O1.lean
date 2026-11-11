import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4N

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

/-! # Phase 4O: instruction 24 (the receipt encoding) and the two slice stores

`dec rc := encode_receipt(tx[0], succeeded, bo[0x10], logs)` runs the
receipt encoder (keccak writes only inside `keccak_pad`/`keccak_st`, the
heap pointer may grow), then the caller stores the two receipt words into
the `bo+32` receipt-slices array at `16 * index + {0, 8}`.

The two obligations beyond the 4D runner contract are the transport of the
logs-list facts (`LogsListOK`, `LogsDisjFixed`, the out-list/fresh-list
disjunction) from the entry state through the callee and the two stores to
the post state, and the `fixedObjects` stability needed for them.  The
Disj source is uniform: `LogsDisjFixed`'s interval list already separates
the list header, backing array and every owned log record from every
fixed object, and the store target interval is a block-out fixed object;
cell preservation for both steps therefore reduces to `Disj` case analysis
plus the arena bounds. -/

/-! ## A. Fixed-object membership helpers -/

/-- Every global-buffer slot of `globalBuffers` appears in `fixedObjects`
(as itself, or degenerate `(g, 0)` when the global is still `0`). -/
private theorem p4O_gbFixed {F : Type} (s : PanSemStateFiniteExact 64 F)
    {n : String} {sz : Nat} (h : (n, sz) ∈ globalBuffers) :
    (globN s n, if globN s n = 0 then 0 else sz) ∈ fixedObjects s := by
  unfold fixedObjects
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.mem_map.2 ⟨(n, sz), h, rfl⟩)))

/-- No global-buffer name prints as the string `"heap_ptr"`. -/
private theorem p4O_gb_no_hp : ∀ gn ∈ globalBuffers,
    (ofString gn.1 : MlS) ≠ ofString "heap_ptr" := by decide

/-- The keccak work intervals of receipt encoding are the two fixed buffers. -/
private theorem p4O_keccak_gbs {F : Type} (s : PanSemStateFiniteExact 64 F) {j : Ivl}
    (hj : j ∈ receiptKeccakIvls s) : j ∈
    (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
  simp only [receiptKeccakIvls, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact List.mem_map.2 ⟨("keccak_pad", 136), by decide, rfl⟩
  · exact List.mem_map.2 ⟨("keccak_st", 200), by decide, rfl⟩

/-- A keccak work interval is either degenerate `(0, 0)` or has its literal
size (`136` or `200`). -/
private theorem p4O_keccak_snd {F : Type} (s : PanSemStateFiniteExact 64 F) {j : Ivl}
    (hj : j ∈ receiptKeccakIvls s) :
    (j.2 = 0 ∧ j.1 = 0) ∨ j.2 = 136 ∨ j.2 = 200 := by
  simp only [receiptKeccakIvls, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · by_cases hg : globN s "keccak_pad" = 0
    · exact Or.inl ⟨by simp [hg], by simp [hg]⟩
    · exact Or.inr (Or.inl (by simp [hg]))
  · by_cases hg : globN s "keccak_st" = 0
    · exact Or.inl ⟨by simp [hg], by simp [hg]⟩
    · exact Or.inr (Or.inr (by simp [hg]))

/-- The keccak work intervals are fixed objects. -/
theorem p4O_keccak_fixed {F : Type} (s : PanSemStateFiniteExact 64 F) {j : Ivl}
    (hj : j ∈ receiptKeccakIvls s) : j ∈ fixedObjects s := by
  simp only [receiptKeccakIvls, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact p4O_gbFixed s (by decide)
  · exact p4O_gbFixed s (by decide)

/-- Fixed objects are owned by the world. -/
private theorem p4O_fixed_in_owned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (_hWT : WorldTypedWith s S Nd) {j : Ivl} (hj : j ∈ fixedObjects s) :
    j ∈ worldOwned s S Nd := by
  simp only [worldOwned, List.mem_append]
  exact Or.inl (Or.inr hj)

/-- A block-out element is a fixed object. -/
theorem p4O_fixed_mem_blockOut {F : Type} {s : PanSemStateFiniteExact 64 F}
    {i : Ivl} (h : i ∈ blockOutObjects s) : i ∈ fixedObjects s := by
  unfold fixedObjects
  simp only [List.mem_append]
  exact Or.inl (Or.inr h)

/-- A bal object is a fixed object. -/
private theorem p4O_fixed_mem_bal {F : Type} {s : PanSemStateFiniteExact 64 F}
    {i : Ivl} (h : i ∈ balObjects s) : i ∈ fixedObjects s := by
  unfold fixedObjects
  simp only [List.mem_append]
  exact Or.inr h

/-- Every ptx region is contained in a fixed object with the same start. -/
private theorem p4O_ptxRegions_fixed {F : Type} (s : PanSemStateFiniteExact 64 F)
    {i : Ivl} (hi : i ∈ ptxRegions s) :
    ∃ j ∈ fixedObjects s, i.1 = j.1 ∧ i.2 ≤ j.2 := by
  simp only [ptxRegions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact ⟨(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩
  · exact ⟨(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 64),
      p4O_gbFixed s (by decide), rfl, by split_ifs <;> omega⟩
  · exact ⟨(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640),
      p4O_gbFixed s (by decide), rfl, le_rfl⟩

/-- A degenerate ptx region has start `0`. -/
private theorem p4O_ptxRegions_zero_aligned {F : Type} (s : PanSemStateFiniteExact 64 F)
    {j : Ivl} (hj : j ∈ ptxRegions s) : j.2 = 0 → j.1 = 0 := by
  simp only [ptxRegions, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    intro hz <;> split_ifs at hz <;> simp_all

/-! ## B. The transaction cell transport -/

/-- A cell inside an aligned interval that is disjoint from `j` does not hit `j`.
(private copy of the R11 argument, avoiding the ambiguous name) -/
private theorem p4O_noHit {a : Nat} {i j : Ivl}
    (ha8 : a % 8 = 0) (hj0 : j.2 = 0 → j.1 % 8 = 0)
    (ha : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) (hd : Disj i j) :
    ¬ CellHits a j := by
  unfold Disj at hd
  unfold CellHits
  rcases hd with h | h | h | h
  · omega
  · have hj8 := hj0 h; omega
  · omega
  · omega

/-- The `tx` word cell at the entry is preserved into the G6-entry state:
the transaction header is disjoint from the world's owned intervals, the ptx
regions (each inside a fixed object with the same start) and both free
regions. -/
theorem p4O_txWordAt {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith entry S Nd)
    (hTAL : TxAccessListAt entry S Nd (locN entry "tx"))
    (hAR : ArenaReady entry)
    (hFO : FrameOutside entry s (worldOwned entry S Nd ++ ptxRegions entry ++ [freeGap entry])
      (heapFree entry))
    (hgE : GuestInv entry) (hgS : GuestInv s) :
    WordAt s (locN entry "tx") := by
  have htxe8 : (locN entry "tx") % 8 = 0 := hTAL.1.1.1
  have hz : 0 < (locN entry "tx", 384).2 / 8 := by simp
  have hw0 : WordAt entry (locN entry "tx") := by
    simpa using hTAL.1.1.2.2 0 hz
  obtain ⟨w, hdom_e, hcell_e⟩ := hw0
  have hlo : sourceBase ≤ locN entry "tx" := hTAL.1.2.1.1
  have hhi : locN entry "tx" + 384 ≤ globN entry "heap_ptr" := hTAL.1.2.1.2
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9⟩ := hAR.2
  have hlim : heapLimit = scratchStart := by decide
  have hhl64 : heapLimit ≤ 2 ^ 64 := by
    rw [WkBlockTxEnc.heapLimit_val]; decide
  have hta : (BitVec.ofNat 64 (locN entry "tx")).toNat = locN entry "tx" := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hself : (locN entry "tx", 384).1 ≤ locN entry "tx" ∧
      locN entry "tx" + 8 ≤ (locN entry "tx", 384).1 + (locN entry "tx", 384).2 := by
    have h1 : (locN entry "tx", 384).1 = locN entry "tx" := rfl
    have h2 : (locN entry "tx", 384).2 = 384 := rfl
    rw [h1, h2]
    exact ⟨le_rfl, by omega⟩
  refine ⟨w, ?_, ?_⟩
  · rw [hgS.memaddrs, ← hgE.memaddrs]
    exact hdom_e
  · have hcell : s.memory (BitVec.ofNat 64 (locN entry "tx")) =
        entry.memory (BitVec.ofNat 64 (locN entry "tx")) := by
      refine hFO (BitVec.ofNat 64 (locN entry "tx")) ?_ ?_
      · simp only [hta]
        intro j hj
        simp only [List.mem_append] at hj
        rcases hj with hj | hj
        · rcases hj with hj | hj
          · exact p4O_noHit (i := (locN entry "tx", 384)) htxe8
              (fun hz => worldOwned_zero_aligned hWT j hj hz) hself
              (hTAL.2.1 (locN entry "tx", 384) (List.mem_singleton.2 rfl) j hj)
          · obtain ⟨j', hj'mem, hj'eq1, hj'eq2⟩ := p4O_ptxRegions_fixed entry hj
            have hj'own : j' ∈ worldOwned entry S Nd := p4O_fixed_in_owned hWT hj'mem
            have hnc : ¬ CellHits (locN entry "tx") j' :=
              p4O_noHit (i := (locN entry "tx", 384)) htxe8
                (fun hz => worldOwned_zero_aligned hWT j' hj'own hz) hself
                (hTAL.2.1 (locN entry "tx", 384) (List.mem_singleton.2 rfl) j' hj'own)
            intro hcellj
            obtain ⟨hc1, hc2⟩ := hcellj
            exact hnc ⟨by omega, by omega⟩
        · simp only [List.mem_singleton] at hj
          subst hj
          have hfg1 : (freeGap entry).1 = globN entry "frame_mem_ptr" := rfl
          have hfg2 : (freeGap entry).2 =
              globN entry "scratch_ptr" - globN entry "frame_mem_ptr" := rfl
          unfold CellHits
          simp only [hfg1, hfg2]
          omega
      · simp only [hta]
        have hhf1 : (heapFree entry).1 = globN entry "heap_ptr" := rfl
        have hhf2 : (heapFree entry).2 = heapLimit - globN entry "heap_ptr" := rfl
        unfold CellHits
        simp only [hhf1, hhf2]
        omega
    rw [hcell]
    exact hcell_e

/-! ## C. The callee step -/

/-- `GuestInv` survives a memory update. -/
private theorem p4O_guestInv_mem {F : Type} {u : PanSemStateFiniteExact 64 F}
    {m : BitVec 64 → HolWordLab 64} (hgi : GuestInv u) : GuestInv {u with memory := m} := by
  obtain ⟨c, mm, sh, b⟩ := hgi
  exact ⟨c, mm, sh, b⟩

/-- An 8-byte cell inside an allocated interval that avoids the keccak work
intervals is preserved by the callee (keccak writes only there, or in the
free regions, which allocation rules out). -/
private theorem p4O_cellKept {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"])
    {iv : Ivl} (hal : Allocated s iv)
    (hdisj : ∀ j ∈ receiptKeccakIvls s, Disj iv j)
    {a : Nat} (h1 : iv.1 ≤ a) (h2 : a + 8 ≤ iv.1 + iv.2) :
    mid.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) := by
  have hhi := (ivl_allocated_bound hAR.2 hal).2
  by_contra hne
  have ha64 : a + 8 ≤ 2 ^ 64 := by omega
  have hta : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rcases heff.cell_frame (BitVec.ofNat 64 a) hne with
    ⟨j, hj, _, hc1, hc2⟩ | ⟨_, hc1, hc2⟩ | ⟨_, hc1, hc2⟩
  · rw [hta] at hc1 hc2
    rcases p4O_keccak_snd s hj with ⟨hz2, hz1⟩ | hz | hz
    · omega
    · rcases hdisj j hj with h | h | h | h <;> omega
    · rcases hdisj j hj with h | h | h | h <;> omega
  · obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9⟩ := hAR.2
    have hlim : heapLimit = scratchStart := by decide
    rw [hta] at hc1 hc2
    simp only [freeGap] at hc1 hc2
    rcases hal with ⟨hlo, hhi2⟩ | ⟨hlo, hhi2⟩ <;> omega
  · obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9⟩ := hAR.2
    have hlim : heapLimit = scratchStart := by decide
    rw [hta] at hc1 hc2
    simp only [heapFree] at hc1 hc2
    rcases hal with ⟨hlo, hhi2⟩ | ⟨hlo, hhi2⟩ <;> omega

theorem p4O_memW_kept {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"])
    {iv : Ivl} (hal : Allocated s iv)
    (hdisj : ∀ j ∈ receiptKeccakIvls s, Disj iv j)
    {a : Nat} (h1 : iv.1 ≤ a) (h2 : a + 8 ≤ iv.1 + iv.2) :
    memW mid a = memW s a := by
  have hcell := p4O_cellKept hAR heff hal hdisj h1 h2
  simp only [memW, hcell]

/-- An allocated, aligned interval that avoids the keccak work intervals is
fully unhit by the callee. -/
theorem p4O_ivlUnhit_callee {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"])
    {iv : Ivl} (hal : Allocated s iv) (hi1 : iv.1 % 8 = 0) (hi2 : iv.2 % 8 = 0)
    (hdisj : ∀ j ∈ receiptKeccakIvls s, Disj iv j) :
    IvlUnhit s mid iv := by
  intro a ha8 hcell
  obtain ⟨hc1, hc2⟩ := hcell
  have h1 : iv.1 ≤ a.toNat := by omega
  have h2 : a.toNat + 8 ≤ iv.1 + iv.2 := by omega
  have hround : BitVec.ofNat 64 a.toNat = a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt a.isLt
  rw [← hround]
  exact p4O_cellKept hAR heff hal hdisj h1 h2

/-- The `bo` record words survive the callee. -/
private theorem p4O_boCells_callee {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) (hE : TxEnv s) (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"]) :
    ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW mid (globN s "bo" + k) = memW s (globN s "bo" + k) := by
  obtain ⟨hbo_alloc, hbo_words⟩ := bo_words hWT.2.2.1 hE.bo_nz
  obtain ⟨hgbs, hbo_pw, hgb_rest, hjr_rest, hbo_bal⟩ := fixedObjects_disj_parts hWT.2.2.1
  have hbo_gbs : (globN s "bo", 88) ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  have hkec : ∀ j ∈ receiptKeccakIvls s, Disj (globN s "bo", 88) j := by
    intro j hj
    refine pairwise_disj_mem hgbs hbo_gbs (p4O_keccak_gbs s hj) ?_
    intro heq
    have h2 : (88 : Nat) = j.2 := congrArg Prod.snd heq
    rcases p4O_keccak_snd s hj with ⟨hz2, hz1⟩ | hz | hz <;> omega
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  have hbo1 : (globN s "bo", 88).1 = globN s "bo" := rfl
  have hbo2 : (globN s "bo", 88).2 = 88 := rfl
  have hle1 : (globN s "bo", 88).1 ≤ globN s "bo" + k := by
    rw [hbo1]
    omega
  have hle2 : globN s "bo" + k + 8 ≤ (globN s "bo", 88).1 + (globN s "bo", 88).2 := by
    rw [hbo1, hbo2]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact p4O_memW_kept hAR heff hbo_alloc hkec hle1 hle2

/-- The low cells 8 and 16 survive the callee (they lie below `sourceBase`). -/
private theorem p4O_memW_low_callee {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"]) :
    memW mid 8 = memW s 8 ∧ memW mid 16 = memW s 16 := by
  have hkey : ∀ k : Nat, k < 17 → mid.memory (BitVec.ofNat 64 k) = s.memory (BitVec.ofNat 64 k) := by
    intro k hk
    by_contra hne
    have hdom : s.memaddrs (BitVec.ofNat 64 k) := heff.out_dom _ hne
    have hord := (ordinaryDomain_iff (BitVec.ofNat 64 k)).mp (by
      rw [← hAR.1.memaddrs]; exact hdom)
    have hsb : 16 < sourceBase := by decide
    have htk : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [htk] at hord
    omega
  constructor
  · simp only [memW, hkey 8 (by decide)]
  · simp only [memW, hkey 16 (by decide)]

/-- `fixedObjects` is stable across the receipt-encoding callee. -/
theorem p4O_callee_fixed_eq {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) (hE : TxEnv s) (hAR : ArenaReady s)
    (heff : HeapByteEff s mid (receiptKeccakIvls s) ["heap_ptr"]) :
    fixedObjects mid = fixedObjects s := by
  have hT : TablesTyped s S := hWT.1
  have hF : FixedTyped s := hWT.2.2.1
  obtain ⟨hgbs, hbo_pw, hgb_rest, hjr_rest, hbo_bal⟩ := fixedObjects_disj_parts hF
  have hbo_gbs : (globN s "bo", 88) ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  -- keccak-vs-bo disjointness
  have hkec : ∀ j ∈ receiptKeccakIvls s, Disj (globN s "bo", 88) j := by
    intro j hj
    refine pairwise_disj_mem hgbs hbo_gbs (p4O_keccak_gbs s hj) ?_
    intro heq
    have h2 : (88 : Nat) = j.2 := congrArg Prod.snd heq
    rcases p4O_keccak_snd s hj with ⟨hz2, hz1⟩ | hz | hz <;> omega
  have hbo_cells : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW mid (globN s "bo" + k) = memW s (globN s "bo" + k) :=
    p4O_boCells_callee hWT hE hAR heff
  have hbo_eq : globN mid "bo" = globN s "bo" :=
    globN_eq_of_lookup (heff.globals (ofString "bo") (by decide))
  have hba_eq : globN mid "bal_accounts" = globN s "bal_accounts" :=
    globN_eq_of_lookup (heff.globals (ofString "bal_accounts") (by decide))
  have hgb_all : ∀ gn ∈ globalBuffers, globN mid gn.1 = globN s gn.1 := by
    intro gn hgn
    refine globN_eq_of_lookup (heff.globals (ofString gn.1) ?_)
    intro hmem
    obtain ⟨y, hy, hye⟩ := List.mem_map.mp hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    exact p4O_gb_no_hp gn hgn hye.symm
  -- the two list headers as fixed objects
  have hbo7 := (blockOutObjects_eq_list hE hT).2.2
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo7]; rfl
  have hget3 : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by
    simp [hbo7]
  have hget5 : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by
    simp [hbo7]
  have hl40_mem : (memW s (globN s "bo" + 40), 24) ∈ blockOutObjects s := by
    have h := List.getElem_mem (l := blockOutObjects s) (n := 3)
      (h := by rw [hbo_len]; decide)
    rw [hget3] at h
    exact h
  have hl72_mem : (memW s (globN s "bo" + 72), 24) ∈ blockOutObjects s := by
    have h := List.getElem_mem (l := blockOutObjects s) (n := 5)
      (h := by rw [hbo_len]; decide)
    rw [hget5] at h
    exact h
  have hfix_mem : ∀ i : Ivl, i ∈ blockOutObjects s → i ∈ fixedObjects s :=
    fun i hi => p4O_fixed_mem_blockOut hi
  have hbal_mem : ∀ i : Ivl, i ∈ balObjects s → i ∈ fixedObjects s :=
    fun i hi => p4O_fixed_mem_bal hi
  -- allocated-and-aligned facts for the headers and bal objects
  have hfix_props : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → Allocated s i ∧ WordsOK s i := by
    intro i hi hnz
    rcases hF.1 i hi with h0 | hprops
    · exact absurd h0 (by omega)
    · exact hprops
  have hhl40 : Allocated s (memW s (globN s "bo" + 40), 24) ∧ WordsOK s (memW s (globN s "bo" + 40), 24) :=
    hfix_props _ (hfix_mem _ hl40_mem) (by simp)
  have hhl72 : Allocated s (memW s (globN s "bo" + 72), 24) ∧ WordsOK s (memW s (globN s "bo" + 72), 24) :=
    hfix_props _ (hfix_mem _ hl72_mem) (by simp)
  -- Disj vs keccak for block-out and bal objects via the gb separation
  have hbojr_mem : ∀ i : Ivl, i ∈ blockOutObjects s →
      i ∈ [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
        32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s := by
    intro i hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl (Or.inr hi)
  have hbaljr_mem : ∀ i : Ivl, i ∈ balObjects s →
      i ∈ [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
        32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s := by
    intro i hi
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr hi
  have hdisj_kec_bo : ∀ i : Ivl, i ∈ blockOutObjects s →
      ∀ j ∈ receiptKeccakIvls s, Disj i j := by
    intro i hi j hj
    exact (hgb_rest j (p4O_keccak_gbs s hj) i (hbojr_mem i hi)).flip
  have hdisj_kec_bal : ∀ i : Ivl, i ∈ balObjects s →
      ∀ j ∈ receiptKeccakIvls s, Disj i j := by
    intro i hi j hj
    exact (hgb_rest j (p4O_keccak_gbs s hj) i (hbaljr_mem i hi)).flip
  -- the keccak Disj side conditions for the two headers
  have hbo_lst : globN s "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
      memW s (globN s "bo" + k) ≠ 0 → LstOK s (memW s (globN s "bo" + k)) :=
    hT.2.2.2.2.2.2.2.2.2.2.1
  have hl40 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 40) ≠ 0 →
      IvlUnhit s mid (memW s (globN s "bo" + 40), 24) := by
    intro _ _
    exact p4O_ivlUnhit_callee hAR heff hhl40.1 hhl40.2.1 hhl40.2.2.1
      (hdisj_kec_bo _ hl40_mem)
  have hl72 : globN s "bo" ≠ 0 → memW s (globN s "bo" + 72) ≠ 0 →
      IvlUnhit s mid (memW s (globN s "bo" + 72), 24) := by
    intro _ _
    exact p4O_ivlUnhit_callee hAR heff hhl72.1 hhl72.2.1 hhl72.2.2.1
      (hdisj_kec_bo _ hl72_mem)
  -- the tables' footprints and the bal objects are unhit
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s mid i := by
    intro t ht i hi
    obtain ⟨hal_i, hdisj_i⟩ := (hT.2.1 t ht).2 i hi
    have hwsk : WordsOK s i := ((hT.2.1 t ht).1.1 i hi).2
    exact p4O_ivlUnhit_callee hAR heff hal_i hwsk.1 hwsk.2.1
      (fun j hj => hdisj_i j (p4O_keccak_fixed s hj))
  have hu_bal : ∀ i ∈ balObjects s, IvlUnhit s mid i := by
    intro i hi
    rcases hF.1 i (p4O_fixed_mem_bal hi) with h0 | ⟨hal_i, hw_i⟩
    · have hiz : i.1 = 0 := fixedObjects_zero_aligned i (p4O_fixed_mem_bal hi) h0
      intro a ha8 hcell
      obtain ⟨_, hc2⟩ := hcell
      exact absurd hc2 (by omega)
    · exact p4O_ivlUnhit_callee hAR heff hal_i hw_i.1 hw_i.2.1 (hdisj_kec_bal i hi)
  have hm_low := p4O_memW_low_callee hAR heff
  -- assemble
  have hbo_part := blockOutObjects_eq_of_bo_same hAR.2 hF hbo_eq hbo_lst
    (fun _ => hbo_cells) hl40 hl72
  have hbal_part := balObjects_eq_of_same_globals hAR.2 hT hF hba_eq hm_low hu_tab hu_bal
  have hg_jr : globN mid "journal" = globN s "journal" :=
    globN_eq_of_lookup (heff.globals (ofString "journal") (by decide))
  have hg_jc : globN mid "journal_cap" = globN s "journal_cap" :=
    globN_eq_of_lookup (heff.globals (ofString "journal_cap") (by decide))
  have hmap : (globalBuffers.map fun gn =>
      (globN mid gn.1, if globN mid gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn =>
      (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn hgn
    rw [hgb_all gn hgn]
  unfold fixedObjects
  rw [hbo_part.1, hbal_part.2.1, hg_jr, hg_jc, hmap]

/-! ## D. The store step -/

/-- `IvlUnhit` composes along memory-preserving steps. -/
private theorem p4O_ivlUnhit_trans {F : Type} {s u post : PanSemStateFiniteExact 64 F}
    {iv : Ivl} (h1 : IvlUnhit s u iv) (h2 : IvlUnhit u post iv) : IvlUnhit s post iv := by
  intro a ha8 hcell
  rw [h2 a ha8 hcell, h1 a ha8 hcell]

/-- `Inside` from plain bounds (avoids pair projections reaching `omega`). -/
private theorem p4O_inside_of {a b lo hi : Nat} (h1 : lo ≤ a) (h2 : a + b ≤ hi) :
    Inside (a, b) lo hi := ⟨h1, h2⟩

/-- The low cells 8 and 16 survive a receipt-slice store (the target lies at
or above the `bo` record, hence above `sourceBase`). -/
private theorem p4O_memW_low_store {F : Type} {u : PanSemStateFiniteExact 64 F}
    {mem' : BitVec 64 → HolWordLab 64} {x : BitVec 64}
    (hm : ∀ a, a ≠ x → mem' a = u.memory a)
    (hx_low : 16 < x.toNat) :
    memW {u with memory := mem'} 8 = memW u 8 ∧ memW {u with memory := mem'} 16 = memW u 16 := by
  have hkey : ∀ k : Nat, k < 17 → mem' (BitVec.ofNat 64 k) = u.memory (BitVec.ofNat 64 k) := by
    intro k hk
    refine hm _ ?_
    intro heq
    have h1 : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have h2 : k = x.toNat := by
      have h3 := congrArg BitVec.toNat heq
      rw [h1] at h3
      exact h3
    omega
  constructor
  · simp only [memW, hkey 8 (by decide)]
  · simp only [memW, hkey 16 (by decide)]

/-- `fixedObjects` is stable across a receipt-slice store. -/
private theorem p4O_store_fixed_eq {F : Type} {u : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith u S Nd) (hE : TxEnv u) (hAR : ArenaReady u)
    {j : Nat} (hj : j = 0 ∨ j = 8)
    {mem' : BitVec 64 → HolWordLab 64} {x : BitVec 64}
    (hm : ∀ a, a ≠ x → mem' a = u.memory a)
    (hx_eq : x.toNat = memW u (globN u "bo" + 32) + 16 * locN u "index" + j) :
    fixedObjects {u with memory := mem'} = fixedObjects u := by
  have hT : TablesTyped u S := hWT.1
  have hF : FixedTyped u := hWT.2.2.1
  obtain ⟨hgbs, hbo_pw, hgb_rest, hjr_rest, hbo_bal⟩ := fixedObjects_disj_parts hF
  -- the receipt-slices array is block-out element 1
  have hbo7 := (blockOutObjects_eq_list hE hT).2.2
  have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo7]; rfl
  have hget1 : (blockOutObjects u)[1] =
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo7]
  have hget3 : (blockOutObjects u)[3] = (memW u (globN u "bo" + 40), 24) := by
    simp [hbo7]
  have hget5 : (blockOutObjects u)[5] = (memW u (globN u "bo" + 72), 24) := by
    simp [hbo7]
  have harr_mem : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := by
    have h := List.getElem_mem (l := blockOutObjects u) (n := 1)
      (h := by rw [hbo_len]; decide)
    rw [hget1] at h
    exact h
  have hl40_mem : (memW u (globN u "bo" + 40), 24) ∈ blockOutObjects u := by
    have h := List.getElem_mem (l := blockOutObjects u) (n := 3)
      (h := by rw [hbo_len]; decide)
    rw [hget3] at h
    exact h
  have hl72_mem : (memW u (globN u "bo" + 72), 24) ∈ blockOutObjects u := by
    have h := List.getElem_mem (l := blockOutObjects u) (n := 5)
      (h := by rw [hbo_len]; decide)
    rw [hget5] at h
    exact h
  have harr_fix := p4O_fixed_mem_blockOut harr_mem
  -- the store cell lies inside the array
  have hidx := hE.idx_lt
  have hin : Inside (x.toNat, 8) (memW u (globN u "bo" + 32))
      (memW u (globN u "bo" + 32) + 16 * memW u (globN u "bo" + 80) + 16) :=
    p4O_inside_of (by omega) (by omega)
  -- every interval disjoint from the array is unhit by the store
  have hu_of : ∀ i : Ivl, (i.2 = 0 → i.1 % 8 = 0) →
      Disj i (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) →
      IvlUnhit u {u with memory := mem'} i := by
    intro i hi0 hd
    exact ivlUnhit_single hm hi0 (disj_of_inside_right hin hd)
  -- Disj sources against the array
  have hbo_gbs : (globN u "bo", 88) ∈
      (globalBuffers.map fun gn => (globN u gn.1, if globN u gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  have harr_bojr : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) ∈
      [(if globN u "journal_cap" = 0 then 0 else globN u "journal",
        32 * globN u "journal_cap")] ++ blockOutObjects u ++ balObjects u := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl (Or.inr harr_mem)
  have hdisj_bo_arr : Disj (globN u "bo", 88)
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) :=
    hgb_rest _ hbo_gbs _ harr_bojr
  have hdisj_l40_arr : Disj (memW u (globN u "bo" + 40), 24)
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) :=
    pairwise_disj_mem hbo_pw hl40_mem harr_mem (by
      intro heq
      have h2 : (24 : Nat) = 16 * memW u (globN u "bo" + 80) + 16 := congrArg Prod.snd heq
      omega)
  have hdisj_l72_arr : Disj (memW u (globN u "bo" + 72), 24)
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) :=
    pairwise_disj_mem hbo_pw hl72_mem harr_mem (by
      intro heq
      have h2 : (24 : Nat) = 16 * memW u (globN u "bo" + 80) + 16 := congrArg Prod.snd heq
      omega)
  -- the bo record
  have hbo_words' := bo_words hF hE.bo_nz
  have hbo1 : (globN u "bo", 88).1 = globN u "bo" := rfl
  have hbo2 : (globN u "bo", 88).2 = 88 := rfl
  have hu_bo : IvlUnhit u {u with memory := mem'} (globN u "bo", 88) :=
    hu_of _ (fun hz => absurd hz (by simp)) hdisj_bo_arr
  have hhi_bo := (ivl_allocated_bound hAR.2 hbo_words'.1).2
  have hk : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW {u with memory := mem'} (globN u "bo" + k) = memW u (globN u "bo" + k) := by
    intro k hkmem
    have hbo8 : (globN u "bo") % 8 = 0 := hbo_words'.2.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkmem
    rcases hkmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact memW_eq_of_ivlUnhit hu_bo (by omega) hhi_bo
        (by rw [hbo1, hbo2]; omega)
  -- the two list headers
  have hl40 : globN u "bo" ≠ 0 → memW u (globN u "bo" + 40) ≠ 0 →
      IvlUnhit u {u with memory := mem'} (memW u (globN u "bo" + 40), 24) :=
    fun _ _ => hu_of _ (fun hz => absurd hz (by simp)) hdisj_l40_arr
  have hl72 : globN u "bo" ≠ 0 → memW u (globN u "bo" + 72) ≠ 0 →
      IvlUnhit u {u with memory := mem'} (memW u (globN u "bo" + 72), 24) :=
    fun _ _ => hu_of _ (fun hz => absurd hz (by simp)) hdisj_l72_arr
  -- the tables' footprints
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint u t, IvlUnhit u {u with memory := mem'} i := by
    intro t ht i hi
    obtain ⟨hal_i, hdisj_i⟩ := (hT.2.1 t ht).2 i hi
    have hwsk : WordsOK u i := ((hT.2.1 t ht).1.1 i hi).2
    exact hu_of _ (fun _ => hwsk.1) (hdisj_i _ harr_fix)
  -- the bal objects
  have hu_bal : ∀ i ∈ balObjects u, IvlUnhit u {u with memory := mem'} i := by
    intro i hi
    rcases hF.1 i (p4O_fixed_mem_bal hi) with h0 | ⟨hal_i, hw_i⟩
    · have hiz : i.1 = 0 := fixedObjects_zero_aligned i (p4O_fixed_mem_bal hi) h0
      intro a ha8 hcell
      obtain ⟨_, hc2⟩ := hcell
      exact absurd hc2 (by omega)
    · exact hu_of _ (fun _ => hw_i.1) (disj_symm (hbo_bal _ harr_mem i hi))
  -- the low cells
  have harr_alloc : Allocated u (memW u (globN u "bo" + 32),
      16 * memW u (globN u "bo" + 80) + 16) := by
    rcases hF.1 _ harr_fix with h0 | ⟨hal, _⟩
    · have h1 : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16).2 =
          16 * memW u (globN u "bo" + 80) + 16 := rfl
      rw [h1] at h0
      omega
    · exact hal
  have hx_low : 16 < x.toNat := by
    have hsb : 16 < sourceBase := by decide
    have hss : sourceBase ≤ scratchStart := by decide
    obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8f, ha9⟩ := hAR.2
    rcases harr_alloc with ⟨h1, _⟩ | ⟨h1, _⟩
    · have h1' : sourceBase ≤ memW u (globN u "bo" + 32) := h1
      omega
    · have h1' : globN u "scratch_ptr" ≤ memW u (globN u "bo" + 32) := h1
      omega
  have hm_low : memW {u with memory := mem'} 8 = memW u 8 ∧
      memW {u with memory := mem'} 16 = memW u 16 :=
    p4O_memW_low_store hm hx_low
  -- globals are untouched by a memory-only store
  have hbo_eq : globN {u with memory := mem'} "bo" = globN u "bo" := rfl
  have hba_eq : globN {u with memory := mem'} "bal_accounts" = globN u "bal_accounts" := rfl
  have hbo_lst : globN u "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
      memW u (globN u "bo" + k) ≠ 0 → LstOK u (memW u (globN u "bo" + k)) :=
    hT.2.2.2.2.2.2.2.2.2.2.1
  have hbo_part := blockOutObjects_eq_of_bo_same hAR.2 hF hbo_eq hbo_lst
    (fun _ => hk) hl40 hl72
  have hbal_part := balObjects_eq_of_same_globals hAR.2 hT hF hba_eq hm_low hu_tab hu_bal
  have hmap : (globalBuffers.map fun gn =>
      (globN {u with memory := mem'} gn.1,
        if globN {u with memory := mem'} gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn =>
      (globN u gn.1, if globN u gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn _
    rfl
  have hg_jr : globN {u with memory := mem'} "journal" = globN u "journal" := rfl
  have hg_jc : globN {u with memory := mem'} "journal_cap" = globN u "journal_cap" := rfl
  unfold fixedObjects
  rw [hbo_part.1, hbal_part.2.1, hg_jr, hg_jc, hmap]

/-! ## E. Evaluation recipes -/

theorem p4O_evalWord_eq {F : Type} {u : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {w1 w2 : BitVec 64} (h1 : evalAt u e = some (.val (.word w1)))
    (h2 : evalAt u e = some (.val (.word w2))) : w1 = w2 := by
  rw [h1] at h2
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at h2
  exact h2

/-- The receipt struct fields evaluate to the returned words. -/
theorem p4O_rcField0 {F : Type} {mid : PanSemStateFiniteExact 64 F} {a b : BitVec 64}
    (hloc : mid.locals.lookup (ofString "rc") =
      some (.rStruct [.val (.word a), .val (.word b)])) :
    evalAt mid (.rfield 0 (.var .local (ofString "rc"))) = some (.val (.word a)) := by
  simp only [evalAt, evalHOLExact, hloc, valueIsWord, valueWord, List.getElem?_cons_succ,
    List.getElem?_cons_zero]

theorem p4O_rcField1 {F : Type} {mid : PanSemStateFiniteExact 64 F} {a b : BitVec 64}
    (hloc : mid.locals.lookup (ofString "rc") =
      some (.rStruct [.val (.word a), .val (.word b)])) :
    evalAt mid (.rfield 1 (.var .local (ofString "rc"))) = some (.val (.word b)) := by
  simp only [evalAt, evalHOLExact, hloc, valueIsWord, valueWord, List.getElem?_cons_succ,
    List.getElem?_cons_zero]

/-! ## F. Logs-fact transports across the slice stores -/

/-- A cell of an interval disjoint from the store-target array differs from
the store target. -/
private theorem p4O_cellNe_store {iv arr : Ivl} {x a : Nat}
    (hdisj : Disj iv arr) (hxin : arr.1 ≤ x ∧ x + 8 ≤ arr.1 + arr.2)
    (h1 : iv.1 ≤ a) (h2 : a + 8 ≤ iv.1 + iv.2) : a ≠ x := by
  intro heq
  subst heq
  unfold Disj at hdisj
  rcases hdisj with h0 | h0 | h0 | h0 <;> omega

/-- The store cell differs from every aligned cell of an interval disjoint
from the store-target array. -/
private theorem p4O_ofNat_ne_store {iv arr : Ivl} {x : BitVec 64} {a : Nat}
    (hdisj : Disj iv arr) (hxin : arr.1 ≤ x.toNat ∧ x.toNat + 8 ≤ arr.1 + arr.2)
    (h1 : iv.1 ≤ a) (h2 : a + 8 ≤ iv.1 + iv.2) (ha64 : a < 2 ^ 64) :
    BitVec.ofNat 64 a ≠ x := by
  intro heq
  have h3 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64] at h3
  exact p4O_cellNe_store hdisj hxin h1 h2 h3

/-- A word cell of an interval disjoint from the store-target array survives
the store (no cell alignment needed). -/
private theorem p4O_memW_store {F : Type} {u : PanSemStateFiniteExact 64 F}
    {mem' : BitVec 64 → HolWordLab 64} {x : BitVec 64}
    (hm : ∀ a, a ≠ x → mem' a = u.memory a)
    {iv arr : Ivl} (hdisj : Disj iv arr)
    (hxin : arr.1 ≤ x.toNat ∧ x.toNat + 8 ≤ arr.1 + arr.2)
    {a : Nat} (h1 : iv.1 ≤ a) (h2 : a + 8 ≤ iv.1 + iv.2) (ha64 : a < 2 ^ 64) :
    memW {u with memory := mem'} a = memW u a := by
  have hcell : mem' (BitVec.ofNat 64 a) = u.memory (BitVec.ofNat 64 a) :=
    hm _ (p4O_ofNat_ne_store hdisj hxin h1 h2 ha64)
  simp only [memW, hcell]

private theorem p4O_wordAt_store {F : Type} {u : PanSemStateFiniteExact 64 F}
    {mem' : BitVec 64 → HolWordLab 64} {x : BitVec 64}
    (hm : ∀ a, a ≠ x → mem' a = u.memory a)
    {iv arr : Ivl} (hdisj : Disj iv arr)
    (hxin : arr.1 ≤ x.toNat ∧ x.toNat + 8 ≤ arr.1 + arr.2)
    {a : Nat} (h1 : iv.1 ≤ a) (h2 : a + 8 ≤ iv.1 + iv.2) (ha64 : a < 2 ^ 64)
    (hw : WordAt u a) : WordAt {u with memory := mem'} a := by
  obtain ⟨w, hdom, hcell⟩ := hw
  have heq : ({u with memory := mem'}).memory (BitVec.ofNat 64 a) =
      u.memory (BitVec.ofNat 64 a) :=
    hm _ (p4O_ofNat_ne_store hdisj hxin h1 h2 ha64)
  exact ⟨w, hdom, by rw [heq]; exact hcell⟩

/-- The low cells below `sourceBase` survive the store. -/
private theorem p4O_memLow_store {F : Type} {u : PanSemStateFiniteExact 64 F}
    {mem' : BitVec 64 → HolWordLab 64} {x : BitVec 64}
    (hm : ∀ a, a ≠ x → mem' a = u.memory a)
    (hx_low : 16 < x.toNat) {c : Nat} (hc : c < 17) :
    mem' (BitVec.ofNat 64 c) = u.memory (BitVec.ofNat 64 c) := by
  refine hm _ ?_
  intro heq
  have h1 : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h3 := congrArg BitVec.toNat heq
  rw [h1] at h3
  omega

private theorem p4O_memW_low_store' {F : Type} {u : PanSemStateFiniteExact 64 F}
    {mem' : BitVec 64 → HolWordLab 64} {x : BitVec 64}
    (hm : ∀ a, a ≠ x → mem' a = u.memory a)
    (hx_low : 16 < x.toNat) {c : Nat} (hc : c < 17) :
    memW {u with memory := mem'} c = memW u c := by
  simp only [memW, p4O_memLow_store hm hx_low hc]

private theorem p4O_wordAt_low_store' {F : Type} {u : PanSemStateFiniteExact 64 F}
    {mem' : BitVec 64 → HolWordLab 64} {x : BitVec 64}
    (hm : ∀ a, a ≠ x → mem' a = u.memory a)
    (hx_low : 16 < x.toNat) {c : Nat} (hc : c < 17) (hw : WordAt u c) :
    WordAt {u with memory := mem'} c := by
  obtain ⟨w, hdom, hcell⟩ := hw
  have heq : ({u with memory := mem'}).memory (BitVec.ofNat 64 c) =
      u.memory (BitVec.ofNat 64 c) := p4O_memLow_store hm hx_low hc
  exact ⟨w, hdom, by rw [heq]; exact hcell⟩

/-- Interval-cell bounds (pair projections are opaque to `omega`). -/
theorem p4O_cellIn {a n c : Nat} (hc : c + 8 ≤ n) :
    (a, n).1 ≤ a + c ∧ a + c + 8 ≤ (a, n).1 + (a, n).2 := by
  have h1 : (a, n).1 = a := rfl
  have h2 : (a, n).2 = n := rfl
  omega

/-- The out record is disjoint from every fixed object: `logs_facts`
separates it from the whole owned world, and fixed objects are owned. -/
theorem p4O_out_disj {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out) :
    ∀ j ∈ fixedObjects s, Disj (w_out.toNat, 96) j := by
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := h.base.ready_entry
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  obtain ⟨logs, _, _, _, hty⟩ := h.logs_facts
  obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, _, _, hWT_s, _, _, _, hty7, _, _⟩ :=
    hty S_e Nd_e hWT_e hD_e
  exact fun j hj => hty7 j (p4O_fixed_in_owned hWT_s hj)

/-- The logs facts survive a receipt-slice store.  The store target is a cell
of the receipt-slices array (the block-out fixed object at `bo+32`), and
`LogsDisjFixed` separates every logs interval from every fixed object, so
the list header, the backing-array cells and every owned log record survive;
`fixedObjects` is stable by `p4O_store_fixed_eq`, so the same `Disj` facts
hold at the post state. -/
theorem p4O_sliceStore_logs {F : Type}
    {entry u s_pmc : PanSemStateFiniteExact 64 F} {w_out wl : BitVec 64}
    (hD : P4Data entry u s_pmc w_out)
    {S Nd : List Nat} (hWT : WorldTypedWith u S Nd) (hE : TxEnv u) (hAR : ArenaReady u)
    {j : Nat} (hj : j = 0 ∨ j = 8)
    {mem' : BitVec 64 → HolWordLab 64} {x : BitVec 64}
    (hm : ∀ a, a ≠ x → mem' a = u.memory a)
    (hx_eq : x.toNat = memW u (globN u "bo" + 32) + 16 * locN u "index" + j)
    (hLL : LogsListOK u wl.toNat) (hDF : LogsDisjFixed u wl.toNat)
    (hdisj : wl.toNat = memW u (w_out.toNat + 16) ∨
      (memW u (wl.toNat) = wl.toNat + 24 ∧ memW u (wl.toNat + 8) = 0 ∧
        WordAt u (wl.toNat) ∧ WordAt u (wl.toNat + 8) ∧
        wl.toNat + 32 ≤ globN u "heap_ptr")) :
    LogsListOK {u with memory := mem'} wl.toNat ∧
      LogsDisjFixed {u with memory := mem'} wl.toNat ∧
      (wl.toNat = memW {u with memory := mem'} (w_out.toNat + 16) ∨
        (memW {u with memory := mem'} (wl.toNat) = wl.toNat + 24 ∧
          memW {u with memory := mem'} (wl.toNat + 8) = 0 ∧
          WordAt {u with memory := mem'} (wl.toNat) ∧
          WordAt {u with memory := mem'} (wl.toNat + 8) ∧
          wl.toNat + 32 ≤ globN {u with memory := mem'} "heap_ptr")) := by
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
  -- the store cell lies inside the array
  have hidx := hE.idx_lt
  have hxin : memW u (globN u "bo" + 32) ≤ x.toNat ∧
      x.toNat + 8 ≤ memW u (globN u "bo" + 32) + 16 * memW u (globN u "bo" + 80) + 16 := by
    omega
  have hin : Inside (x.toNat, 8) (memW u (globN u "bo" + 32))
      (memW u (globN u "bo" + 32) + 16 * memW u (globN u "bo" + 80) + 16) :=
    p4O_inside_of hxin.1 hxin.2
  -- every interval disjoint from the array is unhit by the store
  have hu_of : ∀ i : Ivl, (i.2 = 0 → i.1 % 8 = 0) →
      Disj i (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) →
      IvlUnhit u {u with memory := mem'} i := fun i hi0 hd =>
    ivlUnhit_single hm hi0 (disj_of_inside_right hin hd)
  -- fixed objects and the out record
  have hfix_eq : fixedObjects {u with memory := mem'} = fixedObjects u :=
    p4O_store_fixed_eq hWT hE hAR hj hm hx_eq
  have hout_disj := p4O_out_disj hD
  have hout8 : w_out.toNat % 8 = 0 := hD.out_words.1
  have hout_hi : (w_out.toNat, 96).1 + (w_out.toNat, 96).2 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAR.2 (Or.inl hD.out_inside)).2
  have hout16 : memW {u with memory := mem'} (w_out.toNat + 16) =
      memW u (w_out.toNat + 16) :=
    memW_eq_of_ivlUnhit (a := w_out.toNat + 16)
      (hu_of _ (fun hz => absurd hz (by simp)) (hout_disj _ harr_fix))
      (by omega) hout_hi (p4O_cellIn (a := w_out.toNat) (n := 96) (c := 16) (by omega))
  -- the store target lies above the low cells
  have hx_low : 16 < x.toNat := by
    have hsb : 16 < sourceBase := by decide
    have hss : sourceBase ≤ scratchStart := by decide
    obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8f, ha9⟩ := hAR.2
    rcases harr_alloc with ⟨h1, _⟩ | ⟨h1, _⟩
    · have h1' : sourceBase ≤ memW u (globN u "bo" + 32) := h1
      omega
    · have h1' : globN u "scratch_ptr" ≤ memW u (globN u "bo" + 32) := h1
      omega
  by_cases hwl0 : wl.toNat = 0
  · rw [hwl0] at hLL hDF hdisj
    rw [hwl0]
    refine ⟨Or.inl rfl, Or.inl rfl, ?_⟩
    rcases hdisj with hkeep | ⟨hm0, hm8, hw0, hw8, hhp⟩
    · rw [hout16]
      exact Or.inl hkeep
    · refine Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (p4O_memW_low_store' hm hx_low (c := 0) (by omega)).trans hm0
      · exact (p4O_memW_low_store' hm hx_low (c := 8) (by omega)).trans hm8
      · exact p4O_wordAt_low_store' hm hx_low (c := 0) (by omega) hw0
      · exact p4O_wordAt_low_store' hm hx_low (c := 8) (by omega) hw8
      · exact hhp
  · -- the list is live: both logs facts are live
    have hwl_ne : wl.toNat ≠ 0 := hwl0
    rcases hLL with hz | ⟨hw_hdr, hal_hdr, hcap, hlen, hent⟩
    · exact absurd hz hwl_ne
    rcases hDF with hz2 | ⟨hal_back, hIvls⟩
    · exact absurd hz2 hwl_ne
    -- the header interval
    have hdisj_hdr : Disj (wl.toNat, 24)
        (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) :=
      hIvls _ (List.mem_append.2 (Or.inl (List.mem_cons.2 (Or.inl rfl)))) _ harr_fix
    have hu_hdr : IvlUnhit u {u with memory := mem'} (wl.toNat, 24) :=
      hu_of _ (fun hz => absurd hz (by simp)) hdisj_hdr
    have hhi_hdr : (wl.toNat, 24).1 + (wl.toNat, 24).2 ≤ 2 ^ 64 :=
      (ivl_allocated_bound hAR.2 hal_hdr).2
    have hpw1 : (wl.toNat, 24).1 = wl.toNat := rfl
    have hpw2 : (wl.toNat, 24).2 = 24 := rfl
    have hwa8 : wl.toNat % 8 = 0 := hpw1 ▸ hw_hdr.1
    have c0 : memW {u with memory := mem'} wl.toNat = memW u wl.toNat :=
      memW_eq_of_ivlUnhit (a := wl.toNat) hu_hdr hw_hdr.1 hhi_hdr
        (p4O_cellIn (a := wl.toNat) (n := 24) (c := 0) (by omega))
    have c8 : memW {u with memory := mem'} (wl.toNat + 8) = memW u (wl.toNat + 8) :=
      memW_eq_of_ivlUnhit (a := wl.toNat + 8) hu_hdr (by omega) hhi_hdr
        (p4O_cellIn (a := wl.toNat) (n := 24) (c := 8) (by omega))
    have c16 : memW {u with memory := mem'} (wl.toNat + 16) = memW u (wl.toNat + 16) :=
      memW_eq_of_ivlUnhit (a := wl.toNat + 16) hu_hdr (by omega) hhi_hdr
        (p4O_cellIn (a := wl.toNat) (n := 24) (c := 16) (by omega))
    have hhead : ∀ k ∈ ([0, 8, 16] : List Nat),
        memW {u with memory := mem'} (wl.toNat + k) = memW u (wl.toNat + k) := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact c0
      · exact c8
      · exact c16
    -- the backing array
    have hdisj_back : Disj (memW u wl.toNat, 8 * memW u (wl.toNat + 8))
        (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) :=
      hIvls _ (List.mem_append.2
        (Or.inl (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))) _ harr_fix
    have hhi_back : (memW u wl.toNat, 8 * memW u (wl.toNat + 8)).1 +
        (memW u wl.toNat, 8 * memW u (wl.toNat + 8)).2 ≤ 2 ^ 64 :=
      (ivl_allocated_bound hAR.2 hal_back).2
    have hpb1 : (memW u wl.toNat, 8 * memW u (wl.toNat + 8)).1 = memW u wl.toNat := rfl
    have hpb2 : (memW u wl.toNat, 8 * memW u (wl.toNat + 8)).2 =
        8 * memW u (wl.toNat + 8) := rfl
    have hb : ∀ i : Nat, i < memW u (wl.toNat + 8) →
        memW {u with memory := mem'} (memW u wl.toNat + 8 * i) =
        memW u (memW u wl.toNat + 8 * i) := by
      intro i hi
      exact p4O_memW_store hm hdisj_back hxin (by omega) (by omega) (by omega)
    -- every owned log record
    have hrec_mem : ∀ i : Nat, i < memW u (wl.toNat + 8) →
        (memW u (memW u wl.toNat + 8 * i), 40) ∈ logOwnedIvls u
          (memW u (memW u wl.toNat + 8 * i)) := by
      intro i _
      unfold logOwnedIvls
      refine List.mem_filter.2 ⟨by simp [logRecordIvls], ?_⟩
      simp only [bne_iff_ne, ne_eq, Prod.mk.injEq, not_and]
      intro _ h40; omega
    have hu_rec : ∀ i : Nat, i < memW u (wl.toNat + 8) →
        IvlUnhit u {u with memory := mem'}
          (memW u (memW u wl.toNat + 8 * i), 40) := by
      intro i hi
      have hflat : (memW u (memW u wl.toNat + 8 * i), 40) ∈
          (List.range (memW u (wl.toNat + 8))).flatMap
            (fun idx => logOwnedIvls u (memW u (memW u wl.toNat + 8 * idx))) :=
        List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hrec_mem i hi⟩
      exact hu_of _ (fun h => absurd h (Nat.succ_ne_zero 39))
        (hIvls _ (List.mem_append.2 (Or.inr hflat)) _ harr_fix)
    have hLL' : LogsListOK u wl.toNat := Or.inr ⟨hw_hdr, hal_hdr, hcap, hlen, hent⟩
    refine ⟨?_, ?_, ?_⟩
    · exact pmc_logsListOK_congr_live hAR.2 hAR.1 (p4O_guestInv_mem hAR.1) le_rfl hLL'
        (fun h => h) hhead hb hu_rec
    · refine Or.inr ⟨?_, ?_⟩
      · rw [c0, c8]
        exact hal_back
      · rw [hfix_eq, c0, c8]
        intro o ho j hj
        rcases List.mem_append.1 ho with hA | hB
        · rcases List.mem_cons.1 hA with h1 | h2
          · exact hIvls _ (List.mem_append.2 (Or.inl (List.mem_cons.2 (Or.inl h1)))) j hj
          · rcases List.mem_cons.1 h2 with h1 | h3
            · exact hIvls _ (List.mem_append.2
                (Or.inl (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl h1)))))) j hj
            · exact absurd h3 (by simp)
        · obtain ⟨i, hi, ho2⟩ := List.mem_flatMap.1 hB
          have hi' : i < memW u (wl.toNat + 8) := List.mem_range.1 hi
          rw [hb i hi'] at ho2
          rw [pmc_logOwnedIvls_eq_of_unhit hAR.2 (hent i hi').2 (hu_rec i hi') rfl] at ho2
          exact hIvls _ (List.mem_append.2 (Or.inr (List.mem_flatMap.2
            ⟨i, List.mem_range.2 hi', ho2⟩))) j hj
    · rcases hdisj with hkeep | ⟨hm0, hm8, hw0, hw8, hhp⟩
      · exact Or.inl (hkeep.trans hout16.symm)
      · refine Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [c0]; exact hm0
        · rw [c8]; exact hm8
        · exact p4O_wordAt_store hm hdisj_hdr hxin (by omega) (by omega) (by omega) hw0
        · exact p4O_wordAt_store hm hdisj_hdr hxin (by omega) (by omega) (by omega) hw8
        · exact hhp

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
