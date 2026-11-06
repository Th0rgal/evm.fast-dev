import InitECandidate.Solver.Wave8GuestInv.ContractParts.C10
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexed

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- `keccak_pad` (136 B) and `keccak_st` (200 B) are allocated (when nonzero) and disjoint
from `Nd`'s node records and paths. Propagated from `MptObjReady` in `mpt_root`. -/
def KeccakBufsSafe {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
    ((bufferRegion s gs).2 = 0 ∨ Allocated s (bufferRegion s gs)) ∧
      ∀ o ∈ nodeExtents s Nd, Disj o (bufferRegion s gs)

/-- Strengthened `NodeRlpReady` carrying `KeccakBufsSafe` for the witnessing `Nd`. -/
def NodeRlpReadyK : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "node") ∧ KeccakBufsSafe s Nd

/-- The non-null node guard exported by `node_rlp` and `node_hash`. -/
def NodeRlpReadyNonNull : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => NodeRlpReadyK s ∧ locN s "node" ≠ 0

/-- The guard needed by `_node_rlp_fill`: a typed, non-null node with a nonzero kind. -/
def NodeRlpReadyStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => NodeRlpReadyK s ∧ locN s "node" ≠ 0 ∧ memW s (locN s "node") ≠ 0

namespace NodeRlpFillProof

private theorem node_mem_ne_zero {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {n : Nat} (hNd : NodeHeap s Nd) (hn : n ∈ Nd) : n ≠ 0 := by
  have hbase : sourceBase ≤ n := (hNd.1 n hn).2.2.1.1
  have hpos : 0 < sourceBase := by decide
  omega

private theorem strong_to_nonNull {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : NodeRlpReadyStrong s) : NodeRlpReadyNonNull s := ⟨h.1, h.2.1⟩

private theorem strong_kind_bounds {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : NodeRlpReadyStrong s) :
    1 ≤ memW s (locN s "node") ∧ memW s (locN s "node") ≤ 3 := by
  obtain ⟨Nd, hNd, hr, _⟩ := h.1.2
  have hn : locN s "node" ∈ Nd := hr.resolve_left h.2.1
  exact ⟨Nat.pos_of_ne_zero h.2.2, (hNd.1 _ hn).1⟩

private theorem keccakBufsSafe_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {Nd : List Nat}
    (h : KeccakBufsSafe s Nd) :
    KeccakBufsSafe { s with locals := locals, clock := k } Nd := h

private theorem keccakBufsSafe_of_grows {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hs : KeccakBufsSafe s Nd) (hg : AllocatorGrows s post)
    (hbuf : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion post gs = bufferRegion s gs)
    (hext : nodeExtents post Nd = nodeExtents s Nd) :
    KeccakBufsSafe post Nd := by
  intro gs hgs
  rw [hbuf gs hgs]
  refine ⟨(hs gs hgs).1.elim Or.inl (fun h => Or.inr (hg.allocated h)), ?_⟩
  intro o ho
  rw [hext] at ho
  exact (hs gs hgs).2 o ho

private theorem strong_to_nodeRlpReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : NodeRlpReadyStrong s) : NodeRlpReady s := by
  obtain ⟨Nd, hNd, hr, _⟩ := h.1.2
  exact ⟨h.1.1, Nd, hNd, hr⟩

private theorem strong_node_member {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : NodeRlpReadyStrong s) :
    ∃ Nd, NodeHeap s Nd ∧ locN s "node" ∈ Nd ∧ KeccakBufsSafe s Nd := by
  obtain ⟨Nd, hNd, hr, hk⟩ := h.1.2
  exact ⟨Nd, hNd, hr.resolve_left h.2.1, hk⟩

private theorem scratch48_progress {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : Nat} (hf : FreshScratch s post p 48)
    (hp : globN post "scratch_ptr" = p) :
    globN post "scratch_ptr" + 48 ≤ globN s "scratch_ptr" := by
  rw [hp]
  exact hf.2.2.1.2

private theorem nodeSize_ge32 (k : Nat) : 32 ≤ nodeSize k := by
  unfold nodeSize
  split_ifs <;> omega

private theorem nodeHeap_congr_cache {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hnonCache : ∀ n ∈ Nd, ∀ k, k < nodeSize (memW s n) / 8 →
      k ≠ 1 → k ≠ 2 → k ≠ 3 → memW post (n + 8 * k) = memW s (n + 8 * k))
    (hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40)
    (hpath_bytes : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ j, j < memW s (n + 40) → memB post (memW s (n + 32) + j) = memB s (memW s (n + 32) + j)) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have hw0 : ∀ n ∈ Nd, memW post n = memW s n := by
    intro n hn
    have hsz := nodeSize_ge32 (memW s n)
    simpa using hnonCache n hn 0 (by omega) (by decide) (by decide) (by decide)
  have hivl : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n := by
    intro n hn
    simp [nodeIvl, hw0 n hn]
  have hpath : ∀ n ∈ Nd, nodePath post n = nodePath s n := by
    intro n hn
    have hk_eq := hw0 n hn
    unfold nodePath
    by_cases h12 : memW s n = 1 ∨ memW s n = 2
    · have hsz : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize
        rcases h12 with h1 | h2 <;> [simp [h1]; simp [h2]]
      have hw32 := hnonCache n hn 4 (by omega) (by decide) (by decide) (by decide)
      have hw40 := hnonCache n hn 5 (by omega) (by decide) (by decide) (by decide)
      simp [hk_eq, h12, hw32, hw40]
    · simp [hk_eq, h12]
  have hext_eq : nodeExtents post Nd = nodeExtents s Nd := by
    unfold nodeExtents
    apply List.flatMap_congr
    intro n hn
    rw [hivl n hn, hpath n hn]
  refine ⟨⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩, hext_eq⟩
  · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, hkey_n, _, hleaf, hbranch⟩ := hN.1 n hn
    rw [hw0 n hn, hivl n hn]
    refine ⟨hk3, hag.allocated hal_n, hin_n, P3MptSet.wordsOK_transfer hgS hgP hw_n,
      ?_, ?_, ?_, hrlp_len n hn, ?_, ?_⟩
    · intro h2
      have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
      have hw48 := hnonCache n hn 6 (by omega) (by decide) (by decide) (by decide)
      simpa only [Nat.mul_succ, Nat.mul_zero] using
        (by rw [hw48]; exact hext h2 : RootIn Nd (memW post (n + 48)))
    · intro h3 i hi
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have hw_ch := hnonCache n hn (4 + i) (by omega) (by omega) (by omega) (by omega)
      have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
      rw [← hadd, hw_ch, hadd]
      exact hbr h3 i hi
    · intro h12
      have hsz : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize
        rcases h12 with h1 | h2 <;> [simp [h1]; simp [h2]]
      have hw32 := hnonCache n hn 4 (by omega) (by decide) (by decide) (by decide)
      have hw40 := hnonCache n hn 5 (by omega) (by decide) (by decide) (by decide)
      rw [hw32, hw40]
      rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
      · exact Or.inl h0
      · by_cases hlen0 : memW s (n + 40) = 0
        · exact Or.inl hlen0
        · right
          refine ⟨fun j hj => ?_, hag.allocated hal_p, hin_p, fun m hm => ?_⟩
          · rw [hpath_bytes n hn h12 hlen0 j hj]
            exact hnib j hj
          · rw [hivl m hm]
            exact hdisj_p m hm
    · intro h1
      have hsz : nodeSize (memW s n) = 64 := by unfold nodeSize; simp [h1]
      have hw56 := hnonCache n hn 7 (by omega) (by decide) (by decide) (by decide)
      simpa only [Nat.reduceMul, hw56] using hleaf h1
    · intro h3
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have hw168 := hnonCache n hn 21 (by omega) (by decide) (by decide) (by decide)
      simpa only [Nat.reduceMul, hw168] using hbranch h3
  · rw [hivl n hn, hivl m hm]
    exact hN.2 n hn m hm hne

private theorem nodeSize_mod8 (k : Nat) : nodeSize k % 8 = 0 := by
  unfold nodeSize
  split_ifs <;> omega

private theorem memW_eq_of_cell_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {a : Nat}
    (h : post.memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a)) :
    memW post a = memW s a := by
  unfold memW; rw [h]

private def nodeCacheIvls (Nd : List Nat) : List Ivl :=
  Nd.map fun n => (n + 8, 24)

private def keccakBufIvls {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200)]

private theorem disj_comm {a b : Ivl} (h : Disj a b) : Disj b a := by
  rcases h with h0 | h0 | h1 | h2
  · exact Or.inr (Or.inl h0)
  · exact Or.inl h0
  · exact Or.inr (Or.inr (Or.inr h1))
  · exact Or.inr (Or.inr (Or.inl h2))

private theorem keccakBufIvls_disj_of_safe {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hsafe : KeccakBufsSafe s Nd) :
    ∀ e ∈ keccakBufIvls s, ∀ o ∈ nodeExtents s Nd, Disj e o := by
  intro e he o ho
  simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact disj_comm ((hsafe ("keccak_pad", 136) (by decide)).2 o ho)
  · exact disj_comm ((hsafe ("keccak_st", 200) (by decide)).2 o ho)

private theorem nodeHeap_of_heapByteEff_cache {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {extra : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post (nodeCacheIvls Nd ++ extra) gw)
    (hextra_disj : ∀ e ∈ extra, ∀ o ∈ nodeExtents s Nd, Disj e o)
    (hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hag : AllocatorGrows s post := ⟨heff.hp_le, heff.sp_le⟩
  apply nodeHeap_congr_cache hAs.1 heff.arena.1 hag hN ?_ hrlp_len ?_
  · intro n hn k hk hk1 hk2 hk3
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
    have hn8 : n % 8 = 0 := hw_n.1
    have hsz : 8 * k + 8 ≤ nodeSize (memW s n) := by
      have := nodeSize_mod8 (memW s n); omega
    have ha_lt : n + 8 * k < 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    apply memW_eq_of_cell_eq
    by_contra hne
    have ha_nat : (BitVec.ofNat 64 (n + 8 * k)).toNat = n + 8 * k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
    rcases heff.cell_frame (BitVec.ofNat 64 (n + 8 * k)) hne with
      ⟨iv, hiv, _, hc1, hc2⟩ | ⟨_, hfg1, hfg2⟩ | ⟨_, hhf1, hhf2⟩
    · rw [ha_nat] at hc1 hc2
      rcases List.mem_append.1 hiv with hcache | hex
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hcache
        by_cases hnm : n = m
        · subst hnm; dsimp only at hc1 hc2; omega
        · have hdj := hN.2 n hn m hm hnm
          have hsz_m := nodeSize_ge32 (memW s m)
          dsimp [nodeIvl] at hdj hc1 hc2
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · have ho_mem : nodeIvl s n ∈ nodeExtents s Nd := by
          unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
        have hdj := hextra_disj iv hex (nodeIvl s n) ho_mem
        dsimp [nodeIvl] at hdj
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
    · rw [ha_nat] at hfg1 hfg2
      have hfm8 : globN s "frame_mem_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.2.1
      have hsp8 : globN s "scratch_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.2.2.1
      have hdj := P3MptSet.disj_allocated_freeGap hAs.2 hal_n
      dsimp [nodeIvl, freeGap] at hdj hfg1 hfg2
      rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
    · rw [ha_nat] at hhf1 hhf2
      have hhp8 : globN s "heap_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.1
      have hdj := P3MptSet.disj_allocated_heapFree hAs.2 hal_n
      dsimp [nodeIvl, heapFree] at hdj hhf1 hhf2
      rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · intro n hn h12 hlen0 j hj
    obtain ⟨_, _, _, _, _, _, hkey_n, _⟩ := hN.1 n hn
    rcases hkey_n h12 with h0 | ⟨_, hal_p, hin_p, hdisj_p⟩
    · exact absurd h0 hlen0
    · have hb_lt : memW s (n + 32) + j < 2 ^ 64 := by
        have := hin_p.2; dsimp at this; omega
      by_contra hne
      rcases heff.byte_frame (memW s (n + 32) + j) hb_lt hne with
        ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
      · rcases List.mem_append.1 hiv with hcache | hex
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hcache
          have hdj := hdisj_p m hm
          have hsz_m := nodeSize_ge32 (memW s m)
          dsimp [nodeIvl] at hdj hb1 hb2
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
        · have hp_mem : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
            unfold nodeExtents
            exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
          have hdj := hextra_disj iv hex _ hp_mem
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · have hdj := P3MptSet.disj_allocated_freeGap hAs.2 hal_p
        dsimp [freeGap] at hdj hfg1 hfg2
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · have hdj := P3MptSet.disj_allocated_heapFree hAs.2 hal_p
        dsimp [heapFree] at hdj hhf1 hhf2
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega

private theorem memW_eq_of_heapByteEff_disj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String} {a : Nat}
    (hAs : ArenaReady s) (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post Rl gw)
    (_ha8 : a % 8 = 0) (hal : Allocated s (a, 8)) (ha_lt : a < 2 ^ 64)
    (hdisj : ∀ iv ∈ Rl, 0 < iv.2 → Disj (a, 8) iv) :
    memW post a = memW s a := by
  apply memW_eq_of_cell_eq
  by_contra hne
  have ha_nat : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  rcases heff.cell_frame (BitVec.ofNat 64 a) hne with
    ⟨iv, hiv, hpos, hc1, hc2⟩ | ⟨hpos_fg, hfg1, hfg2⟩ | ⟨hpos_hf, hhf1, hhf2⟩
  · rw [ha_nat] at hc1 hc2
    have hdj := hdisj iv hiv hpos
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · rw [ha_nat] at hfg1 hfg2
    have hdj := P3MptSet.disj_allocated_freeGap hAs.2 hal
    dsimp [freeGap] at hdj hpos_fg hfg1 hfg2
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · rw [ha_nat] at hhf1 hhf2
    have hdj := P3MptSet.disj_allocated_heapFree hAs.2 hal
    dsimp [heapFree] at hdj hpos_hf hhf1 hhf2
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega

private theorem memB_eq_of_heapByteEff_disj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String} {b : Nat}
    (hAs : ArenaReady s) (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post Rl gw)
    (hal : Allocated s (b, 1)) (hb_lt : b < 2 ^ 64)
    (hdisj : ∀ iv ∈ Rl, 0 < iv.2 → Disj iv (b, 1)) :
    memB post b = memB s b := by
  by_contra hne
  rcases heff.byte_frame b hb_lt hne with
    ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
  · have hdj := hdisj iv hiv (by omega)
    dsimp [Disj] at hdj
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · have hdj := P3MptSet.disj_allocated_freeGap hAs.2 hal
    dsimp [Disj, freeGap] at hdj hfg1 hfg2
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · have hdj := P3MptSet.disj_allocated_heapFree hAs.2 hal
    dsimp [Disj, heapFree] at hdj hhf1 hhf2
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega

private theorem nodeHeap_of_heapByteEff_disj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {Rl : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post Rl gw)
    (hdisj : ∀ iv ∈ Rl, 0 < iv.2 → ∀ o ∈ nodeExtents s Nd, Disj iv o) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have heff' : R16Shards.WkBlockTxEnc.HeapByteEff s post (nodeCacheIvls Nd ++ Rl) gw :=
    heff.mono
      (fun i hi _ => Or.inl ⟨i, List.mem_append_right _ hi, le_rfl, le_rfl⟩)
      (fun _ hg => hg)
  have hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40 := by
    intro n hn
    obtain ⟨_, hal_n, hin_n, hw_n, _, _, _, hrlp_s, _⟩ := hN.1 n hn
    have hsz := nodeSize_ge32 (memW s n)
    have hal_16 : Allocated s (n + 16, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    have ha_lt : n + 16 < 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hw16_eq : memW post (n + 16) = memW s (n + 16) := by
      apply memW_eq_of_heapByteEff_disj hAs heff (by omega) hal_16 ha_lt
      intro iv hiv hpos
      have ho_mem : nodeIvl s n ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
      have hdj := hdisj iv hiv hpos (nodeIvl s n) ho_mem
      dsimp [Disj, nodeIvl] at hdj ⊢
      rcases hdj with h0 | h0 | hd1 | hd2
      · exact Or.inr (Or.inl h0)
      · omega
      · exact Or.inr (Or.inr (Or.inr (by omega)))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    rw [hw16_eq]
    exact hrlp_s
  have hextra_disj : ∀ e ∈ Rl, ∀ o ∈ nodeExtents s Nd, Disj e o := by
    intro e he o ho
    by_cases he0 : e.2 = 0
    · exact Or.inl he0
    · exact hdisj e he (Nat.pos_of_ne_zero he0) o ho
  exact nodeHeap_of_heapByteEff_cache hAs hN heff' hextra_disj hrlp_len

private theorem eval_load_memW_of_wordsOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {off len : Nat}
    (hW : WordsOK s (base.toNat, len)) (hoff8 : off % 8 = 0) (hoff_lt : off + 8 ≤ len)
    (hhi : base.toNat + len ≤ 2 ^ 64) {e : ExpHOL 64}
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one e) =
        some (.val (.word w)) ∧
      w.toNat = memW s (base.toNat + off) := by
  have hk_lt : off / 8 < len / 8 := by omega
  obtain ⟨w, hdom, hmem⟩ := hW.2.2 (off / 8) hk_lt
  have haddr_eq : base + BitVec.ofNat 64 off = BitVec.ofNat 64 (base.toNat + 8 * (off / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hdom' : s.memaddrs (base + BitVec.ofNat 64 off) := haddr_eq ▸ hdom
  have hmem' : s.memory (base + BitVec.ofNat 64 off) = .word w := haddr_eq ▸ hmem
  refine ⟨w, ?_, ?_⟩
  · simp [evalHOLExact, he, memLoadHOLExact, hdom', hmem']
  · unfold memW
    have hbv : BitVec.ofNat 64 (base.toNat + off) = base + BitVec.ofNat 64 off := by
      rw [haddr_eq]; congr 1; omega
    rw [hbv, hmem']

private theorem heapByteEff_of_p26_byteEff {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (heff : R10Shards.P26_P28.ByteEff s post Rl) :
    R16Shards.WkBlockTxEnc.HeapByteEff s post Rl gw := by
  have hG : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAR.1
  have hA : ArenaOK post := arenaOK_congr heff.globals hAR.2
  have hg_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  refine ⟨⟨hG, hA⟩, heff.memaddrs, by rw [hg_eq], hg_eq _, by rw [hg_eq], heff.be,
    fun k _ => by rw [heff.globals], heff.out_dom,
    fun a hne => Or.inl (heff.cell_frame a hne),
    fun b hb hne => Or.inl (heff.byte_frame b hb hne)⟩

private theorem eval_store_memW_at {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base w : BitVec 64} {off len : Nat} {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (hW : WordsOK s (base.toNat, len))
    (hoff8 : off % 8 = 0) (hoff_lt : off + 8 ≤ len) (hhi : base.toNat + len ≤ heapEnd)
    (hin_Rl : ∃ i ∈ Rl, i.1 ≤ base.toNat + off ∧ base.toNat + off + 8 ≤ i.1 + i.2)
    {dstExp valExp : ExpHOL 64}
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w))) :
    let out := evaluateHOLFiniteState s (.store dstExp valExp)
    out.1 = none ∧ out.2.locals = s.locals ∧ out.2.globals = s.globals ∧
    memW out.2 (base.toNat + off) = w.toNat ∧
    (∀ b : Nat, b < 2 ^ 64 → b ≠ base.toNat + off →
      out.2.memory (BitVec.ofNat 64 b) = s.memory (BitVec.ofNat 64 b)) ∧
    R16Shards.WkBlockTxEnc.HeapByteEff s out.2 Rl gw := by
  intro out; dsimp only [out]
  have h264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hk_lt : off / 8 < len / 8 := by omega
  obtain ⟨w0, hdom, _⟩ := hW.2.2 (off / 8) hk_lt
  have haddr_eq : base + BitVec.ofNat 64 off = BitVec.ofNat 64 (base.toNat + 8 * (off / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have haddr_nat : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [haddr_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hdom' : s.memaddrs (base + BitVec.ofNat 64 off) := haddr_eq ▸ hdom
  have hbeff : R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s (.store dstExp valExp)).2 Rl :=
    (R10Shards.P26_P28.byteEff_store_one hAR.1 dstExp valExp
      (fun v hv => by rw [hval] at hv; injection hv with h; exact ⟨w, h.symm⟩)
      (fun x hx _ => by
        rw [hdst] at hx; injection hx with h1; injection h1 with h2; injection h2 with h3
        subst h3; rw [haddr_nat]; exact hin_Rl)).1
  have hev : evaluateHOLFiniteState s (.store dstExp valExp) =
      (none, { s with memory := Function.update s.memory (base + BitVec.ofNat 64 off) (.word w) }) := by
    rw [evaluateHOLFiniteState_store]
    simp only [hdst, hval, flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom', BitVec.add_zero, ↓reduceIte]
    congr 1; congr 1
    funext current
    by_cases hc : current = base + BitVec.ofNat 64 off <;> simp [hc, Function.update]
  refine ⟨congrArg Prod.fst hev, ?_, ?_, ?_, ?_, heapByteEff_of_p26_byteEff hAR hbeff⟩
  · rw [hev]
  · rw [hev]
  · rw [hev]
    unfold memW
    have hbv : BitVec.ofNat 64 (base.toNat + off) = base + BitVec.ofNat 64 off := by
      apply BitVec.eq_of_toNat_eq
      rw [haddr_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hbv]; simp
  · intro b hb hne
    rw [hev]; dsimp only
    have hne_bv : BitVec.ofNat 64 b ≠ base + BitVec.ofNat 64 off := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, haddr_nat] at this
      exact hne this
    exact Function.update_of_ne hne_bv _ _

private theorem localsOnlyNonNull : LocalsOnly ["node"] NodeRlpReadyNonNull := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  simp only [NodeRlpReadyNonNull, NodeRlpReadyK, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

private theorem localsOnlyStrong : LocalsOnly ["node"] NodeRlpReadyStrong := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  simp only [NodeRlpReadyStrong, NodeRlpReadyK, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

private theorem entryNonNull {fname : MlS}
    {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "node", .one)]) :
    CallEntryOn NodeRlpReadyNonNull NodeRlpReadyNonNull fname
      [.var .local (ofString "node")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "node") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  exact localsOnlyNonNull state callee (state.clock - 1) (by simpa using hc) hP

private theorem entryStrong {fname : MlS}
    {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "node", .one)]) :
    CallEntryOn NodeRlpReadyStrong NodeRlpReadyStrong fname
      [.var .local (ofString "node")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "node") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  exact localsOnlyStrong state callee (state.clock - 1) (by simpa using hc) hP

private theorem straight (p : ProgHOL 64) (h : extStraightLine p = true) :
    TerminatingProgBoundedOn GuestInv p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p h s hc

private theorem weakenGuard {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {k : Nat} (h : TerminatingProgBoundedOn Q p k)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s) :
    TerminatingProgBoundedOn P p k := fun s hc hP => h s hc (hp s hP)

private theorem seq_hoare_to {P R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (hp : Hoare P first (fun r t => r = none → R t))
    (h2 : TerminatingProgBoundedOn R second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  have hmid := hp.run state hcode hP
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp) rfl) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

private theorem cond_eq_false {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {k : BitVec 64}
    (h : CondFalse (.cmp .equal e (.const k)) s) :
    ∃ w : BitVec 64, evalAt s e = some (.val (.word w)) ∧ w ≠ k := by
  obtain ⟨a, b, ha, hb, hz⟩ := evalAt_cmp s .equal e (.const k) 0 h
  cases evalAt_const s k _ hb
  refine ⟨a, ha, ?_⟩
  intro hab
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hab] at hz

private theorem cond_local_eq_false {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n : String} {k : BitVec 64}
    (h : CondFalse (.cmp .equal (.var .local (ofString n)) (.const k)) s) :
    locN s n ≠ k.toNat := by
  obtain ⟨w, hw, hn⟩ := cond_eq_false h
  rw [← evalAt_local s n w hw]
  exact fun he => hn (BitVec.eq_of_toNat_eq he)

private theorem evalAt_loadL' {F : Type} (t : PanSemStateFiniteExact 64 F)
    (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (locN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.locals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [locN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

private theorem evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F)
    (g : String) (k : BitVec 64) (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (locN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.locals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadL' t g k a h⟩

private theorem strong_of_kind_cond_false {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : NodeRlpReadyNonNull s)
    (hc : CondFalse (.cmp .equal
      (.load .one (.op .add [.var .local (ofString "node"), .const 0])) (.const 0)) s) :
    NodeRlpReadyStrong s := by
  refine ⟨hs.1, hs.2, ?_⟩
  obtain ⟨w, hw, hne⟩ := cond_eq_false hc
  have hm : w.toNat = memW s (locN s "node") := by
    simpa using evalAt_loadL' s "node" 0 w hw
  intro hz
  apply hne
  apply BitVec.eq_of_toNat_eq
  have hwz : w.toNat = (0 : BitVec 64).toNat := by
    rw [hm]
    simpa using hz
  exact hwz

private theorem lookup_fill : originalRuntimeCode.lookup (ofString "_node_rlp_fill") =
    some ((sourceFunctionEntry Guest.Software.guestFn__node_rlp_fill).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 284 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_fill) rfl

private theorem lookup_rlp : originalRuntimeCode.lookup (ofString "node_rlp") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_rlp).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 285 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_rlp) rfl

private theorem lookup_hash : originalRuntimeCode.lookup (ofString "node_hash") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_hash).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 290 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_hash) rfl

private theorem lookup_root : originalRuntimeCode.lookup (ofString "mpt_root") =
    some ((sourceFunctionEntry Guest.Software.guestFn_mpt_root).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 291 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_root) rfl

private theorem lookup_mpt_fail :
    originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

private theorem eval_call_mpt_fail_no_none_no_ret {F : Type}
    (s : PanSemStateFiniteExact 64 F) (c : BitVec 64) (hc : s.code = originalRuntimeCode) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "mpt_fail") [.const c])
    out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) := by
  dsimp only
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const c] =
      some [.val (.word c)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "mpt_fail") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_mpt_fail) c (by rw [hc]; exact lookup_mpt_fail)
  rw [hargs]
  dsimp only
  rw [hlk]
  dsimp only
  split
  · exact ⟨by simp, fun _ => by simp⟩
  · have hb : sourceFnBody Guest.Software.guestFn_mpt_fail =
        .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
    have hraise_out : ∀ st : PanSemStateFiniteExact 64 F,
        let ro := (evaluateHOLFiniteState st
          (.raise (ofString "MptErr") (.var .local (ofString "code")))).1
        ro = some .error ∨ ∃ ev, ro = some (.exception (ofString "MptErr") ev) := by
      intro st
      dsimp only
      rw [evaluateHOLFiniteState_raise]
      split
      · dsimp only
        split <;> simp
      · simp
    let entry := callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "code", .val (.word c)))
    rcases hbody : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_mpt_fail) with
      ⟨res, st⟩
    have hr := hraise_out entry
    rw [hb, evaluateHOLFiniteState_seq_line780] at hbody
    rcases hr_st : evaluateHOLFiniteState entry
      (.raise (ofString "MptErr") (.var .local (ofString "code"))) with ⟨rr, sr⟩
    rw [hr_st] at hr hbody
    dsimp only at hr hbody
    rcases hr with rfl | ⟨ev, rfl⟩
    · injection hbody with h1 _
      subst h1
      exact ⟨by simp, fun _ => by simp⟩
    · injection hbody with h1 _
      subst h1
      exact ⟨by simp, fun _ => by simp⟩

private theorem mpt_fail_hoare {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} :
    Hoare P (.call (some (none, none)) (ofString "mpt_fail") [.const 2])
      (fun r t => r = none → NodeRlpReadyStrong t) := by
  refine ⟨fun {F} s hc _ _ => ?_⟩
  have hno := (eval_call_mpt_fail_no_none_no_ret s 2 hc).1
  exact fun hn => (hno hn).elim

end NodeRlpFillProof

/-- Strengthened `node_rlp`: its explicit kind check justifies the strong fill guard. -/
theorem gbody_node_rlp_strong
    (hf : TerminatingFunBoundedOn NodeRlpReadyStrong
      (ofString "_node_rlp_fill") K.«_node_rlp_fill»)
    (hm : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (_hr : ReadOnlyFn (ofString "mpt_fail")) :
    TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_rlp") K.«node_rlp» := by
  refine ⟨_, _, _, NodeRlpFillProof.lookup_rlp, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals NodeRlpFillProof.localsOnlyNonNull _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (NodeRlpFillProof.weakenGuard (NodeRlpFillProof.straight _ rfl) (fun s h => h.1.1.1))
        (Hoare.ite_return_skip _ _)
        (NodeRlpFillProof.seq_hoare_to
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.call_on hm _ _
              (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1.1.1) _ _))
            (NodeRlpFillProof.weakenGuard (NodeRlpFillProof.straight _ rfl) (fun s h => h.1.1.1)))
          (Hoare.ite
            (Hoare.mono NodeRlpFillProof.mpt_fail_hoare (fun s h => h.1))
            (Hoare.skip (fun s h _ => NodeRlpFillProof.strong_of_kind_cond_false h.1 h.2))
            (fun _ _ h => absurd h (by simp)))
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.call_on hf _ _
              (NodeRlpFillProof.entryStrong NodeRlpFillProof.lookup_fill (by rfl)))
            (fun s h => h.1.1.1)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«node_rlp»
  simp only [Nat.max_def]
  split <;> omega

/-- Strengthened `node_hash`, retaining the non-null guard across its `node_rlp` call. -/
theorem gbody_node_hash_strong
    (ha : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hk : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hn : TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_rlp") K.«node_rlp») :
    TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_hash") K.«node_hash» := by
  refine ⟨_, _, _, NodeRlpFillProof.lookup_hash, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_hash,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals NodeRlpFillProof.localsOnlyNonNull _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (NodeRlpFillProof.weakenGuard (NodeRlpFillProof.straight _ rfl) (fun s h => h.1.1.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hn _ _ _
          (NodeRlpFillProof.entryNonNull NodeRlpFillProof.lookup_rlp (by rfl))
          (decCallResumeOn_guestInv (fun s h => h.1.1.1) _ _ _)
          (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv hk _ _)
              (TerminatingProgBoundedOn.seq_guestInv (NodeRlpFillProof.straight _ rfl)
                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))) ?_
  unfold K.«node_hash»
  omega

namespace NodeRlpFillProof

private theorem callee_param_alias {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname pk caller : MlS) (sk : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(pk, sk)], body, ret))
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local caller] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup pk = state.locals.lookup caller := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact] at hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    rcases hv : state.locals.lookup caller with _ | v
    · rw [hv] at hargs
      cases hargs
    · rw [hv] at hargs
      cases hargs
      split at raw
      · have rawEq := Option.some.inj raw
        rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
        subst hloc
        simp
      · cases raw

private theorem dec_guard {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {k : Nat}
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s init = some v → Q (setVarHOLFinite name v s))
    (hb : TerminatingProgBoundedOn Q body k) :
    TerminatingProgBoundedOn P (.dec name shape init body) k := by
  intro F s hc hP hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · have h := hb (setVarHOLFinite name v s) hc (hi s v hP hv) hnt
      simpa only [setVarHOLFinite] using h
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

private def RootReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "root") ∧ KeccakBufsSafe s Nd

private def RootCallReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RootReady s ∧ locN s "root" ≠ 0

private theorem root_init {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hs : MptObjReady s)
    (hv : evalAt s (.load .one (.op .add [.var .local (ofString "m"), .const 0])) = some v) :
    RootReady (setVarHOLFinite (ofString "root") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "m" 0 v hv
  obtain ⟨ha, S, hS, ⟨Nd, hm⟩, _rest⟩ := hs
  refine ⟨localsFree_arenaReady s _ _ ha, Nd, hm.2.2.2.2.1, ?_, ?_⟩
  · rw [locN_setVar_same, hw]
    simpa using hm.2.2.2.2.2.1
  · intro gs hgs
    have hj_fix : bufferRegion s gs ∈ fixedObjects s := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
      have hbuf : bufferRegion s gs ∈ globalBuffers.map (bufferRegion s) := by
        rcases hgs with rfl | rfl
        · exact List.mem_map.mpr ⟨("keccak_pad", 136), by decide, rfl⟩
        · exact List.mem_map.mpr ⟨("keccak_st", 200), by decide, rfl⟩
      simp only [fixedObjects, List.mem_append, bufferRegion] at hbuf ⊢
      exact Or.inl (Or.inl (Or.inl hbuf))
    refine ⟨?_, fun o ho => (hm.2.2.2.2.2.2 o ho).2.2 _ hj_fix⟩
    rcases hS.2.2.1.1 (bufferRegion s gs) hj_fix with hz | ⟨hal, _⟩
    · exact Or.inl hz
    · exact Or.inr hal

private theorem root_call_of_false {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : RootReady s)
    (hc : CondFalse (.cmp .equal (.var .local (ofString "root")) (.const 0)) s) :
    RootCallReady s := ⟨hs, cond_local_eq_false hc⟩

private theorem root_entry :
    CallEntryOn RootCallReady NodeRlpReadyNonNull (ofString "node_hash")
      [.var .local (ofString "root")] := by
  intro F s vs b callee r hc hP hargs hl
  have hp := callee_param_alias s (ofString "node_hash") (ofString "node") (ofString "root")
    .one _ _ (by rw [hc]; exact lookup_hash) vs b callee r hargs hl
  have hx : locN (callEntryStateHOLFinite s callee) "node" = locN s "root" := by
    simp only [locN, callEntryStateHOLFinite, hp]
  refine ⟨⟨localsFree_arenaReady s _ _ hP.1.1, ?_⟩, ?_⟩
  · rw [hx]
    exact hP.1.2
  · rw [hx]
    exact hP.2

end NodeRlpFillProof

/-- Strengthened `mpt_root`; the original external `MptObjReady` conclusion is unchanged. -/
theorem gbody_mpt_root_strong
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hn : TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_hash") K.«node_hash») :
    TerminatingFunBoundedOn MptObjReady (ofString "mpt_root") K.«mpt_root» := by
  refine ⟨_, _, _, NodeRlpFillProof.lookup_root, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_mpt_root,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (NodeRlpFillProof.dec_guard _ _ _ NodeRlpFillProof.root_init
      (NodeRlpFillProof.seq_hoare_to
        (TerminatingProgBoundedOn.ite_on
          (NodeRlpFillProof.weakenGuard
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv hm _ _)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))
            (fun s h => h.1.1))
          (NodeRlpFillProof.weakenGuard (NodeRlpFillProof.straight _ rfl) (fun s h => h.1.1)))
        (Hoare.ite
          ⟨fun s hc hP hnt he => by
            rw [evaluateHOLFiniteState_seq_line780] at he
            dsimp only at he
            split at he
            · exact False.elim (return_ne_none _ _ he)
            · simp_all⟩
          (Hoare.skip (fun s h _ => NodeRlpFillProof.root_call_of_false h.1 h.2))
          (fun _ _ h => absurd h (by simp)))
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ NodeRlpFillProof.root_entry
          (decCallResumeOn_guestInv (fun s h => h.1.1.1) _ _ _)
          (TerminatingProgBoundedOn.seq_guestInv
            (TerminatingProgBoundedOn.call_guestInv hm _ _)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«mpt_root»
  simp only [Nat.max_def]
  split <;> omega


namespace NodeRlpFillProof
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.HeapPotential
open R16Shards.WkBlockTxEnc

private theorem pan_four_word_lookup
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname p1 p2 p3 p4 : MlS) (body : ProgHOL 64) (w1 w2 w3 w4 : BitVec 64)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hlook : code fname = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, .one)) :
    lookupCodeHOLFinite code fname [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body,
        (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update
          (p2, .val (.word w2))).update (p3, .val (.word w3))).update (p4, .val (.word w4)),
        .one) := by
  have raw : lookupCodeHOLExact code fname
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body,
        (fun k => if k = p4 then some (.val (.word w4))
          else if k = p3 then some (.val (.word w3))
          else if k = p2 then some (.val (.word w2))
          else if k = p1 then some (.val (.word w1))
          else none), .one) := by
    simp [lookupCodeHOLExact, hlook, shapeOfHOLExact, shapeEqHOL, h12, h13, h14, h23, h24, h34]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i hm; rw [raw] at hm; cases hm
  · rename_i fb fl fsh hf
    have heq := Option.some.inj (hf.symm.trans raw)
    rcases Prod.mk.inj heq with ⟨hb_eq, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hfl, hs_eq⟩
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨hb_eq, ?_, hs_eq⟩
    apply HolFiniteMapExact.ext
    funext k
    change fl k = _
    rw [hfl]
    by_cases hk4 : k = p4
    · subst hk4; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · by_cases hk3 : k = p3
      · subst hk3; simp [HolFiniteMapExact.lookup_update, FUPDATE, hk4, Ne.symm hk4]
      · by_cases hk2 : k = p2
        · subst hk2; simp [HolFiniteMapExact.lookup_update, FUPDATE, hk4, hk3, Ne.symm hk4, Ne.symm hk3]
        · by_cases hk1 : k = p1
          · subst hk1; simp [HolFiniteMapExact.lookup_update, FUPDATE, hk4, hk3, hk2, Ne.symm hk4, Ne.symm hk3, Ne.symm hk2]
          · simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.empty, FUPDATE,
              hk4, hk3, hk2, hk1, Ne.symm hk4, Ne.symm hk3, Ne.symm hk2, Ne.symm hk1]

private theorem lookup_rlp_be_len :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one) :=
  lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_be_len) rfl

private theorem lookup_rlp_bytes_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len") =
      some ([(ofString "first_byte", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len, .one) :=
  lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl

private theorem lookup_rlp_value_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_value_encoded_len") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len, .one) :=
  lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl

private theorem lookup_node_ref_len :
    originalRuntimeCode.lookup (ofString "node_ref_len") =
      some ([(ofString "child", .one)], sourceFnBody Guest.Software.guestFn_node_ref_len, .one) :=
  lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_ref_len) rfl

private theorem lookup__node_needs_rlp :
    originalRuntimeCode.lookup (ofString "_node_needs_rlp") =
      some ([(ofString "child", .one)], sourceFnBody Guest.Software.guestFn__node_needs_rlp, .one) :=
  lookup_of_guestAst_getElem 283 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_needs_rlp) rfl

private def roEncGood (f : MlS) : Bool :=
  ((["rlp_be_len", "rlp_header_len", "rlp_list_header_len", "rlp_bytes_encoded_len",
    "rlp_value_encoded_len", "node_ref_len", "_node_needs_rlp", "mpt_fail"] : List String).map ofString).contains f

private def roEncProg : ProgHOL 64 → Bool
  | .dec _ _ _ body => roEncProg body
  | .seq first second => roEncProg first && roEncProg second
  | .ite _ yes no => roEncProg yes && roEncProg no
  | .while _ body => roEncProg body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .decCall _ _ function _ continuation => roEncGood function && roEncProg continuation
  | .call none function _ => roEncGood function
  | .call (some (none, none)) function _ => roEncGood function
  | .call (some (some (.local, _), none)) function _ => roEncGood function
  | _ => false

private theorem roEnc_installed_body (f : MlS)
    (hf : roEncGood f = true)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs)) :
    roEncProg body = true := by
  simp only [roEncGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_be_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee WkBlockTxEnc.lookup_rlp_header_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee WkBlockTxEnc.lookup_rlp_list_header_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_bytes_encoded_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_value_encoded_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_node_ref_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup__node_needs_rlp hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_mpt_fail hl; subst hb; rfl

private theorem evaluate_roEncProg {F : Type} (program : ProgHOL 64)
    (supported : roEncProg program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2 =
      { state with locals := (evaluateHOLFiniteState state program).2.locals,
                   clock := (evaluateHOLFiniteState state program).2.clock } := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : roEncProg body = true := by simpa only [shape, roEncProg] using supported
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · rfl
    · rename_i val _
      split
      · have ih := evaluate_roEncProg body child (setVarHOLFinite name val state) code
        dsimp only [setVarHOLFinite] at ih ⊢
        rw [ih]
      · rfl
  | decCall name kind function arguments continuation =>
    have children : roEncGood function = true ∧ roEncProg continuation = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have hsafe := roEnc_installed_body function children.1 values body callee rs found
          have hbody := evaluate_roEncProg body hsafe (callEntryStateHOLFinite state callee) code
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbody meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at hbody meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try (rw [hbody]; cases state; rfl))
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            let resumed : PanSemStateFiniteExact 64 F :=
              setVarHOLFinite name v
                { st with locals := state.locals,
                          clock := if (callEntryStateHOLFinite state callee).clock < st.clock
                                   then (callEntryStateHOLFinite state callee).clock else st.clock }
            have ih := evaluate_roEncProg continuation children.2 resumed stCode
            dsimp only [resumed, setVarHOLFinite] at ih ⊢
            conv_lhs => rw [ih]
            rw [hbody]; cases state; rfl
          · rw [hbody]; cases state; rfl
  | assign kind name value =>
    cases kind with
    | global => simp [shape, roEncProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> (cases state; rfl)
  | seq first second =>
    have children : roEncProg first = true ∧ roEncProg second = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    have h1 := evaluate_roEncProg first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at h1 remaining meta'
      dsimp only at h1 remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        have h2 := evaluate_roEncProg second children.2 middle (meta'.1.trans code)
        dsimp only
        rw [h2, h1]
      | some _ => exact h1
  | ite condition yes no =>
    have children : roEncProg yes = true ∧ roEncProg no = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_roEncProg no children.2 state code
      · exact evaluate_roEncProg yes children.1 state code
    · rfl
  | «while» condition body =>
    have child : roEncProg body = true := by simpa only [shape, roEncProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hb := evaluate_roEncProg body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at hb remaining meta'
            dsimp only at hb remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none =>
              have hw := evaluate_roEncProg (.while condition body) (by simpa [roEncProg] using child) middle mCode
              rw [hw, hb]; cases state; rfl
            | some r =>
              cases r with
              | «continue» =>
                have hw := evaluate_roEncProg (.while condition body) (by simpa [roEncProg] using child) middle mCode
                rw [hw, hb]; cases state; rfl
              | _ => rw [hb]; cases state; rfl
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> (cases state; rfl)
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> (cases state; rfl)
  | call info function arguments =>
    have hk : roEncGood function = true ∧
        (info = none ∨ info = some (none, none) ∨ ∃ nm, info = some (some (.local, nm), none)) := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | _⟩
      · exact ⟨by simpa [shape, roEncProg] using supported, Or.inl rfl⟩
      · exact ⟨by simpa [shape, roEncProg] using supported, Or.inr (Or.inl rfl)⟩
      · simp [shape, roEncProg] at supported
      · cases kind
        · exact ⟨by simpa [shape, roEncProg] using supported, Or.inr (Or.inr ⟨nm, rfl⟩)⟩
        · simp [shape, roEncProg] at supported
      · simp [shape, roEncProg] at supported
    rw [evaluateHOLFiniteState_call]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        split
        · rfl
        · rename_i nonzero
          have hsafe := roEnc_installed_body function hk.1 values body callee rs found
          have hbody := evaluate_roEncProg body hsafe (callEntryStateHOLFinite state callee) code
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbody
          obtain ⟨r, st⟩ := out
          dsimp only at hbody ⊢
          rcases hk.2 with rfl | rfl | ⟨nm, rfl⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (rw [hbody]; cases state; rfl)
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (rw [hbody]; cases state; rfl)
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (try dsimp only [setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]) <;>
              (rw [hbody]; cases state; rfl)
  | _ => simp [shape, roEncProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | omega


private theorem heapByteEff_of_roEncProg {F : Type} {s : PanSemStateFiniteExact 64 F}
    (p : ProgHOL 64) (hp : roEncProg p = true) (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (Rl : List Ivl) (gw : List String) :
    HeapByteEff s (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [evaluate_roEncProg p hp s hc]
  exact (HeapByteEff.refl hAR Rl gw).locals_clock _ _

private theorem heapByteEff_dec_any {F : Type} {s : PanSemStateFiniteExact 64 F}
    (nm : MlS) (sh : ShapeHOL) (e : ExpHOL 64) (body : ProgHOL 64)
    {Rl : List Ivl} {gw : List String} (hAR : ArenaReady s)
    (hb : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      HeapByteEff (setVarHOLFinite nm v s) (evaluateHOLFiniteState (setVarHOLFinite nm v s) body).2 Rl gw) :
    HeapByteEff s (evaluateHOLFiniteState s (.dec nm sh e body)).2 Rl gw := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact HeapByteEff.refl hAR Rl gw
  · rename_i v hv
    split
    · rename_i hsh
      have h0 : HeapByteEff s (setVarHOLFinite nm v s) Rl gw :=
        (HeapByteEff.refl hAR Rl gw).locals_clock _ _
      exact (h0.trans (hb v hv hsh)).locals_clock _ _
    · exact HeapByteEff.refl hAR Rl gw

private theorem heapByteEff_ite_any {F : Type} {s : PanSemStateFiniteExact 64 F}
    (cond : ExpHOL 64) (yes no : ProgHOL 64) {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s)
    (hy : ∀ cw : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 → HeapByteEff s (evaluateHOLFiniteState s yes).2 Rl gw)
    (hn : ∀ cw : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word cw)) →
      cw = 0 → HeapByteEff s (evaluateHOLFiniteState s no).2 Rl gw) :
    HeapByteEff s (evaluateHOLFiniteState s (.ite cond yes no)).2 Rl gw := by
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i cw hcw
    split
    · rename_i hz; exact hn cw hcw hz
    · rename_i hnz; exact hy cw hcw hnz
  · exact HeapByteEff.refl hAR Rl gw

private theorem heapByteEff_seq_none {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p q : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (hnone : (evaluateHOLFiniteState s (.seq p q)).1 = none)
    (hp : (evaluateHOLFiniteState s p).1 = none → HeapByteEff s (evaluateHOLFiniteState s p).2 Rl gw)
    (hq : ∀ mid, evaluateHOLFiniteState s p = (none, mid) →
      (evaluateHOLFiniteState mid q).1 = none → HeapByteEff mid (evaluateHOLFiniteState mid q).2 Rl gw) :
    HeapByteEff s (evaluateHOLFiniteState s (.seq p q)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  rcases hev : evaluateHOLFiniteState s p with ⟨r, mid⟩
  simp only [hev] at hnone ⊢
  cases r with
  | none =>
    have hf := hp (by rw [hev])
    rw [hev] at hf
    exact hf.trans (hq mid hev hnone)
  | some r => simp at hnone


private theorem eval_rlp_header_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 =
      some (.returned v)) :
    ∃ hl : BitVec 64,
      v = .val (.word hl) ∧ 1 ≤ hl.toNat ∧ hl.toNat ≤ 9 := by
  have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 ≠
      some .timeOut := by rw [hret]; simp
  rcases hn : s.locals.lookup (ofString "n") with _ | nv
  · have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
        .seq (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n"))) (.return (.const 1)) .skip)
          (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
            (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
    rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
    simp [evalHOLExact, hn] at hret
  · rcases nv with ⟨⟨nw⟩⟩ | _ | _
    · obtain ⟨hret_eq, _⟩ := eval_rlp_header_len_body_exact s nw hc hn hnt
      rw [hret] at hret_eq
      injection hret_eq with h1; injection h1 with h2; subst h2
      have hbds := rlpHeaderLenPure_bounds nw.toNat
      have hbv : (BitVec.ofNat 64 (rlpHeaderLenPure nw.toNat)).toNat = rlpHeaderLenPure nw.toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact ⟨BitVec.ofNat 64 (rlpHeaderLenPure nw.toNat), rfl, by omega, by omega⟩
    · have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
          .seq (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n"))) (.return (.const 1)) .skip)
            (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
              (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
      simp [evalHOLExact, hn, valueIsWord] at hret
    · have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
          .seq (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n"))) (.return (.const 1)) .skip)
            (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
              (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
      simp [evalHOLExact, hn, valueIsWord] at hret

private theorem eval_rlp_bytes_encoded_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (nw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).1 =
      some (.returned v)) :
    ∃ el : BitVec 64,
      v = .val (.word el) ∧ 1 ≤ el.toNat ∧ el.toNat ≤ rlpHeaderLenPure nw.toNat + nw.toNat ∧
      el.toNat ≤ nw.toNat + 9 := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len =
      .seq
        (.ite (.op .and [
            .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
            .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))])
          (.return (.const 1#64))
          .skip)
        (.decCall (ofString "h") .one (ofString "rlp_header_len") [.var .local (ofString "n")]
          (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [
        .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
        .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))]) with _ | cv
  · simp [hcond] at hret
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · simp only [hcond] at hret
      by_cases hcw0 : cw = 0
      · rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hret
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
        have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "n")] = some [.val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
        have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_header_len") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_rlp_header_len) nw
          (by rw [hc]; exact WkBlockTxEnc.lookup_rlp_header_len)
        simp only [hargs, hlk] at hret
        by_cases hclk0 : s.clock = 0
        · simp [hclk0] at hret
        · simp only [hclk0, ↓reduceIte] at hret
          let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw)))
          have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rc, sc⟩
          have hcal' : evaluateHOLFiniteState
              (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw))))
              (sourceFnBody Guest.Software.guestFn_rlp_header_len) = (rc, sc) := hcal
          simp only [hcal'] at hret
          cases rc with
          | none => simp at hret
          | some rc' =>
            cases rc' with
            | returned vc =>
              have hnt_ent : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 ≠
                  some .timeOut := by rw [hcal]; simp
              obtain ⟨hret_hl, _⟩ := eval_rlp_header_len_body_exact entry nw hc hent_n hnt_ent
              rw [hcal] at hret_hl
              injection hret_hl with hret_hl'; injection hret_hl' with hvc; subst hvc
              set hlw := BitVec.ofNat 64 (rlpHeaderLenPure nw.toNat)
              have hbds := rlpHeaderLenPure_bounds nw.toNat
              have hhlw_nat : hlw.toNat = rlpHeaderLenPure nw.toNat := by
                dsimp [hlw]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hlw) : ValueHOL 64)) .one &&
                  shapeEqHOL (shapeOfHOLExact (.val (.word hlw) : ValueHOL 64)) .one) = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              simp only [hsh, ↓reduceIte] at hret
              let resSt := setVarHOLFinite (ofString "h") (.val (.word hlw)) { sc with locals := s.locals }
              rw [evaluateHOLFiniteState_return] at hret
              have hev_add : @evalHOLExact 64 F _ resSt.toExact (fun a => Classical.propDecidable (resSt.memaddrs a))
                  (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
                  some (.val (.word (hlw + nw))) := by
                have hne : ofString "h" ≠ ofString "n" := by decide
                simp [resSt, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  hne, Ne.symm hne, hn, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
              have hsz : sizeOfShapeWithContextHOL resSt.structs
                  (shapeOfHOLExact (.val (.word (hlw + nw)) : ValueHOL 64)) ≤ 32 := by simp [shapeOfHOLExact]
              rw [hev_add] at hret; dsimp only at hret; rw [if_pos hsz] at hret
              injection hret with hr; injection hr with hr'; subst hr'
              have hsum : (hlw + nw).toNat = hlw.toNat + nw.toNat := by
                rw [BitVec.toNat_add]; omega
              exact ⟨hlw + nw, rfl, by omega, by omega, by omega⟩
            | _ => simp at hret
      · rw [if_neg hcw0] at hret
        rw [evaluateHOLFiniteState_return] at hret
        simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
        subst hret
        have hbds := rlpHeaderLenPure_bounds nw.toNat
        exact ⟨1, rfl, by decide, by change 1 ≤ _; omega, by change 1 ≤ _; omega⟩
    · simp [hcond] at hret
    · simp [hcond] at hret

private theorem eval_rlp_value_encoded_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (pw nw : BitVec 64)
    (_hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).1 =
      some (.returned v)) :
    ∃ vl : BitVec 64,
      v = .val (.word vl) ∧ 1 ≤ vl.toNat ∧ vl.toNat ≤ rlpHeaderLenPure nw.toNat + nw.toNat ∧
      vl.toNat ≤ nw.toNat + 9 := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len =
      .dec (ofString "fb") .one (.const 0)
        (.seq
          (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
            (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
            .skip)
          (.call none (ofString "rlp_bytes_encoded_len")
            [.var .local (ofString "fb"), .var .local (ofString "n")])) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [hev0] at hret; dsimp only at hret; rw [if_pos hsh0] at hret
  let s1 := setVarHOLFinite (ofString "fb") (.val (.word 0)) s
  rw [evaluateHOLFiniteState_seq_line780] at hret
  rcases hite : evaluateHOLFiniteState s1
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
        .skip) with ⟨ri, si⟩
  have hsi_code : si.code = originalRuntimeCode := by
    have hm := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata s1
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p")))) .skip)).1
    rw [hite] at hm; exact hm.trans hc
  have hsi_n : ri = none → si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    intro hri
    have hn_keep := evaluate_avoidsLocal_flowing (ofString "n")
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p")))) .skip)
      (by decide) s1 (Or.inl (by rw [hite]; exact hri))
    rw [hite] at hn_keep
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
        show ofString "fb" ≠ ofString "n" by decide]
    exact hn_keep.trans hs1_n
  have hite_ev : evaluateHOLFiniteState (setVarHOLFinite (ofString "fb") (.val (.word 0)) s)
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
        .skip) = (ri, si) := hite
  rw [hite_ev] at hret
  cases ri with
  | some ri' =>
    dsimp only at hret
    injection hret with hret'; subst hret'
    rw [evaluateHOLFiniteState_ite] at hite
    split at hite
    · split at hite
      · rw [evaluateHOLFiniteState_skip] at hite; cases hite
      · rw [evaluateHOLFiniteState_assign] at hite
        split at hite
        · cases hite
        · split at hite <;> cases hite
    · cases hite
  | none =>
    dsimp only at hret
    have hsin := hsi_n rfl
    rw [evaluateHOLFiniteState_call] at hret
    rcases hfb : si.locals.lookup (ofString "fb") with _ | fbv
    · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb] at hret
    · rcases fbv with ⟨⟨fbw⟩⟩ | fs | ⟨nm, fs⟩
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [.val (.word fbw), .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hlk := pan_two_word_lookup si.code.lookup (ofString "rlp_bytes_encoded_len")
          (ofString "first_byte") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) fbw nw
          (by decide) (by rw [hsi_code]; exact lookup_rlp_bytes_encoded_len)
        simp only [hargs, hlk] at hret
        by_cases hclk0 : si.clock = 0
        · simp [hclk0] at hret
        · simp only [hclk0, ↓reduceIte] at hret
          let cmap := (HolFiniteMapExact.empty.update (ofString "first_byte", ValueHOL.val (.word fbw))).update
            (ofString "n", ValueHOL.val (.word nw))
          let entry := callEntryStateHOLFinite si cmap
          have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) with ⟨rc, sc⟩
          have hcal' : evaluateHOLFiniteState (callEntryStateHOLFinite si cmap)
              (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) = (rc, sc) := hcal
          rw [hcal'] at hret
          cases rc with
          | none => simp at hret
          | some rc' =>
            cases rc' with
            | returned vc =>
              obtain ⟨el, rfl, h1, hub1, hub2⟩ :=
                eval_rlp_bytes_encoded_len_returned entry hsi_code nw hent_n hnw60 vc (by rw [hcal])
              have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word el) : ValueHOL 64)) .one = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              simp only [hsh, ↓reduceIte] at hret
              injection hret with hr; injection hr with hr'; subst hr'
              exact ⟨el, rfl, h1, hub1, hub2⟩
            | _ => simp at hret
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [ValueHOL.rStruct fs, .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite si.code.lookup (ofString "rlp_bytes_encoded_len")
            [ValueHOL.rStruct fs, .val (.word nw)] = none := by
          rw [hsi_code]; unfold PanSemStateFiniteExact.lookupCodeHOLFinite
          have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len")
              [ValueHOL.rStruct fs, .val (.word nw)] = none := by
            simp [lookupCodeHOLExact, lookup_rlp_bytes_encoded_len, shapeOfHOLExact, shapeEqHOL]
          split
          · rfl
          · rename_i h; rw [hraw] at h; cases h
        rw [hargs] at hret; dsimp only at hret; rw [hnone] at hret; simp at hret
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [ValueHOL.nStruct nm fs, .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite si.code.lookup (ofString "rlp_bytes_encoded_len")
            [ValueHOL.nStruct nm fs, .val (.word nw)] = none := by
          rw [hsi_code]; unfold PanSemStateFiniteExact.lookupCodeHOLFinite
          have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len")
              [ValueHOL.nStruct nm fs, .val (.word nw)] = none := by
            simp [lookupCodeHOLExact, lookup_rlp_bytes_encoded_len, shapeOfHOLExact, shapeEqHOL]
          split
          · rfl
          · rename_i h; rw [hraw] at h; cases h
        rw [hargs] at hret; dsimp only at hret; rw [hnone] at hret; simp at hret

private theorem eval_node_ref_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).1 =
      some (.returned v)) :
    ∃ rl : BitVec 64, v = .val (.word rl) ∧ rl.toNat ≤ 33 := by
  have hb : sourceFnBody Guest.Software.guestFn_node_ref_len =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0)) (.return (.const 1)) .skip)
        (.seq
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
            (.return (.const 33)) .skip)
          (.seq
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
              (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip)
            (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                  (.return (.var .local (ofString "rl"))) .skip)
                (.return (.const 33)))))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780] at hret
  rcases h1 : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0)) (.return (.const 1)) .skip) with ⟨r1, s1⟩
  rw [h1] at hret
  cases r1 with
  | some r1' =>
    dsimp only at hret
    rw [evaluateHOLFiniteState_ite] at h1
    split at h1
    · split at h1
      · rw [evaluateHOLFiniteState_skip] at h1; cases h1
      · rw [evaluateHOLFiniteState_return] at h1
        simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at h1
        obtain ⟨rfl, _⟩ := h1; simp at hret; subst hret
        exact ⟨1, rfl, by decide⟩
    · injection h1 with hr _; injection hr with hr'; subst hr'; simp at hret
  | none =>
    have hs1 : s1 = s := by
      rw [evaluateHOLFiniteState_ite] at h1
      split at h1
      · split at h1
        · rw [evaluateHOLFiniteState_skip] at h1; exact (Prod.mk.inj h1).2.symm
        · exfalso; exact return_ne_none s _ (congrArg Prod.fst h1)
      · cases h1
    dsimp only at hret
    rw [hs1] at hret
    rw [evaluateHOLFiniteState_seq_line780] at hret
    rcases h2 : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
          (.return (.const 33)) .skip) with ⟨r2, s2⟩
    rw [h2] at hret
    cases r2 with
    | some r2' =>
      dsimp only at hret
      rw [evaluateHOLFiniteState_ite] at h2
      split at h2
      · split at h2
        · rw [evaluateHOLFiniteState_skip] at h2; cases h2
        · rw [evaluateHOLFiniteState_return] at h2
          simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at h2
          obtain ⟨rfl, _⟩ := h2; simp at hret; subst hret
          exact ⟨33, rfl, by decide⟩
      · injection h2 with hr _; injection hr with hr'; subst hr'; simp at hret
    | none =>
      have hs2 : s2 = s := by
        rw [evaluateHOLFiniteState_ite] at h2
        split at h2
        · split at h2
          · rw [evaluateHOLFiniteState_skip] at h2; exact (Prod.mk.inj h2).2.symm
          · exfalso; exact return_ne_none s _ (congrArg Prod.fst h2)
        · cases h2
      dsimp only at hret
      rw [hs2] at hret
      rw [evaluateHOLFiniteState_seq_line780] at hret
      rcases h3 : evaluateHOLFiniteState s
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨r3, s3⟩
      rw [h3] at hret
      have hmf := eval_call_mpt_fail_no_none_no_ret s 13 hc
      cases r3 with
      | some r3' =>
        dsimp only at hret
        injection hret with hret'; subst hret'
        rw [evaluateHOLFiniteState_ite] at h3
        split at h3
        · split at h3
          · rw [evaluateHOLFiniteState_skip] at h3; cases h3
          · exact False.elim (hmf.2 v (congrArg Prod.fst h3))
        · injection h3 with hr _; cases hr
      | none =>
        have hs3 : s3 = s := by
          rw [evaluateHOLFiniteState_ite] at h3
          split at h3
          · split at h3
            · rw [evaluateHOLFiniteState_skip] at h3; exact (Prod.mk.inj h3).2.symm
            · exact False.elim (hmf.1 (congrArg Prod.fst h3))
          · cases h3
        dsimp only at hret
        rw [hs3] at hret
        rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
        rcases hld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "child"), .const 16])) with _ | rlv
        · rw [hld] at hret; simp at hret
        · obtain ⟨rlw, rfl⟩ := R10Shards.P26_P28.eval_load_one_word s _ rlv hld
          have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word rlw) : ValueHOL 64)) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [hld] at hret; dsimp only at hret; rw [if_pos hsh] at hret
          let s4 := setVarHOLFinite (ofString "rl") (.val (.word rlw)) s
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
          have hcmp : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
              (.cmp .lower (.var .local (ofString "rl")) (.const 32)) =
              some (.val (.word (if rlw.toNat < 32 then 1 else 0))) := by
            simp [s4, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
          rw [hcmp] at hret; dsimp only at hret
          by_cases hlt32 : rlw.toNat < 32
          · rw [if_pos hlt32] at hret
            have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
            rw [if_neg h10, evaluateHOLFiniteState_return] at hret
            simp [s4, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
            subst hret
            exact ⟨rlw, rfl, by omega⟩
          · rw [if_neg hlt32] at hret
            simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret
            rw [evaluateHOLFiniteState_return] at hret
            simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
            subst hret
            exact ⟨33, rfl, by decide⟩

private theorem lookup_nibble_list_to_compact :
    originalRuntimeCode.lookup (ofString "nibble_list_to_compact") =
      some ([(ofString "nibs", .one), (ofString "n", .one), (ofString "is_leaf", .one), (ofString "dst", .one)],
        sourceFnBody Guest.Software.guestFn_nibble_list_to_compact, .one) :=
  lookup_of_guestAst_getElem 250 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nibble_list_to_compact) rfl

private theorem seq_none_rel {F : Type} (s : PanSemStateFiniteExact 64 F) (p q : ProgHOL 64)
    (h : (evaluateHOLFiniteState s (.seq p q)).1 = none) :
    (evaluateHOLFiniteState s p).1 = none ∧
    (evaluateHOLFiniteState (evaluateHOLFiniteState s p).2 q).1 = none ∧
    (evaluateHOLFiniteState s (.seq p q)).2 =
      (evaluateHOLFiniteState (evaluateHOLFiniteState s p).2 q).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  rcases hr : evaluateHOLFiniteState s p with ⟨r, t⟩
  simp only [hr] at h ⊢
  cases r with
  | none => exact ⟨rfl, h, rfl⟩
  | some r => simp at h

private theorem eval_noTopBreak : ∀ (p : ProgHOL 64),
    (p = .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
          (.op .or [
            .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
            .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]) ∨
     p = .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]) ∨
     p = .assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])) →
    ∀ {F : Type} (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st p).1 ≠ some .break := by
  rintro p (rfl | rfl | rfl) F st
  · rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  · rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  · rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp

private theorem eval_compactBody_noBreak {F : Type} (st : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState st
      (.seq
        (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
          (.op .or [
            .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
            .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
        (.seq
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
          (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))))).1 ≠ some .break := by
  let p0 : ProgHOL 64 := .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
    (.op .or [
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
      .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])])
  rw [evaluateHOLFiniteState_seq_line780]; dsimp only
  split
  · rw [evaluateHOLFiniteState_seq_line780]; dsimp only
    split
    · exact eval_noTopBreak _ (Or.inr (Or.inr rfl)) _
    · exact eval_noTopBreak _ (Or.inr (Or.inl rfl)) ((st.evaluateHOLFiniteState p0).2)
  · exact eval_noTopBreak _ (Or.inl rfl) st

private theorem eval_compactBody_noReturn {F : Type} (st : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64) :
    (evaluateHOLFiniteState st
      (.seq
        (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
          (.op .or [
            .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
            .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
        (.seq
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
          (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))))).1 ≠ some (.returned rv) := by
  have hnr : ∀ (p : ProgHOL 64),
      (p = .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
            (.op .or [
              .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
              .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]) ∨
       p = .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]) ∨
       p = .assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])) →
      ∀ (u : PanSemStateFiniteExact 64 F),
        (evaluateHOLFiniteState u p).1 ≠ some (.returned rv) := by
    rintro p (rfl | rfl | rfl) u
    · rw [evaluateHOLFiniteState_storeByte]
      split
      · split
        · split <;> simp
        · simp
      · simp
    · rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
    · rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  let p0 : ProgHOL 64 := .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
    (.op .or [
      .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
      .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])])
  rw [evaluateHOLFiniteState_seq_line780]; dsimp only
  split
  · rw [evaluateHOLFiniteState_seq_line780]; dsimp only
    split
    · exact hnr _ (Or.inr (Or.inr rfl)) _
    · exact hnr _ (Or.inr (Or.inl rfl)) ((st.evaluateHOLFiniteState p0).2)
  · exact hnr _ (Or.inl rfl) st

private def compactLoop : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    (.seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
        (.op .or [
          .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
          .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
      (.seq
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
        (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))))

private theorem eval_compactLoop_not_returned {F : Type} :
    ∀ (kk : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = kk →
      ∀ v', (evaluateHOLFiniteState st compactLoop).1 ≠ some (.returned v') := by
  intro kk
  induction kk using Nat.strong_induction_on with
  | h kk ih =>
    intro st hkk v' hbad
    rw [compactLoop, evaluateHOLFiniteState_while_fixClockRewrite, ← compactLoop] at hbad
    split at hbad
    · split at hbad
      · split at hbad
        · simp at hbad
        · let bProg : ProgHOL 64 :=
            .seq
              (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
                (.op .or [
                  .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                  .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
              (.seq
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
                (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])))
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) bProg
          have hnr_b := eval_compactBody_noReturn (decClockHOLFinite st) v'
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) bProg with ⟨rb1, mb1⟩
          change evaluateHOLFiniteState (decClockHOLFinite st) _ = (rb1, mb1) at hbr
          rw [hbr] at hbad hrem hnr_b
          cases rb1 with
          | none => exact ih mb1.clock (by simp [decClockHOLFinite, hkk] at hrem ⊢; omega) mb1 rfl v' hbad
          | some rb1' =>
            cases rb1' with
            | «continue» => exact ih mb1.clock (by simp [decClockHOLFinite, hkk] at hrem ⊢; omega) mb1 rfl v' hbad
            | returned v'' =>
              have hnr_b' := eval_compactBody_noReturn (decClockHOLFinite st) v''
              rw [hbr] at hnr_b'
              exact hnr_b' rfl
            | _ => simp at hbad
      · simp at hbad
    · simp at hbad

private theorem eval_compactLoop_eff {F : Type} :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F) (dst0 nw iw ow : BitVec 64) (cap : Nat),
      s.clock ≤ k →
      GuestInv s →
      dst0.toNat + cap ≤ heapLimit →
      s.locals.lookup (ofString "dst") = some (.val (.word dst0)) →
      s.locals.lookup (ofString "n") = some (.val (.word nw)) →
      s.locals.lookup (ofString "i") = some (.val (.word iw)) →
      s.locals.lookup (ofString "o") = some (.val (.word ow)) →
      1 ≤ ow.toNat →
      ow.toNat + (nw.toNat + 1 - iw.toNat) / 2 ≤ cap →
      iw.toNat ≤ nw.toNat + 1 →
      nw.toNat < 2 ^ 63 →
      (evaluateHOLFiniteState s compactLoop).1 = none →
      ∃ ow' : BitVec 64,
        1 ≤ ow'.toNat ∧ ow'.toNat ≤ cap ∧
        (evaluateHOLFiniteState s compactLoop).2.locals.lookup (ofString "o") = some (.val (.word ow')) ∧
        R10Shards.P26_P28.ByteEff s (evaluateHOLFiniteState s compactLoop).2 [(dst0.toNat, cap)] := by
  intro k
  induction k with
  | zero =>
    intro s dst0 nw iw ow cap hk _ _ _ hn hi ho how1 how_cap _ _ hnone
    unfold compactLoop at hnone ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hc] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have hk0 : s.clock = 0 := by omega
      simp [hlt, hk0] at hnone
    · simp only [hlt, ↓reduceIte]
      exact ⟨ow, how1, by omega, ho, (R10Shards.P26_P28.ByteEff.refl s _).locals_clock _ _⟩
  | succ k ih =>
    intro s dst0 nw iw ow cap hk hG hcap hdst hn hi ho how1 how_cap hi_le hnw_hi hnone
    rw [compactLoop, evaluateHOLFiniteState_while_fixClockRewrite, ← compactLoop] at hnone ⊢
    have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hc] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hlt : iw.toNat < nw.toNat
    · have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos hlt, if_pos h10] at hnone ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnone
      · rw [if_neg hk0] at hnone ⊢
        let sd := decClockHOLFinite s
        have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
        have hhl_he : heapLimit ≤ heapEnd := by decide
        have h264 : heapEnd < 2 ^ 64 := by decide
        have how_lt_cap : ow.toNat < cap := by omega
        let sbProg : ProgHOL 64 :=
          .storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
            (.op .or [
              .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
              .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])])
        let asgProg : ProgHOL 64 :=
          .seq (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
            (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1]))
        have hsb_eff : R10Shards.P26_P28.ByteEff sd
            (evaluateHOLFiniteState sd sbProg).2 [(dst0.toNat, cap)] := by
          apply R10Shards.P26_P28.byteEff_storeByte_at hGd _ _ dst0 ow.toNat cap (by omega)
            (fun _ => ⟨(dst0.toNat, cap), List.mem_singleton.2 rfl, le_refl _, le_refl _⟩) how_lt_cap
          have hod : sd.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hdst
          have hoo : sd.locals.lookup (ofString "o") = some (.val (.word ow)) := ho
          simp [evalHOLExact, evalListHOLExact, hod, hoo, wordOpHOL, wordOp, valueIsWord, valueWord,
            BitVec.add_zero]
        have hclk_b := evaluateHOLFiniteState_clock_le sd (.seq sbProg asgProg)
        rcases hbo_sd : evaluateHOLFiniteState (decClockHOLFinite s) (.seq sbProg asgProg) with ⟨rb, sb⟩
        have hbo_sd' : evaluateHOLFiniteState sd (.seq sbProg asgProg) = (rb, sb) := hbo_sd
        have hbo_raw : evaluateHOLFiniteState (decClockHOLFinite s)
            (.seq
              (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "o")])
                (.op .or [
                  .shift .lsl (.loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i")])) (.const 4),
                  .loadByte (.op .add [.var .local (ofString "nibs"), .var .local (ofString "i"), .const 1])]))
              (.seq (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 2]))
                (.assign .local (ofString "o") (.op .add [.var .local (ofString "o"), .const 1])))) = (rb, sb) := hbo_sd
        rw [hbo_raw] at hnone
        rw [hbo_sd'] at hclk_b
        have hnc : rb ≠ some .continue := by
          have := evaluate_noTopContinue (.seq sbProg asgProg) rfl sd
          rw [hbo_sd'] at this; exact this
        dsimp only at hnone ⊢
        cases rb with
        | some r' =>
          cases r' with
          | «continue» => exact absurd rfl hnc
          | «break» =>
            have hnb := eval_compactBody_noBreak sd
            rw [hbo_sd'] at hnb; exact absurd rfl hnb
          | _ => simp at hnone
        | none =>
          obtain ⟨hsb_none, hasg_none, hsb_eq⟩ := seq_none_rel sd sbProg asgProg (by rw [hbo_sd'])
          let s1 := (evaluateHOLFiniteState sd sbProg).2
          have hs1_loc : s1.locals = s.locals := by
            dsimp only [s1, sbProg] at hsb_none ⊢
            rw [evaluateHOLFiniteState_storeByte] at hsb_none ⊢
            split at hsb_none
            · split at hsb_none
              · split at hsb_none <;> simp_all [sd, decClockHOLFinite]
              · simp at hsb_none
            · simp at hsb_none
          have hasg_ev : evaluateHOLFiniteState s1 asgProg =
              (none, setVarHOLFinite (ofString "o") (.val (.word (ow + 1)))
                (setVarHOLFinite (ofString "i") (.val (.word (iw + 2))) s1)) := by
            dsimp only [asgProg]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hs1_loc]; exact hi
            have hs1_o : s1.locals.lookup (ofString "o") = some (.val (.word ow)) := by rw [hs1_loc]; exact ho
            have hne_io : ofString "i" ≠ ofString "o" := by decide
            simp [evalHOLExact, evalListHOLExact, hs1_i, hs1_o, hne_io, Ne.symm hne_io,
              wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero,
              isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
              setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              evaluateHOLFiniteState_assign]
          have hsb_def : sb = setVarHOLFinite (ofString "o") (.val (.word (ow + 1)))
              (setVarHOLFinite (ofString "i") (.val (.word (iw + 2))) s1) := by
            have := hsb_eq; rw [hbo_sd', hasg_ev] at this; exact this
          have hiw2_nat : (iw + 2).toNat = iw.toNat + 2 := by
            have h2val : ((2 : BitVec 64)).toNat = 2 := rfl
            rw [BitVec.toNat_add, h2val]; exact Nat.mod_eq_of_lt (by omega)
          have how1_nat : (ow + 1).toNat = ow.toNat + 1 := by
            have h1val : ((1 : BitVec 64)).toNat = 1 := rfl
            rw [BitVec.toNat_add, h1val]; exact Nat.mod_eq_of_lt (by omega)
          have heff_iter : R10Shards.P26_P28.ByteEff s sb [(dst0.toNat, cap)] := by
            rw [hsb_def]
            exact ((((R10Shards.P26_P28.ByteEff.refl s _).locals_clock sd.locals sd.clock).trans hsb_eff).locals_clock _ _).locals_clock _ _
          have hG_sb : GuestInv sb :=
            guestInv_congr heff_iter.code heff_iter.memaddrs heff_iter.shMemaddrs heff_iter.baseAddr hG
          have hsb_dst : sb.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_loc, hdst,
              show ofString "o" ≠ ofString "dst" by decide, show ofString "i" ≠ ofString "dst" by decide]
          have hsb_n : sb.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_loc, hn,
              show ofString "o" ≠ ofString "n" by decide, show ofString "i" ≠ ofString "n" by decide]
          have hsb_i : sb.locals.lookup (ofString "i") = some (.val (.word (iw + 2))) := by
            rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "o" ≠ ofString "i" by decide]
          have hsb_o : sb.locals.lookup (ofString "o") = some (.val (.word (ow + 1))) := by
            rw [hsb_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hclk_sb : sb.clock ≤ k := by
            change sb.clock ≤ s.clock - 1 at hclk_b; omega
          have hnone_sb : (evaluateHOLFiniteState sb compactLoop).1 = none := hnone
          obtain ⟨ow', how'1, how'_cap, hpost_o, heff_rest⟩ :=
            ih sb dst0 nw (iw + 2) (ow + 1) cap hclk_sb hG_sb hcap hsb_dst hsb_n hsb_i hsb_o
              (by omega) (by rw [how1_nat, hiw2_nat]; omega) (by rw [hiw2_nat]; omega)
              hnw_hi hnone_sb
          exact ⟨ow', how'1, how'_cap, hpost_o, (heff_iter.trans heff_rest).locals_clock _ _⟩
    · simp only [hlt, ↓reduceIte]
      exact ⟨ow, how1, by omega, ho, (R10Shards.P26_P28.ByteEff.refl s _).locals_clock _ _⟩

private theorem byteEff_fixClock_snd {F : Type} {s0 s1 post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {r : Option (PanSemResultExact 64)}
    (h : R10Shards.P26_P28.ByteEff s0 post Rl) :
    R10Shards.P26_P28.ByteEff s0 (fixClockHOLFinite s1 (r, post)).2 Rl := by
  dsimp only [fixClockHOLFinite]
  exact h.locals_clock post.locals _

private theorem byteEff_resVar_snd {F : Type} {s0 post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {nm : MlS} {old : Option (ValueHOL 64)}
    (h : R10Shards.P26_P28.ByteEff s0 post Rl) :
    R10Shards.P26_P28.ByteEff s0
      { post with locals := HolFiniteMapExact.resVarEq post.locals (nm, old) } Rl :=
  h.locals_clock _ post.clock

private theorem eval_nibble_list_to_compact_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nibsw nw islw dst0 : BitVec 64) (cap : Nat) (v : ValueHOL 64)
    (hG : GuestInv s)
    (hcap : dst0.toNat + cap ≤ heapLimit)
    (_hnibs : s.locals.lookup (ofString "nibs") = some (.val (.word nibsw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hisl : s.locals.lookup (ofString "is_leaf") = some (.val (.word islw)))
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hnw_hi : nw.toNat < 2 ^ 63)
    (hn_cap : nw.toNat / 2 + 1 ≤ cap)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).1 =
      some (.returned v)) :
    ∃ ow : BitVec 64,
      v = .val (.word ow) ∧ 1 ≤ ow.toNat ∧ ow.toNat ≤ nw.toNat / 2 + 1 ∧
      R10Shards.P26_P28.ByteEff s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).2
        [(dst0.toNat, cap)] := by
  have hcap_pos : 1 ≤ cap := by omega
  have hb : sourceFnBody Guest.Software.guestFn_nibble_list_to_compact =
      .dec (ofString "flag") .one (.panop .mul [.var .local (ofString "is_leaf"), .const 2])
        (.dec (ofString "i") .one (.const 0)
          (.seq
            (.ite (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0))
              (.storeByte (.var .local (ofString "dst"))
                (.panop .mul [.const 16, .var .local (ofString "flag")]))
              (.seq
                (.storeByte (.var .local (ofString "dst"))
                  (.op .add [
                    .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
                    .loadByte (.var .local (ofString "nibs"))]))
                (.assign .local (ofString "i") (.const 1))))
            (.dec (ofString "o") .one (.const 1)
              (.seq compactLoop (.return (.var .local (ofString "o"))))))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hret ⊢
  have hev_fl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.panop .mul [.var .local (ofString "is_leaf"), .const 2]) = some (.val (.word (islw * 2))) := by
    simp [evalHOLExact, evalListHOLExact, hisl, panOpHOL, valueIsWord, valueWord]
  have hsh_fl : shapeEqHOL .one (shapeOfHOLExact (.val (.word (islw * 2)) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hret ⊢
  rw [hev_fl] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_fl] at hret ⊢
  let s1 := setVarHOLFinite (ofString "flag") (.val (.word (islw * 2))) s
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  have hev_i0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  have hsh_0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hret ⊢
  rw [hev_i0] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_0] at hret ⊢
  let s2 := setVarHOLFinite (ofString "i") (.val (.word 0)) s1
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "i" ≠ ofString "n" by decide, show ofString "flag" ≠ ofString "n" by decide]
  have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
      show ofString "i" ≠ ofString "dst" by decide, show ofString "flag" ≠ ofString "dst" by decide]
  let hdrProg : ProgHOL 64 :=
    .ite (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0))
      (.storeByte (.var .local (ofString "dst"))
        (.panop .mul [.const 16, .var .local (ofString "flag")]))
      (.seq
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [
            .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
            .loadByte (.var .local (ofString "nibs"))]))
        (.assign .local (ofString "i") (.const 1)))
  let tailProg : ProgHOL 64 :=
    .dec (ofString "o") .one (.const 1) (.seq compactLoop (.return (.var .local (ofString "o"))))
  rcases hhdr : evaluateHOLFiniteState s2 hdrProg with ⟨rh, sh⟩
  have hhdr_cases : rh = none →
      ∃ iw : BitVec 64,
        (nw.toNat % 2 = 0 ∧ iw = 0 ∨ nw.toNat % 2 = 1 ∧ iw = 1) ∧
        sh.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
        sh.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        sh.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
        R10Shards.P26_P28.ByteEff s sh [(dst0.toNat, cap)] := by
    intro hrh
    dsimp only [hdrProg] at hhdr
    rw [evaluateHOLFiniteState_ite] at hhdr
    have hcond : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.cmp .equal (.op .and [.var .local (ofString "n"), .const 1]) (.const 0)) =
        some (.val (.word (if (nw &&& 1) = 0 then 1 else 0))) := by
      simp [evalHOLExact, evalListHOLExact, hs2_n, wordOpHOL, wordOp,
        Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord]
    rw [hcond] at hhdr
    dsimp only at hhdr
    have hs2_eff0 : R10Shards.P26_P28.ByteEff s s2 [(dst0.toNat, cap)] :=
      ((R10Shards.P26_P28.ByteEff.refl s _).locals_clock s1.locals s1.clock).locals_clock s2.locals s2.clock
    have hG_s2 : GuestInv s2 := guestInv_congr (s := s) rfl rfl rfl rfl hG
    by_cases hodd : nw &&& 1 = 0
    · have hcw : (if nw &&& 1 = 0 then (1 : BitVec 64) else 0) ≠ 0 := by rw [if_pos hodd]; decide
      rw [if_neg hcw] at hhdr
      have hpar : nw.toNat % 2 = 0 := by
        have := congrArg BitVec.toNat hodd
        simpa [BitVec.toNat_and, Nat.and_one_is_mod] using this
      have hsb_eff : R10Shards.P26_P28.ByteEff s2
          (evaluateHOLFiniteState s2
            (.storeByte (.var .local (ofString "dst"))
              (.panop .mul [.const 16, .var .local (ofString "flag")]))).2
          [(dst0.toNat, cap)] :=
        (R10Shards.P26_P28.byteEff_storeByte (s := s2) (Rl := [(dst0.toNat, cap)]) hG_s2
          (.var .local (ofString "dst"))
          (.panop .mul [.const 16, .var .local (ofString "flag")])
          (fun x hx _ => by
            have hxd : x = dst0 := (by simpa [evalHOLExact, hs2_dst] using hx : dst0 = x).symm
            rw [hxd]
            exact ⟨(dst0.toNat, cap), List.mem_singleton.mpr rfl, le_rfl, by dsimp; omega⟩)).1
      have hsb_loc : (evaluateHOLFiniteState s2
          (.storeByte (.var .local (ofString "dst"))
            (.panop .mul [.const 16, .var .local (ofString "flag")]))).2.locals = s2.locals := by
        rw [evaluateHOLFiniteState_storeByte] at hhdr ⊢
        split at hhdr
        · split at hhdr
          · split at hhdr <;> simp_all
          · simp_all
        · simp_all
      rw [hhdr] at hsb_eff hsb_loc
      refine ⟨0, Or.inl ⟨hpar, rfl⟩, ?_, by rw [hsb_loc]; exact hs2_n,
        by rw [hsb_loc]; exact hs2_dst, hs2_eff0.trans hsb_eff⟩
      rw [hsb_loc]; simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · have hcw : (if nw &&& 1 = 0 then (1 : BitVec 64) else 0) = 0 := by rw [if_neg hodd]
      rw [if_pos hcw] at hhdr
      have hpar : nw.toNat % 2 = 1 := by
        have : nw.toNat &&& 1 ≠ 0 := by
          intro hz; apply hodd; apply BitVec.eq_of_toNat_eq; simpa [BitVec.toNat_and] using hz
        have hlt2 : nw.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
        have hand_mod : nw.toNat &&& 1 = nw.toNat % 2 := Nat.and_one_is_mod nw.toNat
        omega
      obtain ⟨hsb_n, _, hseq_eq⟩ := seq_none_rel s2
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [
            .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
            .loadByte (.var .local (ofString "nibs"))]))
        (.assign .local (ofString "i") (.const 1))
        (by rw [hhdr]; exact hrh)
      let sm := (evaluateHOLFiniteState s2
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [
            .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
            .loadByte (.var .local (ofString "nibs"))]))).2
      have hsb_eff : R10Shards.P26_P28.ByteEff s2 sm [(dst0.toNat, cap)] :=
        (R10Shards.P26_P28.byteEff_storeByte (s := s2) (Rl := [(dst0.toNat, cap)]) hG_s2
          (.var .local (ofString "dst"))
          (.op .add [
            .panop .mul [.const 16, .op .add [.var .local (ofString "flag"), .const 1]],
            .loadByte (.var .local (ofString "nibs"))])
          (fun x hx _ => by
            have hxd : x = dst0 := (by simpa [evalHOLExact, hs2_dst] using hx : dst0 = x).symm
            rw [hxd]
            exact ⟨(dst0.toNat, cap), List.mem_singleton.mpr rfl, le_rfl, by dsimp; omega⟩)).1
      have hsm_loc : sm.locals = s2.locals := by
        dsimp only [sm] at hsb_n ⊢
        rw [evaluateHOLFiniteState_storeByte] at hsb_n ⊢
        split at hsb_n
        · split at hsb_n
          · split at hsb_n <;> simp_all
          · simp at hsb_n
        · simp at hsb_n
      have hasg_ev : evaluateHOLFiniteState sm (.assign .local (ofString "i") (.const 1)) =
          (none, setVarHOLFinite (ofString "i") (.val (.word 1)) sm) := by
        rw [evaluateHOLFiniteState_assign]
        have hsm_i : sm.locals.lookup (ofString "i") = some (.val (.word 0)) := by
          rw [hsm_loc]; simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        simp [evalHOLExact, isValidValueHOLExact, lookupKvarHOLExact, hsm_i,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
      have hsh_eq : sh = setVarHOLFinite (ofString "i") (.val (.word 1)) sm := by
        have := hseq_eq; rw [hhdr, hasg_ev] at this; exact this
      refine ⟨1, Or.inr ⟨hpar, rfl⟩, ?_, ?_, ?_, ?_⟩
      · rw [hsh_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · rw [hsh_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsm_loc, hs2_n,
          show ofString "i" ≠ ofString "n" by decide]
      · rw [hsh_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsm_loc, hs2_dst,
          show ofString "i" ≠ ofString "dst" by decide]
      · rw [hsh_eq]; exact (hs2_eff0.trans hsb_eff).locals_clock _ _
  change (evaluateHOLFiniteState s2 (.seq hdrProg tailProg)).1 = some (.returned v) at hret
  have hrh_none : rh = none := by
    rcases rh with _ | r0
    · rfl
    · exfalso
      rw [evaluateHOLFiniteState_seq_line780, hhdr] at hret
      dsimp only at hret
      injection hret with hr0; subst hr0
      dsimp only [hdrProg] at hhdr
      rw [evaluateHOLFiniteState_ite] at hhdr
      split at hhdr
      · split at hhdr
        · rw [evaluateHOLFiniteState_seq_line780] at hhdr; dsimp only at hhdr
          split at hhdr
          · rw [evaluateHOLFiniteState_assign] at hhdr
            split at hhdr
            · simp at hhdr
            · split at hhdr <;> simp at hhdr
          · rename_i r1 h1
            rw [evaluateHOLFiniteState_storeByte] at h1
            split at h1
            · split at h1
              · split at h1 <;> simp_all
              · simp_all
            · simp_all
        · rw [evaluateHOLFiniteState_storeByte] at hhdr
          split at hhdr
          · split at hhdr
            · split at hhdr <;> simp at hhdr
            · simp at hhdr
          · simp at hhdr
      · simp at hhdr
  obtain ⟨iw, hpar_iw, hsh_i, hsh_n, hsh_dst, hsh_eff⟩ := hhdr_cases hrh_none
  change ∃ ow : BitVec 64,
    v = .val (.word ow) ∧ 1 ≤ ow.toNat ∧ ow.toNat ≤ nw.toNat / 2 + 1 ∧
    R10Shards.P26_P28.ByteEff s
      { (evaluateHOLFiniteState s2 (.seq hdrProg tailProg)).2 with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s2 (.seq hdrProg tailProg)).2.locals
            (ofString "i", s1.locals.lookup (ofString "i")))
          (ofString "flag", s.locals.lookup (ofString "flag")) }
      [(dst0.toNat, cap)]
  rw [evaluateHOLFiniteState_seq_line780, hhdr, hrh_none] at hret ⊢
  dsimp only [tailProg] at hret ⊢
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  have hev_o1 : @evalHOLExact 64 F _ sh.toExact (fun a => Classical.propDecidable (sh.memaddrs a))
      (.const 1) = some (.val (.word 1)) := rfl
  have hsh_1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hret ⊢
  rw [hev_o1] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_1] at hret ⊢
  let so := setVarHOLFinite (ofString "o") (.val (.word 1)) sh
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  set rlp := (evaluateHOLFiniteState so compactLoop).1 with hrlp_def
  set slp := (evaluateHOLFiniteState so compactLoop).2 with hslp_def
  have hlp : evaluateHOLFiniteState so compactLoop = (rlp, slp) := Prod.ext hrlp_def.symm hslp_def.symm
  rw [hlp] at hret ⊢
  dsimp only at hret ⊢
  have hrlp_none : rlp = none := by
    rcases hr_cases : rlp with _ | r0
    · rfl
    · exfalso
      rw [hr_cases] at hret
      dsimp only at hret
      injection hret with hr0; subst hr0
      exact eval_compactLoop_not_returned so.clock so rfl v (by rw [hlp, hr_cases])
  rw [hrlp_none] at hret hlp ⊢
  dsimp only at hret ⊢
  have hG_so : GuestInv so :=
    guestInv_congr hsh_eff.code hsh_eff.memaddrs hsh_eff.shMemaddrs hsh_eff.baseAddr hG
  have hso_dst : so.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsh_dst,
      show ofString "o" ≠ ofString "dst" by decide]
  have hso_n : so.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsh_n,
      show ofString "o" ≠ ofString "n" by decide]
  have hso_i : so.locals.lookup (ofString "i") = some (.val (.word iw)) := by
    simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsh_i,
      show ofString "o" ≠ ofString "i" by decide]
  have hso_o : so.locals.lookup (ofString "o") = some (.val (.word 1)) := by
    simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ho_cap_init : ((1 : BitVec 64)).toNat + (nw.toNat + 1 - iw.toNat) / 2 ≤ cap := by
    rcases hpar_iw with ⟨hp0, rfl⟩ | ⟨hp1, rfl⟩
    · change 1 + (nw.toNat + 1) / 2 ≤ cap; omega
    · change 1 + (nw.toNat + 1 - 1) / 2 ≤ cap; omega
  have hi_le_init : iw.toNat ≤ nw.toNat + 1 := by
    rcases hpar_iw with ⟨_, rfl⟩ | ⟨hp1, rfl⟩
    · change 0 ≤ nw.toNat + 1; omega
    · change 1 ≤ nw.toNat + 1; omega
  have how_cap_tight : ((1 : BitVec 64)).toNat + (nw.toNat + 1 - iw.toNat) / 2 ≤ nw.toNat / 2 + 1 := by
    rcases hpar_iw with ⟨hp0, rfl⟩ | ⟨hp1, rfl⟩
    · change 1 + (nw.toNat + 1) / 2 ≤ nw.toNat / 2 + 1; omega
    · change 1 + (nw.toNat + 1 - 1) / 2 ≤ nw.toNat / 2 + 1; omega
  obtain ⟨ow, how1, how_bound, hslp_o, heff_lp⟩ :=
    eval_compactLoop_eff so.clock so dst0 nw iw 1 (nw.toNat / 2 + 1) le_rfl hG_so (by omega)
      hso_dst hso_n hso_i hso_o (by decide) how_cap_tight hi_le_init hnw_hi
      (by rw [hlp])
  have hslp_o' : slp.locals.lookup (ofString "o") = some (.val (.word ow)) := by
    rw [hlp] at hslp_o; exact hslp_o
  have heff_lp' : R10Shards.P26_P28.ByteEff so slp [(dst0.toNat, nw.toNat / 2 + 1)] := by
    rw [hlp] at heff_lp; exact heff_lp
  have heff_lp_cap : R10Shards.P26_P28.ByteEff so slp [(dst0.toNat, cap)] :=
    heff_lp'.mono (fun i hi _ => by
      simp only [List.mem_singleton] at hi; subst hi
      exact ⟨(dst0.toNat, cap), List.mem_singleton.mpr rfl, le_rfl, by dsimp; omega⟩)
  rw [evaluateHOLFiniteState_return] at hret ⊢
  simp [evalHOLExact, hslp_o', shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret ⊢
  subst hret
  refine ⟨ow, rfl, how1, how_bound, ?_⟩
  exact ((hsh_eff.locals_clock so.locals so.clock).trans heff_lp_cap).locals_clock _ _

private theorem eval_nibble_list_to_compact_heapByteEff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nibsw nw islw dst0 : BitVec 64) (cap : Nat)
    (gw : List String) (v : ValueHOL 64)
    (hAR : ArenaReady s)
    (hcap : dst0.toNat + cap ≤ heapLimit)
    (hnibs : s.locals.lookup (ofString "nibs") = some (.val (.word nibsw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hisl : s.locals.lookup (ofString "is_leaf") = some (.val (.word islw)))
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hnw_hi : nw.toNat < 2 ^ 63)
    (hn_cap : nw.toNat / 2 + 1 ≤ cap)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).1 =
      some (.returned v)) :
    ∃ ow : BitVec 64,
      v = .val (.word ow) ∧ 1 ≤ ow.toNat ∧ ow.toNat ≤ nw.toNat / 2 + 1 ∧
      HeapByteEff s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).2
        [(dst0.toNat, cap)] gw := by
  obtain ⟨ow, rfl, how1, how_bound, hbeff⟩ :=
    eval_nibble_list_to_compact_returned s nibsw nw islw dst0 cap v
      hAR.1 hcap hnibs hn hisl hdst hnw_hi hn_cap hret
  exact ⟨ow, rfl, how1, how_bound, heapByteEff_of_p26_byteEff hAR hbeff⟩

private theorem eval_call_local_nibble_list_to_compact_heapByteEff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String)
    (nibsExp nExp islExp dstExp : ExpHOL 64)
    (nibsw nw islw dst0 : BitVec 64) (cap : Nat) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hnibs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nibsExp =
      some (.val (.word nibsw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hisl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) islExp =
      some (.val (.word islw)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hcap : dst0.toNat + cap ≤ heapLimit)
    (hnw_hi : nw.toNat < 2 ^ 63)
    (hn_cap : nw.toNat / 2 + 1 ≤ cap)
    (hsub : (∃ j ∈ Rl, j.1 ≤ dst0.toNat ∧ dst0.toNat + cap ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ dst0.toNat ∧ dst0.toNat + cap ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ dst0.toNat ∧ dst0.toNat + cap ≤ heapLimit))
    (hnone : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "nibble_list_to_compact")
        [nibsExp, nExp, islExp, dstExp])).1 = none) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "nibble_list_to_compact")
        [nibsExp, nExp, islExp, dstExp])
    ∃ ow : BitVec 64,
      1 ≤ ow.toNat ∧ ow.toNat ≤ nw.toNat / 2 + 1 ∧
      out.2.locals = s.locals.update (ofString lname, .val (.word ow)) ∧
      HeapByteEff s out.2 Rl gw := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [nibsExp, nExp, islExp, dstExp] =
      some [.val (.word nibsw), .val (.word nw), .val (.word islw), .val (.word dst0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hnibs, hn, hisl, hdst]
  have hlk := pan_four_word_lookup s.code.lookup (ofString "nibble_list_to_compact")
    (ofString "nibs") (ofString "n") (ofString "is_leaf") (ofString "dst")
    (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact) nibsw nw islw dst0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_nibble_list_to_compact)
  simp only [hargs, hlk] at hnone ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnone
  · simp only [hcz, ↓reduceIte] at hnone ⊢
    let cmap := (((HolFiniteMapExact.empty.update (ofString "nibs", ValueHOL.val (.word nibsw))).update
      (ofString "n", ValueHOL.val (.word nw))).update (ofString "is_leaf", ValueHOL.val (.word islw))).update
      (ofString "dst", ValueHOL.val (.word dst0))
    let ent := callEntryStateHOLFinite s cmap
    have hent_nibs : ent.locals.lookup (ofString "nibs") = some (.val (.word nibsw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "dst" ≠ ofString "nibs" by decide,
        show ofString "is_leaf" ≠ ofString "nibs" by decide,
        show ofString "n" ≠ ofString "nibs" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "dst" ≠ ofString "n" by decide,
        show ofString "is_leaf" ≠ ofString "n" by decide]
    have hent_isl : ent.locals.lookup (ofString "is_leaf") = some (.val (.word islw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "dst" ≠ ofString "is_leaf" by decide]
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hent_AR : ArenaReady ent := localsFree_arenaReady s _ _ hAR
    generalize hcal : evaluateHOLFiniteState (callEntryStateHOLFinite s
        ((((HolFiniteMapExact.empty.update (ofString "nibs", ValueHOL.val (.word nibsw))).update
          (ofString "n", ValueHOL.val (.word nw))).update (ofString "is_leaf", ValueHOL.val (.word islw))).update
          (ofString "dst", ValueHOL.val (.word dst0))))
        (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact) = calOut at hnone ⊢
    rcases calOut with ⟨rc, sc⟩
    have hcal_ent : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact) =
        (rc, sc) := hcal
    cases rc with
    | none => simp at hnone
    | some rc' =>
      cases rc' with
      | returned vc =>
        obtain ⟨ow, rfl, how1, how_bound, heff_ent⟩ :=
          eval_nibble_list_to_compact_heapByteEff ent nibsw nw islw dst0 cap gw vc
            hent_AR hcap hent_nibs hent_n hent_isl hent_dst hnw_hi hn_cap (by rw [hcal_ent])
        rw [hcal_ent] at heff_ent
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word ow) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word ow)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh, if_pos hval]
        have heff0 : HeapByteEff s ent [(dst0.toNat, cap)] gw :=
          (HeapByteEff.refl hAR [(dst0.toNat, cap)] gw).locals_clock ent.locals ent.clock
        have heff_out : HeapByteEff s
            (setVarHOLFinite (ofString lname) (.val (.word ow)) { sc with locals := s.locals })
            [(dst0.toNat, cap)] gw :=
          (heff0.trans heff_ent).locals_clock _ _
        refine ⟨ow, how1, how_bound, rfl, heff_out.mono ?_ (fun _ hg => hg)⟩
        intro i hi _
        simp only [List.mem_singleton] at hi
        subst hi
        exact hsub
      | _ => simp at hnone


private theorem eval_nibble_list_to_compact_nodeHeap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (nibsw nw islw dst0 : BitVec 64) (cap : Nat) (gw : List String) (v : ValueHOL 64)
    (hAR : ArenaReady s) (hN : NodeHeap s Nd)
    (hcap : dst0.toNat + cap ≤ heapLimit)
    (hnibs : s.locals.lookup (ofString "nibs") = some (.val (.word nibsw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hisl : s.locals.lookup (ofString "is_leaf") = some (.val (.word islw)))
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hnw_hi : nw.toNat < 2 ^ 63)
    (hn_cap : nw.toNat / 2 + 1 ≤ cap)
    (hdisj : (∀ o ∈ nodeExtents s Nd, Disj (dst0.toNat, cap) o) ∨ globN s "heap_ptr" ≤ dst0.toNat)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).2
    ∃ ow : BitVec 64,
      v = .val (.word ow) ∧ 1 ≤ ow.toNat ∧ ow.toNat ≤ nw.toNat / 2 + 1 ∧
      HeapByteEff s post [(dst0.toNat, cap)] gw ∧
      NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  intro post; dsimp only [post]
  obtain ⟨ow, rfl, how1, how_bound, heff⟩ :=
    eval_nibble_list_to_compact_heapByteEff s nibsw nw islw dst0 cap gw v
      hAR hcap hnibs hn hisl hdst hnw_hi hn_cap hret
  refine ⟨ow, rfl, how1, how_bound, heff, ?_⟩
  rcases hdisj with hdj | hfresh
  · exact nodeHeap_of_heapByteEff_disj hAR hN heff (fun iv hiv _ o ho => by
      simp only [List.mem_singleton] at hiv; subst hiv; exact hdj o ho)
  · have heff_empty : HeapByteEff s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_nibble_list_to_compact)).2 [] gw :=
      heff.mono
        (fun i hi _ => by
          simp only [List.mem_singleton] at hi; subst hi
          exact Or.inr (Or.inr ⟨hfresh, hcap⟩))
        (fun _ hg => hg)
    exact nodeHeap_of_heapByteEff_disj hAR hN heff_empty (fun _ hiv => by simp at hiv)

private theorem eval_call_local_nibble_list_to_compact_nodeHeap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (lname : String)
    (nibsExp nExp islExp dstExp : ExpHOL 64)
    (nibsw nw islw dst0 : BitVec 64) (cap : Nat) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hN : NodeHeap s Nd)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hnibs : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nibsExp =
      some (.val (.word nibsw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hisl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) islExp =
      some (.val (.word islw)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hcap : dst0.toNat + cap ≤ heapLimit)
    (hnw_hi : nw.toNat < 2 ^ 63)
    (hn_cap : nw.toNat / 2 + 1 ≤ cap)
    (hsub : (∃ j ∈ Rl, j.1 ≤ dst0.toNat ∧ dst0.toNat + cap ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ dst0.toNat ∧ dst0.toNat + cap ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ dst0.toNat ∧ dst0.toNat + cap ≤ heapLimit))
    (hdisj : ∀ iv ∈ Rl, 0 < iv.2 → ∀ o ∈ nodeExtents s Nd, Disj iv o)
    (hnone : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "nibble_list_to_compact")
        [nibsExp, nExp, islExp, dstExp])).1 = none) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "nibble_list_to_compact")
        [nibsExp, nExp, islExp, dstExp])
    ∃ ow : BitVec 64,
      1 ≤ ow.toNat ∧ ow.toNat ≤ nw.toNat / 2 + 1 ∧
      out.2.locals = s.locals.update (ofString lname, .val (.word ow)) ∧
      HeapByteEff s out.2 Rl gw ∧
      NodeHeap out.2 Nd ∧ nodeExtents out.2 Nd = nodeExtents s Nd := by
  intro out; dsimp only [out]
  obtain ⟨ow, how1, how_bound, hloc, heff⟩ :=
    eval_call_local_nibble_list_to_compact_heapByteEff s lname nibsExp nExp islExp dstExp
      nibsw nw islw dst0 cap Rl gw hcode hAR hl_old hnibs hn hisl hdst hcap hnw_hi hn_cap hsub hnone
  exact ⟨ow, how1, how_bound, hloc, heff, nodeHeap_of_heapByteEff_disj hAR hN heff hdisj⟩

private theorem lookup_node_hash_cached :
    originalRuntimeCode.lookup (ofString "node_hash_cached") =
      some ([(ofString "node", .one)],
        sourceFnBody Guest.Software.guestFn_node_hash_cached, .one) :=
  lookup_of_guestAst_getElem 288 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_hash_cached) rfl

private theorem lookup_node_write_ref :
    originalRuntimeCode.lookup (ofString "node_write_ref") =
      some ([(ofString "child", .one), (ofString "dst", .one)],
        sourceFnBody Guest.Software.guestFn_node_write_ref, .one) :=
  lookup_of_guestAst_getElem 289 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_write_ref) rfl


private theorem keccakBufIvls_disj_of_buffers {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat}
    (hdisj : ∀ o ∈ nodeExtents s Nd,
      Disj (bufferRegion s ("keccak_pad", 136)) o ∧
      Disj (bufferRegion s ("keccak_st", 200)) o) :
    ∀ e ∈ keccakBufIvls s, ∀ o ∈ nodeExtents s Nd, Disj e o := by
  intro e he o ho
  simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact (hdisj o ho).1
  · exact (hdisj o ho).2


private def nodeRefBytes {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat) : Nat :=
  if c = 0 then 1
  else if memW s c = 0 then 33
  else if memW s (c + 16) < 32 then memW s (c + 16)
  else 33

private theorem nodeRefBytes_le33 {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat) :
    nodeRefBytes s c ≤ 33 := by
  unfold nodeRefBytes
  split_ifs <;> omega

private theorem nodeRefBytes_congr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd : List Nat}
    (hw0 : ∀ n ∈ Nd, memW post n = memW s n)
    (hw16 : ∀ n ∈ Nd, memW post (n + 16) = memW s (n + 16))
    {c : Nat} (hc : RootIn Nd c) :
    nodeRefBytes post c = nodeRefBytes s c := by
  rcases hc with rfl | hmem
  · simp [nodeRefBytes]
  · unfold nodeRefBytes
    by_cases hc0 : c = 0
    · simp [hc0]
    · simp [hc0, hw0 c hmem, hw16 c hmem]

private theorem node_memW_eq_of_hashOnly_cell_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {extra : List Ivl}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (hextra_disj : ∀ e ∈ extra, 0 < e.2 → ∀ o ∈ nodeExtents s Nd, Disj e o)
    (hcf : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ e ∈ extra, CellHitsPos a.toNat e) ∨
      CellHitsPos a.toNat (freeGap s) ∨
      CellHitsPos a.toNat (heapFree s) ∨
      (∃ m ∈ Nd, a.toNat = m + 24))
    {n off : Nat} (hn : n ∈ Nd) (hoff8 : off % 8 = 0)
    (hoff_lt : off + 8 ≤ nodeSize (memW s n)) (hoff_ne24 : off ≠ 24) :
    memW post (n + off) = memW s (n + off) := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
  have hn8 : n % 8 = 0 := hw_n.1
  have ha_lt : n + off < 2 ^ 64 := by
    have := hin_n.2; dsimp [nodeIvl] at this; omega
  apply memW_eq_of_cell_eq
  by_contra hne
  have ha_nat : (BitVec.ofNat 64 (n + off)).toNat = n + off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have ho_mem : nodeIvl s n ∈ nodeExtents s Nd := by
    unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
  rcases hcf (BitVec.ofNat 64 (n + off)) hne with
    ⟨iv, hex, hpos, hc1, hc2⟩ | ⟨hpos_fg, hfg1, hfg2⟩ | ⟨hpos_hf, hhf1, hhf2⟩ | ⟨m, hm, heq⟩
  · rw [ha_nat] at hc1 hc2
    have hdj := hextra_disj iv hex hpos (nodeIvl s n) ho_mem
    dsimp [nodeIvl] at hdj
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · rw [ha_nat] at hfg1 hfg2
    have hdj := P3MptSet.disj_allocated_freeGap hAs.2 hal_n
    dsimp [nodeIvl, freeGap] at hdj hpos_fg hfg1 hfg2
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · rw [ha_nat] at hhf1 hhf2
    have hdj := P3MptSet.disj_allocated_heapFree hAs.2 hal_n
    dsimp [nodeIvl, heapFree] at hdj hpos_hf hhf1 hhf2
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  · rw [ha_nat] at heq
    by_cases hnm : n = m
    · subst hnm; omega
    · have hdj := hN.2 n hn m hm hnm
      have hsz_m := nodeSize_ge32 (memW s m)
      dsimp [nodeIvl] at hdj
      rcases hdj with h0 | h0 | hd1 | hd2 <;> omega

private theorem eval_node_ref_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (child0 : BitVec 64) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hN : NodeHeap s Nd)
    (hchild_in : RootIn Nd child0.toNat)
    (hloc : s.locals.lookup (ofString "child") = some (.val (.word child0)))
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).1 =
      some (.returned v)) :
    ∃ rl : BitVec 64,
      v = .val (.word rl) ∧ rl.toNat = nodeRefBytes s child0.toNat ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2.clock } := by
  have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_node_ref_len) rfl s hc
  have hb : sourceFnBody Guest.Software.guestFn_node_ref_len =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0)) (.return (.const 1)) .skip)
        (.seq
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
            (.return (.const 33)) .skip)
          (.seq
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
              (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip)
            (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                  (.return (.var .local (ofString "rl"))) .skip)
                (.return (.const 33)))))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780] at hret
  have hcmp0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "child")) (.const 0)) =
      some (.val (.word (if child0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hloc, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hc0 : child0 = 0
  · subst hc0
    rw [evaluateHOLFiniteState_ite, hcmp0] at hret
    simp only [↓reduceIte] at hret
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10, evaluateHOLFiniteState_return] at hret
    simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
    subst hret
    exact ⟨1, rfl, by simp [nodeRefBytes], hro⟩
  · have hc0_nat : child0.toNat ≠ 0 := fun h => hc0 (BitVec.eq_of_toNat_eq h)
    have hchild_nd : child0.toNat ∈ Nd := by
      rcases hchild_in with h0 | hm
      · exact absurd h0 hc0_nat
      · exact hm
    rw [evaluateHOLFiniteState_ite, hcmp0, if_neg hc0] at hret
    simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    obtain ⟨_, _, hin_c, hw_c, _⟩ := hN.1 child0.toNat hchild_nd
    have hsz_c := nodeSize_ge32 (memW s child0.toNat)
    have hhi_c : child0.toNat + nodeSize (memW s child0.toNat) ≤ 2 ^ 64 := by
      have := hin_c.2; dsimp [nodeIvl] at this; omega
    obtain ⟨kw, hld0, hkw_nat⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 0)
      hw_c (by decide) (by omega) hhi_c
      (e := .op .add [.var .local (ofString "child"), .const 0])
      (by simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord])
    simp only [Nat.add_zero] at hkw_nat
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
    have hcmp_k : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0)) =
        some (.val (.word (if kw = 0 then 1 else 0))) := by
      unfold evalHOLExact
      rw [hld0]
      simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_k] at hret; dsimp only at hret
    by_cases hkw0 : kw = 0
    · rw [if_pos hkw0] at hret
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_neg h10, evaluateHOLFiniteState_return] at hret
      simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
      subst hret
      have hm0 : memW s child0.toNat = 0 := by rw [← hkw_nat, hkw0]; rfl
      exact ⟨33, rfl, by simp [nodeRefBytes, hc0_nat, hm0], hro⟩
    · have hm_ne0 : memW s child0.toNat ≠ 0 := by
        intro h; apply hkw0; apply BitVec.eq_of_toNat_eq; rw [hkw_nat, h]; rfl
      rw [if_neg hkw0] at hret
      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret
      rw [evaluateHOLFiniteState_seq_line780] at hret
      rcases h3 : evaluateHOLFiniteState s
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨r3, s3⟩
      rw [h3] at hret
      have hmf := eval_call_mpt_fail_no_none_no_ret s 13 hc
      cases r3 with
      | some r3' =>
        dsimp only at hret
        injection hret with hret'; subst hret'
        rw [evaluateHOLFiniteState_ite] at h3
        split at h3
        · split at h3
          · rw [evaluateHOLFiniteState_skip] at h3; cases h3
          · exact False.elim (hmf.2 v (congrArg Prod.fst h3))
        · injection h3 with hr _; cases hr
      | none =>
        have hs3 : s3 = s := by
          rw [evaluateHOLFiniteState_ite] at h3
          split at h3
          · split at h3
            · rw [evaluateHOLFiniteState_skip] at h3; exact (Prod.mk.inj h3).2.symm
            · exact False.elim (hmf.1 (congrArg Prod.fst h3))
          · cases h3
        dsimp only at hret
        rw [hs3, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
        obtain ⟨rlw, hld16, hrlw_nat⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 16)
          hw_c (by decide) (by omega) hhi_c
          (e := .op .add [.var .local (ofString "child"), .const 16])
          (by simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord])
        have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word rlw) : ValueHOL 64)) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [hld16] at hret; dsimp only at hret; rw [if_pos hsh] at hret
        let s4 := setVarHOLFinite (ofString "rl") (.val (.word rlw)) s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
        have hcmp : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
            (.cmp .lower (.var .local (ofString "rl")) (.const 32)) =
            some (.val (.word (if rlw.toNat < 32 then 1 else 0))) := by
          simp [s4, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
        rw [hcmp] at hret; dsimp only at hret
        by_cases hlt32 : rlw.toNat < 32
        · rw [if_pos hlt32] at hret
          have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
          rw [if_neg h10, evaluateHOLFiniteState_return] at hret
          simp [s4, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
          subst hret
          have hlt32' : memW s (child0.toNat + 16) < 32 := by rw [← hrlw_nat]; exact hlt32
          exact ⟨rlw, rfl, by simp [nodeRefBytes, hc0_nat, hm_ne0, hlt32', hrlw_nat], hro⟩
        · rw [if_neg hlt32] at hret
          simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret
          rw [evaluateHOLFiniteState_return] at hret
          simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
          subst hret
          have hlt32' : ¬ memW s (child0.toNat + 16) < 32 := by rw [← hrlw_nat]; exact hlt32
          exact ⟨33, rfl, by simp [nodeRefBytes, hc0_nat, hm_ne0, hlt32'], hro⟩

private theorem nodeHeap_of_hashOnly_heapByteEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {extra : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (heff : HeapByteEff s post (Nd.map (fun n => (n + 24, 8)) ++ extra) gw)
    (hextra_disj : ∀ e ∈ extra, 0 < e.2 → ∀ o ∈ nodeExtents s Nd, Disj e o) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd ∧
    (∀ n ∈ Nd, memW post n = memW s n ∧ memW post (n + 8) = memW s (n + 8) ∧
      memW post (n + 16) = memW s (n + 16)) := by
  have heff_cache : HeapByteEff s post (nodeCacheIvls Nd ++ extra) gw :=
    heff.mono
      (fun i hi _ => by
        rcases List.mem_append.1 hi with hm24 | hex
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
          exact Or.inl ⟨(m + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩),
            by dsimp; omega, by dsimp; omega⟩
        · exact Or.inl ⟨i, List.mem_append_right _ hex, le_rfl, le_rfl⟩)
      (fun _ hg => hg)
  have hcf : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ e ∈ extra, CellHitsPos a.toNat e) ∨
      CellHitsPos a.toNat (freeGap s) ∨
      CellHitsPos a.toNat (heapFree s) ∨
      (∃ m ∈ Nd, a.toNat = m + 24) := by
    intro a hne
    have hdom := heff.out_dom a hne
    have ha8 : a.toNat % 8 = 0 := by
      rw [hAs.1.memaddrs, ordinaryDomain_iff] at hdom; exact hdom.1
    rcases heff.cell_frame a hne with ⟨iv, hiv, hpos, hc1, hc2⟩ | hfg | hhf
    · rcases List.mem_append.1 hiv with hm24 | hex
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
        have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
        dsimp only at hc1 hc2
        exact Or.inr (Or.inr (Or.inr ⟨m, hm, by omega⟩))
      · exact Or.inl ⟨iv, hex, hpos, hc1, hc2⟩
    · exact Or.inr (Or.inl hfg)
    · exact Or.inr (Or.inr (Or.inl hhf))
  have hw012 : ∀ n ∈ Nd, memW post n = memW s n ∧ memW post (n + 8) = memW s (n + 8) ∧
      memW post (n + 16) = memW s (n + 16) := by
    intro n hn
    have hsz := nodeSize_ge32 (memW s n)
    refine ⟨?_, ?_, ?_⟩
    · simpa using node_memW_eq_of_hashOnly_cell_frame hAs hN hextra_disj hcf hn
        (off := 0) (by decide) (by omega) (by decide)
    · exact node_memW_eq_of_hashOnly_cell_frame hAs hN hextra_disj hcf hn
        (off := 8) (by decide) (by omega) (by decide)
    · exact node_memW_eq_of_hashOnly_cell_frame hAs hN hextra_disj hcf hn
        (off := 16) (by decide) (by omega) (by decide)
  have hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40 := by
    intro n hn
    rw [(hw012 n hn).2.2]
    exact (hN.1 n hn).2.2.2.2.2.2.2.1
  have hextra_disj_all : ∀ e ∈ extra, ∀ o ∈ nodeExtents s Nd, Disj e o := by
    intro e he o ho
    by_cases he0 : e.2 = 0
    · exact Or.inl he0
    · exact hextra_disj e he (by omega) o ho
  obtain ⟨hN_post, hext⟩ := nodeHeap_of_heapByteEff_cache hAs hN heff_cache hextra_disj_all hrlp_len
  exact ⟨hN_post, hext, hw012⟩

private theorem eval_node_hash_cached_heapByteEff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (node0 : BitVec 64)
    (gw : List String) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hN : NodeHeap s Nd)
    (hnode_in : node0.toNat ∈ Nd)
    (hloc : s.locals.lookup (ofString "node") = some (.val (.word node0)))
    (hgw : "heap_ptr" ∈ gw)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_hash_cached)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_hash_cached)).2
    ∃ hw : BitVec 64,
      v = .val (.word hw) ∧
      HeapByteEff s post (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s) gw ∧
      HeapByteEff s post (nodeCacheIvls Nd ++ keccakBufIvls s) gw := by
  intro post; dsimp only [post]
  have hhe264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hhl_he : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
  have hb : sourceFnBody Guest.Software.guestFn_node_hash_cached =
      .dec (ofString "cached") .one (.load .one (.op .add [.var .local (ofString "node"), .const 24]))
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "cached")) (.const 0))
            (.return (.var .local (ofString "cached"))) .skip)
          (.seq
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "node"), .const 8])) (.const 0))
              (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip)
            (.decCall (ofString "h") .one (ofString "alloc") [.const 32]
              (.seq
                (.call (some (none, none)) (ofString "keccak256")
                  [.load .one (.op .add [.var .local (ofString "node"), .const 8]),
                   .load .one (.op .add [.var .local (ofString "node"), .const 16]),
                   .var .local (ofString "h")])
                (.seq
                  (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h")))
                  (.return (.var .local (ofString "h")))))))) := rfl
  obtain ⟨_, _, hin_n, hw_n, _⟩ := hN.1 node0.toNat hnode_in
  have hsz_n := nodeSize_ge32 (memW s node0.toNat)
  have hhi_n_he : node0.toNat + nodeSize (memW s node0.toNat) ≤ heapEnd := by
    have := hin_n.2; dsimp [nodeIvl] at this; omega
  have hhi_n : node0.toNat + nodeSize (memW s node0.toNat) ≤ 2 ^ 64 := by omega
  obtain ⟨cw, hld24, _⟩ := eval_load_memW_of_wordsOK (base := node0) (off := 24)
    hw_n (by decide) (by omega) hhi_n
    (e := .op .add [.var .local (ofString "node"), .const 24])
    (by simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord])
  have hsh_cw : shapeEqHOL .one (shapeOfHOLExact (.val (.word cw) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  let R24 := Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s
  have hmono_cache : ∀ p : PanSemStateFiniteExact 64 F,
      HeapByteEff s p R24 gw → HeapByteEff s p (nodeCacheIvls Nd ++ keccakBufIvls s) gw := by
    intro p hp
    exact hp.mono
      (fun i hi _ => by
        rcases List.mem_append.1 hi with hm24 | hex
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
          exact Or.inl ⟨(m + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩),
            by dsimp; omega, by dsimp; omega⟩
        · exact Or.inl ⟨i, List.mem_append_right _ hex, le_rfl, le_rfl⟩)
      (fun _ hg => hg)
  rw [hb, evaluateHOLFiniteState_dec_total] at hret ⊢
  dsimp only at hret ⊢
  rw [hld24] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_cw] at hret ⊢
  set s1 := setVarHOLFinite (ofString "cached") (.val (.word cw)) s
  have hAR_s1 : ArenaReady s1 := ⟨guestInv_setVar _ _ _ hAR.1, hAR.2⟩
  have hs1_cw : s1.locals.lookup (ofString "cached") = some (.val (.word cw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_node : s1.locals.lookup (ofString "node") = some (.val (.word node0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hloc,
      show ofString "cached" ≠ ofString "node" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  have hcmp_cw : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .notEqual (.var .local (ofString "cached")) (.const 0)) =
      some (.val (.word (if cw ≠ 0 then 1 else 0))) := by
    simp [evalHOLExact, hs1_cw, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hcw_nz : cw ≠ 0
  · have hret_s1 : evaluateHOLFiniteState s1
        (.ite (.cmp .notEqual (.var .local (ofString "cached")) (.const 0))
          (.return (.var .local (ofString "cached"))) .skip) =
        (some (.returned (.val (.word cw))), s1.emptyLocalsHOLFinite) := by
      rw [evaluateHOLFiniteState_ite, hcmp_cw, if_pos hcw_nz]
      dsimp only
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_neg h10, evaluateHOLFiniteState_return]
      simp [evalHOLExact, hs1_cw, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret_s1] at hret ⊢
    dsimp only at hret ⊢
    have hcw_v : v = .val (.word cw) := by
      injection hret with hret'
      injection hret' with hv
      exact hv.symm
    subst hcw_v
    have heff24 : HeapByteEff s
        { s1.emptyLocalsHOLFinite with
          locals := HolFiniteMapExact.resVarEq s1.emptyLocalsHOLFinite.locals
            (ofString "cached", s.locals.lookup (ofString "cached")) } R24 gw :=
      (HeapByteEff.refl hAR R24 gw).locals_clock _ _
    exact ⟨cw, rfl, heff24, hmono_cache _ heff24⟩
  · have hcw_eq0 : cw = 0 := Classical.not_not.mp hcw_nz
    have hite1 : evaluateHOLFiniteState s1
        (.ite (.cmp .notEqual (.var .local (ofString "cached")) (.const 0))
          (.return (.var .local (ofString "cached"))) .skip) = (none, s1) := by
      rw [evaluateHOLFiniteState_ite, hcmp_cw]
      simp [hcw_eq0, evaluateHOLFiniteState_skip]
    rw [hite1] at hret ⊢; dsimp only at hret ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
    have h2 : evaluateHOLFiniteState s1
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "node"), .const 8])) (.const 0))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) = (none, s1) := by
      have hmf := eval_call_mpt_fail_no_none_no_ret s1 13 hc
      rcases hite2 : evaluateHOLFiniteState s1
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "node"), .const 8])) (.const 0))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨r2, s2⟩
      cases r2 with
      | some r2' =>
        exfalso
        have hr2_ret : r2' = .returned v := by
          rw [hite2] at hret; dsimp only at hret; injection hret
        subst hr2_ret
        rw [evaluateHOLFiniteState_ite] at hite2
        split at hite2
        · split at hite2
          · rw [evaluateHOLFiniteState_skip] at hite2; cases hite2
          · exact hmf.2 v (congrArg Prod.fst hite2)
        · injection hite2 with hr _; cases hr
      | none =>
        rw [evaluateHOLFiniteState_ite] at hite2
        split at hite2
        · split at hite2
          · rw [evaluateHOLFiniteState_skip] at hite2; exact hite2.symm
          · exact False.elim (hmf.1 (congrArg Prod.fst hite2))
        · cases hite2
    rw [h2] at hret ⊢
    dsimp only at hret ⊢
    let kcStmt : ProgHOL 64 :=
      .call (some (none, none)) (ofString "keccak256")
        [.load .one (.op .add [.var .local (ofString "node"), .const 8]),
         .load .one (.op .add [.var .local (ofString "node"), .const 16]),
         .var .local (ofString "h")]
    let tailStmt : ProgHOL 64 :=
      .seq
        (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h")))
        (.return (.var .local (ofString "h")))
    let contK : ProgHOL 64 := .seq kcStmt tailStmt
    change (evaluateHOLFiniteState s1
        (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).1 =
      some (.returned v) at hret
    have hnt_dc : (evaluateHOLFiniteState s1
        (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).1 ≠ some .timeOut := by
      rw [hret]; simp
    have hres_dc : Resumes (evaluateHOLFiniteState s1
        (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).1 :=
      Or.inl ⟨v, hret⟩
    obtain ⟨hp, n32, q, m1, hn32_ev, hhp_nat, _, _, hhp_q, hq_lim, _, hm1_hp, hm1_g, hm1_m, hm1_loc,
        heff_m1, hnt_m1, _, hdc_eq⟩ :=
      eval_decCall_alloc_resumes s1 "h" (.const 32) contK R24 gw hc hAR_s1 hgw hnt_dc hres_dc
    have hn32 : n32 = 32 := by
      simp [evalHOLExact] at hn32_ev; exact hn32_ev.symm
    subst hn32
    have h32_nat : (32 : BitVec 64).toNat = 32 := rfl
    change ∃ hw, v = .val (.word hw) ∧
      HeapByteEff s
        { (evaluateHOLFiniteState s1
            (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState s1
              (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).2.locals
            (ofString "cached", s.locals.lookup (ofString "cached")) } R24 gw ∧
      HeapByteEff s
        { (evaluateHOLFiniteState s1
            (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState s1
              (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).2.locals
            (ofString "cached", s.locals.lookup (ofString "cached")) }
        (nodeCacheIvls Nd ++ keccakBufIvls s) gw
    rw [hdc_eq] at hret ⊢
    dsimp only at hret ⊢
    have hm1_h : m1.locals.lookup (ofString "h") = some (.val (.word hp)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm1_node : m1.locals.lookup (ofString "node") = some (.val (.word node0)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_node,
        show ofString "h" ≠ ofString "node" by decide]
    have hw_n_m1' : WordsOK m1 (node0.toNat, nodeSize (memW s node0.toNat)) :=
      P3MptSet.wordsOK_transfer hAR.1 heff_m1.arena.1 hw_n
    obtain ⟨rpw, hld8_m1, _⟩ := eval_load_memW_of_wordsOK (s := m1) (base := node0) (off := 8)
      hw_n_m1' (by decide) (by omega) hhi_n
      (e := .op .add [.var .local (ofString "node"), .const 8])
      (by simp [evalHOLExact, evalListHOLExact, hm1_node, wordOpHOL, wordOp, valueIsWord, valueWord])
    obtain ⟨rlw, hld16_m1, _⟩ := eval_load_memW_of_wordsOK (s := m1) (base := node0) (off := 16)
      hw_n_m1' (by decide) (by omega) hhi_n
      (e := .op .add [.var .local (ofString "node"), .const 16])
      (by simp [evalHOLExact, evalListHOLExact, hm1_node, wordOpHOL, wordOp, valueIsWord, valueWord])
    have hkpad_m1 : globN m1 "keccak_pad" = globN s "keccak_pad" := by
      unfold globN; rw [hm1_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "keccak_pad" by decide]; rfl
    have hkst_m1 : globN m1 "keccak_st" = globN s "keccak_st" := by
      unfold globN; rw [hm1_g]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "keccak_st" by decide]; rfl
    have hcontK_eq := evaluateHOLFiniteState_seq_line780 m1 kcStmt tailStmt
    change evaluateHOLFiniteState m1 contK = _ at hcontK_eq
    rw [hcontK_eq] at hret hnt_m1 ⊢
    have hkc_none : (evaluateHOLFiniteState m1 kcStmt).1 = none := by
      rcases hkc0 : evaluateHOLFiniteState m1 kcStmt with ⟨rkc, m2'⟩
      cases rkc with
      | none => rfl
      | some r_kc =>
        exfalso
        have hrkc_ret : r_kc = .returned v := by
          rw [hkc0] at hret; dsimp only at hret; injection hret
        subst hrkc_ret
        have hkc_fst : (evaluateHOLFiniteState m1 kcStmt).1 = some (.returned v) :=
          congrArg Prod.fst hkc0
        dsimp only [kcStmt] at hkc_fst
        rw [evaluateHOLFiniteState_call] at hkc_fst
        revert hkc_fst; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite m1 _) _ with ⟨rc, _⟩
        rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
    let m2 := (evaluateHOLFiniteState m1 kcStmt).2
    have hkc : evaluateHOLFiniteState m1 kcStmt = (none, m2) := Prod.ext hkc_none rfl
    rw [hkc] at hret ⊢
    dsimp only [tailStmt] at hret ⊢
    let Rkc : List Ivl := (hp.toNat, 32) :: R24
    have hkc_eff := eval_call_keccak256_heap m1
      (.load .one (.op .add [.var .local (ofString "node"), .const 8]))
      (.load .one (.op .add [.var .local (ofString "node"), .const 16]))
      (.var .local (ofString "h"))
      rpw rlw hp Rkc gw heff_m1.arena.1.code heff_m1.arena
      hld8_m1 hld16_m1 (by simp [evalHOLExact, hm1_h])
      ⟨(hp.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩
      (fun hnz => by
        rw [hkpad_m1] at hnz ⊢
        exact ⟨bufferRegion s ("keccak_pad", 136),
          List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self)),
          le_rfl, by simp [bufferRegion, hnz]⟩)
      (fun hnz => by
        rw [hkst_m1] at hnz ⊢
        exact ⟨bufferRegion s ("keccak_st", 200),
          List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          le_rfl, by simp [bufferRegion, hnz]⟩)
      (by dsimp only [kcStmt] at hkc; rw [hkc]; simp)
      (by dsimp only [kcStmt] at hkc; rw [hkc]; exact Or.inl rfl)
    dsimp only [kcStmt] at hkc; rw [hkc] at hkc_eff
    obtain ⟨heff_m2_raw, hm2_lg⟩ := hkc_eff
    obtain ⟨hm2_loc, _⟩ := hm2_lg rfl
    have hm2_h : m2.locals.lookup (ofString "h") = some (.val (.word hp)) := by
      rw [hm2_loc]; exact hm1_h
    have hm2_node : m2.locals.lookup (ofString "node") = some (.val (.word node0)) := by
      rw [hm2_loc]; exact hm1_node
    have hw_n_m2 : WordsOK m2 (node0.toNat, nodeSize (memW s node0.toNat)) :=
      P3MptSet.wordsOK_transfer hAR.1 heff_m2_raw.arena.1 hw_n
    have hst24 := eval_store_memW_at (s := m2) (base := node0) (w := hp) (off := 24)
      (len := nodeSize (memW s node0.toNat)) (Rl := R24) (gw := gw)
      heff_m2_raw.arena hw_n_m2 (by decide) (by omega) hhi_n_he
      ⟨(node0.toNat + 24, 8),
        List.mem_append_left _ (List.mem_map.2 ⟨node0.toNat, hnode_in, rfl⟩),
        le_rfl, le_rfl⟩
      (dstExp := .op .add [.var .local (ofString "node"), .const 24])
      (valExp := .var .local (ofString "h"))
      (by simp [evalHOLExact, evalListHOLExact, hm2_node, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [evalHOLExact, hm2_h])
    dsimp only at hst24
    obtain ⟨hst_n, hm3_loc, _, _, _, heff_st⟩ := hst24
    let m3 := (evaluateHOLFiniteState m2
      (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h")))).2
    rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
    have hst_pair : evaluateHOLFiniteState m2
        (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h"))) =
        (none, m3) := Prod.ext hst_n rfl
    rw [hst_pair] at hret ⊢; dsimp only at hret ⊢
    have hm3_h : m3.locals.lookup (ofString "h") = some (.val (.word hp)) := by
      rw [hm3_loc]; exact hm2_h
    have hret_m3 : evaluateHOLFiniteState m3 (.return (.var .local (ofString "h"))) =
        (some (.returned (.val (.word hp))), m3.emptyLocalsHOLFinite) := by
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLExact, hm3_h, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret_m3] at hret ⊢
    dsimp only at hret ⊢
    have hhp_v : v = .val (.word hp) := by
      injection hret with hret'
      injection hret' with hv
      exact hv.symm
    subst hhp_v
    have heff_s_m1 : HeapByteEff s m1 R24 gw :=
      ((HeapByteEff.refl hAR R24 gw).locals_clock s1.locals s1.clock).trans heff_m1
    have heff_s_m2_rkc : HeapByteEff s m2 Rkc gw :=
      (heff_s_m1.mono
        (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩)
        (fun _ hg => hg)).trans heff_m2_raw
    have heff_s_m2 : HeapByteEff s m2 R24 gw :=
      heff_s_m2_rkc.mono
        (fun i hi _ => by
          simp only [Rkc, List.mem_cons] at hi
          rcases hi with rfl | hi24
          · exact Or.inr (Or.inr ⟨by
              have hhp_s : globN s1 "heap_ptr" = globN s "heap_ptr" := rfl
              dsimp; omega,
              by dsimp; omega⟩)
          · exact Or.inl ⟨i, hi24, le_rfl, le_rfl⟩)
        (fun _ hg => hg)
    have heff_s_m3 : HeapByteEff s m3 R24 gw := heff_s_m2.trans heff_st
    have heff_final : HeapByteEff s
        { m3.emptyLocalsHOLFinite with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq m3.emptyLocalsHOLFinite.locals
              (ofString "h", s1.locals.lookup (ofString "h")))
            (ofString "cached", s.locals.lookup (ofString "cached")) } R24 gw :=
      heff_s_m3.locals_clock _ m3.emptyLocalsHOLFinite.clock
    exact ⟨hp, rfl, heff_final, hmono_cache _ heff_final⟩

private theorem eval_node_hash_cached_nodeHeap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (node0 : BitVec 64)
    (gw : List String) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hN : NodeHeap s Nd)
    (hnode_in : node0.toNat ∈ Nd)
    (hloc : s.locals.lookup (ofString "node") = some (.val (.word node0)))
    (hgw : "heap_ptr" ∈ gw)
    (hdisj_kc : ∀ o ∈ nodeExtents s Nd,
      Disj (bufferRegion s ("keccak_pad", 136)) o ∧
      Disj (bufferRegion s ("keccak_st", 200)) o)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_hash_cached)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_hash_cached)).2
    ∃ hw : BitVec 64,
      v = .val (.word hw) ∧
      HeapByteEff s post (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s) gw ∧
      HeapByteEff s post (nodeCacheIvls Nd ++ keccakBufIvls s) gw ∧
      NodeHeap post Nd ∧
      nodeExtents post Nd = nodeExtents s Nd ∧
      (∀ n ∈ Nd, memW post n = memW s n ∧ memW post (n + 8) = memW s (n + 8) ∧
        memW post (n + 16) = memW s (n + 16)) ∧
      (∀ m, RootIn Nd m → nodeRefBytes post m = nodeRefBytes s m) := by
  intro post; dsimp only [post]
  obtain ⟨hw, hv, heff24, heff_cache⟩ :=
    eval_node_hash_cached_heapByteEff s Nd node0 gw v hc hAR hN hnode_in hloc hgw hret
  have hkc_disj := keccakBufIvls_disj_of_buffers hdisj_kc
  obtain ⟨hN_post, hext_post, hw012⟩ :=
    nodeHeap_of_hashOnly_heapByteEff hAR hN heff24 (fun e he _ o ho => hkc_disj e he o ho)
  refine ⟨hw, hv, heff24, heff_cache, hN_post, hext_post, hw012, ?_⟩
  intro m hm
  exact nodeRefBytes_congr (fun n hn => (hw012 n hn).1) (fun n hn => (hw012 n hn).2.2) hm

private theorem eval_decCall_node_hash_cached {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (lname : String)
    (nodeExp : ExpHOL 64) (node0 : BitVec 64) (cont : ProgHOL 64) (gw : List String)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hN : NodeHeap s Nd)
    (hnode_in : node0.toNat ∈ Nd)
    (hnode_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
      some (.val (.word node0)))
    (hgw : "heap_ptr" ∈ gw)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "node_hash_cached") [nodeExp] cont)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "node_hash_cached") [nodeExp] cont)
    (∃ (hw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      mid.locals = s.locals.update (ofString lname, .val (.word hw)) ∧
      HeapByteEff s mid (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s) gw ∧
      HeapByteEff s mid (nodeCacheIvls Nd ++ keccakBufIvls s) gw ∧
      ((∀ o ∈ nodeExtents s Nd,
          Disj (bufferRegion s ("keccak_pad", 136)) o ∧
          Disj (bufferRegion s ("keccak_st", 200)) o) →
        NodeHeap mid Nd ∧
        nodeExtents mid Nd = nodeExtents s Nd ∧
        (∀ n ∈ Nd, memW mid n = memW s n ∧ memW mid (n + 8) = memW s (n + 8) ∧
          memW mid (n + 16) = memW s (n + 16)) ∧
        (∀ m, RootIn Nd m → nodeRefBytes mid m = nodeRefBytes s m)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      out = ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) })) ∨
    (out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) ∧
      out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧
      (Resumes out.1 →
        HeapByteEff s out.2 (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s) gw ∧
        HeapByteEff s out.2 (nodeCacheIvls Nd ++ keccakBufIvls s) gw)) := by
  intro out; dsimp only [out]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [nodeExp] = some [.val (.word node0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hnode_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "node_hash_cached")
    (ofString "node") (sourceFnBody Guest.Software.guestFn_node_hash_cached) node0
    (by rw [hc]; exact lookup_node_hash_cached)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "node", ValueHOL.val (.word node0))
    set ent := callEntryStateHOLFinite s cmap
    have hAR_ent : ArenaReady ent := ⟨guestInv_callEntry s cmap hAR.1, hAR.2⟩
    have hent_loc : ent.locals.lookup (ofString "node") = some (.val (.word node0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hN_ent : NodeHeap ent Nd := hN
    have hkc_ent : keccakBufIvls ent = keccakBufIvls s := rfl
    rcases hbody : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_node_hash_cached) with ⟨rb, sb⟩
    have hnt_ent : rb ≠ some .timeOut := by
      rintro rfl; rw [hbody] at hnt; exact hnt rfl
    simp only [hbody] at hnt ⊢
    cases rb with
    | none =>
      right
      exact ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => False.elim (not_resumes_error hres)⟩
    | some r0 =>
      cases r0 with
      | timeOut => exact absurd rfl hnt_ent
      | returned rv =>
        obtain ⟨hw, rfl, heff24_ent, heff_cache_ent⟩ :=
          eval_node_hash_cached_heapByteEff ent Nd node0 gw rv hc hAR_ent hN_ent hnode_in hent_loc hgw
            (by rw [hbody])
        rw [hbody, hkc_ent] at heff24_ent heff_cache_ent
        dsimp only at heff24_ent heff_cache_ent
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word hw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnt ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word hw)) { sb with locals := s.locals }
        have heff_s_ent24 : HeapByteEff s ent (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s) gw :=
          (HeapByteEff.refl hAR _ gw).locals_clock ent.locals ent.clock
        have heff_s_ent_cache : HeapByteEff s ent (nodeCacheIvls Nd ++ keccakBufIvls s) gw :=
          (HeapByteEff.refl hAR _ gw).locals_clock ent.locals ent.clock
        have heff24_mid : HeapByteEff s mid (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s) gw :=
          (heff_s_ent24.trans heff24_ent).locals_clock mid.locals mid.clock
        have heff_cache_mid : HeapByteEff s mid (nodeCacheIvls Nd ++ keccakBufIvls s) gw :=
          (heff_s_ent_cache.trans heff_cache_ent).locals_clock mid.locals mid.clock
        left
        refine ⟨hw, mid, rfl, heff24_mid, heff_cache_mid, ?_, hnt, rfl⟩
        intro hdisj_kc
        have hkc_disj := keccakBufIvls_disj_of_buffers hdisj_kc
        obtain ⟨hN_mid, hext_mid, hw012_mid⟩ :=
          nodeHeap_of_hashOnly_heapByteEff hAR hN heff24_mid (fun e he _ o ho => hkc_disj e he o ho)
        refine ⟨hN_mid, hext_mid, hw012_mid, fun m hm => ?_⟩
        exact nodeRefBytes_congr (fun n hn => (hw012_mid n hn).1) (fun n hn => (hw012_mid n hn).2.2) hm
      | «break» =>
        right
        exact ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => False.elim (not_resumes_error hres)⟩
      | «continue» =>
        right
        exact ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => False.elim (not_resumes_error hres)⟩
      | error =>
        right
        exact ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => False.elim (not_resumes_error hres)⟩
      | finalFfi f =>
        right
        refine ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => ?_⟩
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception eid ev =>
        right
        refine ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => ?_⟩
        rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
        · simp at h
        · injection h with h'; injection h' with he1 he2; subst he1 he2
          have hex_eff : HeapByteEff ent sb (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s) gw := by
            have hhe264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
            have hhl_he : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
            have hb : sourceFnBody Guest.Software.guestFn_node_hash_cached =
                .dec (ofString "cached") .one (.load .one (.op .add [.var .local (ofString "node"), .const 24]))
                  (.seq
                    (.ite (.cmp .notEqual (.var .local (ofString "cached")) (.const 0))
                      (.return (.var .local (ofString "cached"))) .skip)
                    (.seq
                      (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "node"), .const 8])) (.const 0))
                        (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip)
                      (.decCall (ofString "h") .one (ofString "alloc") [.const 32]
                        (.seq
                          (.call (some (none, none)) (ofString "keccak256")
                            [.load .one (.op .add [.var .local (ofString "node"), .const 8]),
                             .load .one (.op .add [.var .local (ofString "node"), .const 16]),
                             .var .local (ofString "h")])
                          (.seq
                            (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h")))
                            (.return (.var .local (ofString "h")))))))) := rfl
            obtain ⟨_, _, hin_n, hw_n, _⟩ := hN_ent.1 node0.toNat hnode_in
            have hsz_n := nodeSize_ge32 (memW ent node0.toNat)
            have hhi_n : node0.toNat + nodeSize (memW ent node0.toNat) ≤ 2 ^ 64 := by
              have := hin_n.2; dsimp [nodeIvl] at this; omega
            obtain ⟨cw, hld24, _⟩ := eval_load_memW_of_wordsOK (base := node0) (off := 24)
              hw_n (by decide) (by omega) hhi_n
              (e := .op .add [.var .local (ofString "node"), .const 24])
              (by simp [evalHOLExact, evalListHOLExact, hent_loc, wordOpHOL, wordOp, valueIsWord, valueWord])
            have hsh_cw : shapeEqHOL .one (shapeOfHOLExact (.val (.word cw) : ValueHOL 64)) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            let R24 := Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s
            rw [hb, evaluateHOLFiniteState_dec_total] at hbody
            dsimp only at hbody
            rw [hld24] at hbody; dsimp only at hbody; rw [if_pos hsh_cw] at hbody
            set s1 := setVarHOLFinite (ofString "cached") (.val (.word cw)) ent
            have hAR_s1 : ArenaReady s1 := ⟨guestInv_setVar _ _ _ hAR_ent.1, hAR_ent.2⟩
            have hs1_cw : s1.locals.lookup (ofString "cached") = some (.val (.word cw)) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hs1_node : s1.locals.lookup (ofString "node") = some (.val (.word node0)) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_loc,
                show ofString "cached" ≠ ofString "node" by decide]
            rw [evaluateHOLFiniteState_seq_line780] at hbody
            have hcmp_cw : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                (.cmp .notEqual (.var .local (ofString "cached")) (.const 0)) =
                some (.val (.word (if cw ≠ 0 then 1 else 0))) := by
              simp [evalHOLExact, hs1_cw, Compiler.Encoders.Asm.wordCmpHOL]
            by_cases hcw_nz : cw ≠ 0
            · have hret_s1 : evaluateHOLFiniteState s1
                  (.ite (.cmp .notEqual (.var .local (ofString "cached")) (.const 0))
                    (.return (.var .local (ofString "cached"))) .skip) =
                  (some (.returned (.val (.word cw))), s1.emptyLocalsHOLFinite) := by
                rw [evaluateHOLFiniteState_ite, hcmp_cw, if_pos hcw_nz]
                dsimp only
                have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
                rw [if_neg h10, evaluateHOLFiniteState_return]
                simp [evalHOLExact, hs1_cw, shapeOfHOLExact, sizeOfShapeWithContextHOL]
              rw [hret_s1] at hbody; simp at hbody
            · have hcw_eq0 : cw = 0 := Classical.not_not.mp hcw_nz
              have hite1 : evaluateHOLFiniteState s1
                  (.ite (.cmp .notEqual (.var .local (ofString "cached")) (.const 0))
                    (.return (.var .local (ofString "cached"))) .skip) = (none, s1) := by
                rw [evaluateHOLFiniteState_ite, hcmp_cw]
                simp [hcw_eq0, evaluateHOLFiniteState_skip]
              rw [hite1] at hbody; dsimp only at hbody
              rw [evaluateHOLFiniteState_seq_line780] at hbody
              rcases hite2 : evaluateHOLFiniteState s1
                  (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "node"), .const 8])) (.const 0))
                    (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨r2, s2⟩
              rw [hite2] at hbody
              cases r2 with
              | some r2' =>
                dsimp only at hbody
                have hro_ite2 := evaluate_roEncProg
                  (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "node"), .const 8])) (.const 0))
                    (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) rfl s1 hc
                rw [hite2] at hro_ite2; dsimp only at hro_ite2
                injection hbody with _ hsb_eq
                rw [← hsb_eq]
                have hs2_eff : HeapByteEff ent s2 R24 gw := by
                  rw [hro_ite2]
                  exact ((HeapByteEff.refl hAR_ent R24 gw).locals_clock s1.locals s1.clock).locals_clock s2.locals s2.clock
                exact hs2_eff.locals_clock _ s2.clock
              | none =>
                have hs2_eq : s2 = s1 := by
                  have hmf := eval_call_mpt_fail_no_none_no_ret s1 13 hc
                  rw [evaluateHOLFiniteState_ite] at hite2
                  split at hite2
                  · split at hite2
                    · rw [evaluateHOLFiniteState_skip] at hite2; exact (Prod.mk.inj hite2).2.symm
                    · exact False.elim (hmf.1 (congrArg Prod.fst hite2))
                  · cases hite2
                subst hs2_eq
                dsimp only at hbody
                let kcStmt : ProgHOL 64 :=
                  .call (some (none, none)) (ofString "keccak256")
                    [.load .one (.op .add [.var .local (ofString "node"), .const 8]),
                     .load .one (.op .add [.var .local (ofString "node"), .const 16]),
                     .var .local (ofString "h")]
                let tailStmt : ProgHOL 64 :=
                  .seq
                    (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h")))
                    (.return (.var .local (ofString "h")))
                let contK : ProgHOL 64 := .seq kcStmt tailStmt
                have hbody_fst : (evaluateHOLFiniteState s1
                    (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).1 =
                    some (.exception eid ev) := congrArg Prod.fst hbody
                have hbody_snd : { (evaluateHOLFiniteState s1
                    (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).2 with
                    locals := HolFiniteMapExact.resVarEq
                      (evaluateHOLFiniteState s1
                        (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).2.locals
                      (ofString "cached", ent.locals.lookup (ofString "cached")) } = sb :=
                  congrArg Prod.snd hbody
                have hnt_dc : (evaluateHOLFiniteState s1
                    (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).1 ≠ some .timeOut := by
                  rw [hbody_fst]; simp
                have hres_dc : Resumes (evaluateHOLFiniteState s1
                    (.decCall (ofString "h") .one (ofString "alloc") [.const 32] contK)).1 :=
                  Or.inr ⟨eid, ev, hbody_fst, hne⟩
                obtain ⟨hp, n32, q, m1, hn32_ev, hhp_nat, _, _, hhp_q, hq_lim, _, _, hm1_g, hm1_m, hm1_loc,
                    heff_m1, hnt_m1, hres_m1, hdc_eq⟩ :=
                  eval_decCall_alloc_resumes s1 "h" (.const 32) contK R24 gw hc hAR_s1 hgw hnt_dc hres_dc
                have hn32 : n32 = 32 := by simp [evalHOLExact] at hn32_ev; exact hn32_ev.symm
                subst hn32
                have h32_nat : (32 : BitVec 64).toNat = 32 := rfl
                have hm1_h : m1.locals.lookup (ofString "h") = some (.val (.word hp)) := by
                  rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                have hm1_node : m1.locals.lookup (ofString "node") = some (.val (.word node0)) := by
                  rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_node,
                    show ofString "h" ≠ ofString "node" by decide]
                have hw_n_m1 : WordsOK m1 (node0.toNat, nodeSize (memW ent node0.toNat)) :=
                  P3MptSet.wordsOK_transfer hAR_ent.1 heff_m1.arena.1 hw_n
                obtain ⟨rpw, hld8_m1, _⟩ := eval_load_memW_of_wordsOK (base := node0) (off := 8)
                  hw_n_m1 (by decide) (by omega) hhi_n
                  (e := .op .add [.var .local (ofString "node"), .const 8])
                  (by simp [evalHOLExact, evalListHOLExact, hm1_node, wordOpHOL, wordOp, valueIsWord, valueWord])
                obtain ⟨rlw, hld16_m1, _⟩ := eval_load_memW_of_wordsOK (base := node0) (off := 16)
                  hw_n_m1 (by decide) (by omega) hhi_n
                  (e := .op .add [.var .local (ofString "node"), .const 16])
                  (by simp [evalHOLExact, evalListHOLExact, hm1_node, wordOpHOL, wordOp, valueIsWord, valueWord])
                have hkpad_m1 : globN m1 "keccak_pad" = globN s "keccak_pad" := by
                  change globN m1 "keccak_pad" = globN s1 "keccak_pad"
                  unfold globN; rw [hm1_g]
                  simp [HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "heap_ptr" ≠ ofString "keccak_pad" by decide]
                have hkst_m1 : globN m1 "keccak_st" = globN s "keccak_st" := by
                  change globN m1 "keccak_st" = globN s1 "keccak_st"
                  unfold globN; rw [hm1_g]
                  simp [HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "heap_ptr" ≠ ofString "keccak_st" by decide]
                have hcontK_eq := evaluateHOLFiniteState_seq_line780 m1 kcStmt tailStmt
                change evaluateHOLFiniteState m1 contK = _ at hcontK_eq
                rcases hkc : evaluateHOLFiniteState m1 kcStmt with ⟨rkc, m2⟩
                have hnt_kc : rkc ≠ some .timeOut := by
                  rintro rfl; rw [hcontK_eq, hkc] at hnt_m1; exact hnt_m1 rfl
                have hor_kc : rkc = none ∨ Resumes rkc := by
                  cases rkc with
                  | none => exact Or.inl rfl
                  | some _ => right; rw [hcontK_eq, hkc] at hres_m1; exact hres_m1
                let Rkc : List Ivl := (hp.toNat, 32) :: R24
                have heff_m2_pair := eval_call_keccak256_heap m1
                  (.load .one (.op .add [.var .local (ofString "node"), .const 8]))
                  (.load .one (.op .add [.var .local (ofString "node"), .const 16]))
                  (.var .local (ofString "h"))
                  rpw rlw hp Rkc gw heff_m1.arena.1.code heff_m1.arena
                  hld8_m1 hld16_m1 (by simp [evalHOLExact, hm1_h])
                  ⟨(hp.toNat, 32), List.mem_cons_self, le_rfl, le_rfl⟩
                  (fun hnz => by
                    rw [hkpad_m1] at hnz ⊢
                    exact ⟨bufferRegion s ("keccak_pad", 136),
                      List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [keccakBufIvls])),
                      by simp [bufferRegion, hnz], by simp [bufferRegion, hnz]⟩)
                  (fun hnz => by
                    rw [hkst_m1] at hnz ⊢
                    exact ⟨bufferRegion s ("keccak_st", 200),
                      List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [keccakBufIvls])),
                      by simp [bufferRegion, hnz], by simp [bufferRegion, hnz]⟩)
                  (by rw [hkc]; exact hnt_kc) (by rw [hkc]; exact hor_kc)
                dsimp only [kcStmt] at hkc
                rw [hkc] at heff_m2_pair
                have heff_ent_m1 : HeapByteEff ent m1 R24 gw :=
                  ((HeapByteEff.refl hAR_ent R24 gw).locals_clock s1.locals s1.clock).trans heff_m1
                have heff_ent_m2 : HeapByteEff ent m2 R24 gw := by
                  have h1 : HeapByteEff ent m2 Rkc gw :=
                    (heff_ent_m1.mono
                      (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩)
                      (fun _ hg => hg)).trans heff_m2_pair.1
                  exact h1.mono
                    (fun i hi _ => by
                      simp only [Rkc, List.mem_cons] at hi
                      rcases hi with rfl | hi24
                      · exact Or.inr (Or.inr ⟨by
                          have hhp_s : globN s1 "heap_ptr" = globN ent "heap_ptr" := rfl
                          dsimp; omega, by dsimp; omega⟩)
                      · exact Or.inl ⟨i, hi24, le_rfl, le_rfl⟩)
                    (fun _ hg => hg)
                cases rkc with
                | some rkc' =>
                  rw [hdc_eq, hcontK_eq] at hbody_snd
                  dsimp only [kcStmt] at hbody_snd
                  rw [hkc] at hbody_snd
                  dsimp only at hbody_snd
                  rw [← hbody_snd]
                  exact (heff_ent_m2.locals_clock _ m2.clock).locals_clock _ m2.clock
                | none =>
                  exfalso
                  rw [hdc_eq, hcontK_eq] at hbody_fst
                  dsimp only [kcStmt] at hbody_fst
                  rw [hkc] at hbody_fst
                  dsimp only at hbody_fst
                  dsimp only [tailStmt] at hbody_fst
                  rw [evaluateHOLFiniteState_seq_line780] at hbody_fst; dsimp only at hbody_fst
                  rcases hst_m2 : evaluateHOLFiniteState m2
                    (.store (.op .add [.var .local (ofString "node"), .const 24]) (.var .local (ofString "h"))) with ⟨rst, m3⟩
                  rw [hst_m2] at hbody_fst
                  cases rst with
                  | none =>
                    dsimp only at hbody_fst
                    rw [evaluateHOLFiniteState_return] at hbody_fst
                    split at hbody_fst
                    · simp at hbody_fst
                    · split at hbody_fst <;> simp at hbody_fst
                  | some rst' =>
                    dsimp only at hbody_fst
                    rw [evaluateHOLFiniteState_store] at hst_m2
                    split at hst_m2
                    · split at hst_m2
                      · split at hst_m2
                        · injection hst_m2 with hr _; cases hr
                        · injection hst_m2 with hr _; injection hr with hr'; subst hr'; simp at hbody_fst
                      · injection hst_m2 with hr _; injection hr with hr'; subst hr'; simp at hbody_fst
                    · injection hst_m2 with hr _; injection hr with hr'; subst hr'; simp at hbody_fst
          have heff_s_sb24 : HeapByteEff s sb.emptyLocalsHOLFinite
              (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s) gw :=
            (((HeapByteEff.refl hAR _ gw).locals_clock ent.locals ent.clock).trans hex_eff).locals_clock _ _
          have heff_s_sb_cache : HeapByteEff s sb.emptyLocalsHOLFinite
              (nodeCacheIvls Nd ++ keccakBufIvls s) gw :=
            heff_s_sb24.mono
              (fun i hi _ => by
                rcases List.mem_append.1 hi with hm24 | hex
                · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
                  exact Or.inl ⟨(m + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩),
                    by dsimp; omega, by dsimp; omega⟩
                · exact Or.inl ⟨i, List.mem_append_right _ hex, le_rfl, le_rfl⟩)
              (fun _ hg => hg)
          exact ⟨heff_s_sb24, heff_s_sb_cache⟩

private theorem storeByte_only_none_or_error_local {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    (evaluateHOLFiniteState t (.storeByte dst val)).1 = none ∨
      (evaluateHOLFiniteState t (.storeByte dst val)).1 = some .error := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

private theorem eval_node_write_ref_heapByteEff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (child0 dst0 : BitVec 64)
    (Rl : List Ivl) (gw : List String) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hN : NodeHeap s Nd)
    (hchild_in : RootIn Nd child0.toNat)
    (hchild_loc : s.locals.lookup (ofString "child") = some (.val (.word child0)))
    (hdst_loc : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hdst_fit : dst0.toNat + nodeRefBytes s child0.toNat ≤ heapEnd)
    (hin_ivl : ∃ iv ∈ Rl, iv.1 ≤ dst0.toNat ∧ dst0.toNat + nodeRefBytes s child0.toNat ≤ iv.1 + iv.2)
    (hgw : "heap_ptr" ∈ gw)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_write_ref)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_write_ref)).2
    ∃ w : BitVec 64,
      v = .val (.word w) ∧
      w.toNat = nodeRefBytes s child0.toNat ∧
      HeapByteEff s post (Rl ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)) gw ∧
      HeapByteEff s post (Rl ++ (nodeCacheIvls Nd ++ keccakBufIvls s)) gw := by
  intro post; dsimp only [post]
  have hhe264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have h264_lim : heapLimit ≤ 2 ^ 64 := by decide
  let R24 : List Ivl := Rl ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)
  let Rc : List Ivl := Rl ++ (nodeCacheIvls Nd ++ keccakBufIvls s)
  have hmono_cache : ∀ t, HeapByteEff s t R24 gw → HeapByteEff s t Rc gw := by
    intro t heff
    refine heff.mono (fun i hi _ => ?_) (fun _ hg => hg)
    rcases List.mem_append.1 hi with hrl | hrest
    · exact Or.inl ⟨i, List.mem_append_left _ hrl, le_rfl, le_rfl⟩
    · rcases List.mem_append.1 hrest with hm24 | hkc
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
        exact Or.inl ⟨(m + 8, 24),
          List.mem_append_right _ (List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩)),
          by dsimp; omega, by dsimp; omega⟩
      · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkc), le_rfl, le_rfl⟩
  have hmono_rl : ∀ (a b : PanSemStateFiniteExact 64 F), HeapByteEff a b Rl gw → HeapByteEff a b R24 gw := by
    intro a b heff
    exact heff.mono (fun i hi _ => Or.inl ⟨i, List.mem_append_left _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg)
  have hb : sourceFnBody Guest.Software.guestFn_node_write_ref =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "dst")) (.const 128)) (.return (.const 1))) .skip)
        (.seq
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
            (.seq
              (.storeByte (.var .local (ofString "dst")) (.const 160))
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .load .one (.op .add [.var .local (ofString "child"), .const 24]),
                   .const 32])
                (.return (.const 33))))
            .skip)
          (.seq
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
              (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip)
            (.dec (ofString "rp") .one (.load .one (.op .add [.var .local (ofString "child"), .const 8]))
              (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                    (.seq
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")])
                      (.return (.var .local (ofString "rl"))))
                    .skip)
                  (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
                    (.seq
                      (.storeByte (.var .local (ofString "dst")) (.const 160))
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.op .add [.var .local (ofString "dst"), .const 1],
                           .var .local (ofString "h"),
                           .const 32])
                        (.return (.const 33)))))))))) := rfl
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  rw [hb, evaluateHOLFiniteState_seq_line780] at hret ⊢
  have hcmp0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "child")) (.const 0)) =
      some (.val (.word (if child0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hchild_loc, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hc0 : child0 = 0
  · subst hc0
    have hnrb : nodeRefBytes s (0 : BitVec 64).toNat = 1 := by simp [nodeRefBytes]
    rw [evaluateHOLFiniteState_ite, hcmp0, if_pos rfl] at hret ⊢
    dsimp only at hret ⊢
    rw [if_neg h10, evaluateHOLFiniteState_seq_line780] at hret ⊢
    rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
    simp only [hsb] at hret ⊢
    rcases storeByte_only_none_or_error_local s (.var .local (ofString "dst")) (.const 128) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hret ⊢
      obtain ⟨hbre1, _⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst_loc, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
        exact ⟨iv, hiv, h1, by omega⟩)
      rw [evaluateHOLFiniteState_return] at hret ⊢
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte] at hret ⊢
      injection hret with hret'; injection hret' with hv_eq
      have heff1 : HeapByteEff s s1.emptyLocalsHOLFinite R24 gw :=
        (hmono_rl s s1 (HeapByteEff.of_m11_bre hAR hbre1)).locals_clock _ _
      exact ⟨1, hv_eq.symm, by rw [hnrb]; rfl, heff1, hmono_cache _ heff1⟩
    · rw [hsb] at hse; dsimp only at hse; subst hse; simp at hret
  · have hc0_nat : child0.toNat ≠ 0 := fun h => hc0 (BitVec.eq_of_toNat_eq h)
    have hchild_nd : child0.toNat ∈ Nd := by
      rcases hchild_in with h0 | hm
      · exact absurd h0 hc0_nat
      · exact hm
    rw [evaluateHOLFiniteState_ite, hcmp0, if_neg hc0] at hret ⊢
    dsimp only at hret ⊢
    rw [if_pos rfl, evaluateHOLFiniteState_skip] at hret ⊢
    dsimp only at hret ⊢
    obtain ⟨_, _, hin_c, hw_c, _⟩ := hN.1 child0.toNat hchild_nd
    have hsz_c := nodeSize_ge32 (memW s child0.toNat)
    have hhi_c : child0.toNat + nodeSize (memW s child0.toNat) ≤ 2 ^ 64 := by
      have := hin_c.2; dsimp [nodeIvl] at this; omega
    obtain ⟨kw, hld0, hkw_nat⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 0)
      hw_c (by decide) (by omega) hhi_c
      (e := .op .add [.var .local (ofString "child"), .const 0])
      (by simp [evalHOLExact, evalListHOLExact, hchild_loc, wordOpHOL, wordOp, valueIsWord, valueWord])
    simp only [Nat.add_zero] at hkw_nat
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret ⊢
    have hcmp_k : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0)) =
        some (.val (.word (if kw = 0 then 1 else 0))) := by
      unfold evalHOLExact; rw [hld0]; simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_k] at hret ⊢; dsimp only at hret ⊢
    by_cases hkw0 : kw = 0
    · have hm0 : memW s child0.toNat = 0 := by rw [← hkw_nat, hkw0]; rfl
      have hnrb : nodeRefBytes s child0.toNat = 33 := by simp [nodeRefBytes, hc0_nat, hm0]
      rw [if_pos hkw0, if_neg h10, evaluateHOLFiniteState_seq_line780] at hret ⊢
      rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 160)) with ⟨rsb, s1⟩
      simp only [hsb] at hret ⊢
      rcases storeByte_only_none_or_error_local s (.var .local (ofString "dst")) (.const 160) with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hret ⊢
        obtain ⟨hbre1, hs1_loc⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hdst_loc, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev
          obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
          exact ⟨iv, hiv, h1, by omega⟩)
        have heff_s1 : HeapByteEff s s1 Rl gw := HeapByteEff.of_m11_bre hAR hbre1
        have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [hs1_loc]; exact hdst_loc
        have hs1_child : s1.locals.lookup (ofString "child") = some (.val (.word child0)) := by
          rw [hs1_loc]; exact hchild_loc
        have hw_c_s1 : WordsOK s1 (child0.toNat, nodeSize (memW s child0.toNat)) :=
          P3MptSet.wordsOK_transfer hAR.1 heff_s1.arena.1 hw_c
        obtain ⟨hw24, hld24_s1, _⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 24)
          hw_c_s1 (by decide) (by omega) hhi_c
          (e := .op .add [.var .local (ofString "child"), .const 24])
          (by simp [evalHOLExact, evalListHOLExact, hs1_child, wordOpHOL, wordOp, valueIsWord, valueWord])
        have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
          rw [BitVec.toNat_add]; change (dst0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
        rcases hmc : evaluateHOLFiniteState s1
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .const 1],
               .load .one (.op .add [.var .local (ofString "child"), .const 24]),
               .const 32]) with ⟨rmc, s2⟩
        have hnt_mc : rmc ≠ some .timeOut := by
          rintro rfl; rw [hmc] at hret; simp at hret
        have hmc_spec := eval_call_memcpy_heap s1
          (.op .add [.var .local (ofString "dst"), .const 1])
          (.load .one (.op .add [.var .local (ofString "child"), .const 24]))
          (.const 32)
          (dst0 + 1) hw24 32 Rl gw heff_s1.arena.1.code heff_s1.arena
          (by simp [evalHOLExact, evalListHOLExact, hs1_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
          hld24_s1 (by simp [evalHOLExact])
          (fun _ => by
            obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
            have h32 : (32 : BitVec 64).toNat = 32 := rfl
            exact ⟨iv, hiv, by rw [hdst1_nat]; omega, by rw [hdst1_nat, h32]; omega⟩)
          (by rw [hmc]; exact hnt_mc)
        dsimp only at hmc_spec; rw [hmc] at hmc_spec; simp only [hmc] at hret ⊢
        cases rmc with
        | some rmc' =>
          dsimp only at hret
          injection hret with hret'; subst hret'
          exact False.elim (hmc_spec.2 (by simp) (Or.inl ⟨v, rfl⟩))
        | none =>
          dsimp only at hret ⊢
          obtain ⟨heff_s2, _, _⟩ := hmc_spec.1 rfl
          rw [evaluateHOLFiniteState_return] at hret ⊢
          simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte] at hret ⊢
          injection hret with hret'; injection hret' with hv_eq
          have heff_tot : HeapByteEff s s2.emptyLocalsHOLFinite R24 gw :=
            (hmono_rl s s2 (heff_s1.trans heff_s2)).locals_clock _ _
          exact ⟨33, hv_eq.symm, by rw [hnrb]; rfl, heff_tot, hmono_cache _ heff_tot⟩
      · rw [hsb] at hse; dsimp only at hse; subst hse; simp at hret
    · have hm_ne0 : memW s child0.toNat ≠ 0 := by
        intro h; apply hkw0; apply BitVec.eq_of_toNat_eq; rw [hkw_nat, h]; rfl
      rw [if_neg hkw0, if_pos rfl, evaluateHOLFiniteState_skip] at hret ⊢
      dsimp only at hret ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
      rcases hite3 : evaluateHOLFiniteState s
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨r3, s3⟩
      simp only [hite3] at hret ⊢
      have hmf := eval_call_mpt_fail_no_none_no_ret s 13 hc
      cases r3 with
      | some r3' =>
        dsimp only at hret
        injection hret with hret'; subst hret'
        rw [evaluateHOLFiniteState_ite] at hite3
        split at hite3
        · split at hite3
          · rw [evaluateHOLFiniteState_skip] at hite3; cases hite3
          · exact False.elim (hmf.2 v (congrArg Prod.fst hite3))
        · injection hite3 with hr _; cases hr
      | none =>
        have hs3 : s3 = s := by
          rw [evaluateHOLFiniteState_ite] at hite3
          split at hite3
          · split at hite3
            · rw [evaluateHOLFiniteState_skip] at hite3; exact (Prod.mk.inj hite3).2.symm
            · exact False.elim (hmf.1 (congrArg Prod.fst hite3))
          · cases hite3
        rw [hs3] at hret ⊢; dsimp only at hret ⊢
        obtain ⟨rpw, hld8, hrpw_nat⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 8)
          hw_c (by decide) (by omega) hhi_c
          (e := .op .add [.var .local (ofString "child"), .const 8])
          (by simp [evalHOLExact, evalListHOLExact, hchild_loc, wordOpHOL, wordOp, valueIsWord, valueWord])
        have hsh_rp : shapeEqHOL .one (shapeOfHOLExact (.val (.word rpw) : ValueHOL 64)) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [evaluateHOLFiniteState_dec_total] at hret ⊢
        dsimp only at hret ⊢
        rw [hld8] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_rp] at hret ⊢
        set srp := setVarHOLFinite (ofString "rp") (.val (.word rpw)) s
        have hAR_srp : ArenaReady srp := ⟨guestInv_setVar _ _ _ hAR.1, hAR.2⟩
        have hsrp_rp : srp.locals.lookup (ofString "rp") = some (.val (.word rpw)) := by
          simp [srp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsrp_child : srp.locals.lookup (ofString "child") = some (.val (.word child0)) := by
          simp [srp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hchild_loc,
            show ofString "rp" ≠ ofString "child" by decide]
        have hsrp_dst : srp.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          simp [srp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst_loc,
            show ofString "rp" ≠ ofString "dst" by decide]
        obtain ⟨rlw, hld16, hrlw_nat⟩ := eval_load_memW_of_wordsOK (s := srp) (base := child0) (off := 16)
          hw_c (by decide) (by omega) hhi_c
          (e := .op .add [.var .local (ofString "child"), .const 16])
          (by simp [evalHOLExact, evalListHOLExact, hsrp_child, wordOpHOL, wordOp, valueIsWord, valueWord])
        have hrlw_eq : rlw.toNat = memW s (child0.toNat + 16) := hrlw_nat
        have hsh_rl : shapeEqHOL .one (shapeOfHOLExact (.val (.word rlw) : ValueHOL 64)) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [evaluateHOLFiniteState_dec_total] at hret ⊢
        dsimp only at hret ⊢
        rw [hld16] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh_rl] at hret ⊢
        set srl := setVarHOLFinite (ofString "rl") (.val (.word rlw)) srp
        have hAR_srl : ArenaReady srl := ⟨guestInv_setVar _ _ _ hAR_srp.1, hAR_srp.2⟩
        have hsrl_rl : srl.locals.lookup (ofString "rl") = some (.val (.word rlw)) := by
          simp [srl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsrl_rp : srl.locals.lookup (ofString "rp") = some (.val (.word rpw)) := by
          simp [srl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrp_rp,
            show ofString "rl" ≠ ofString "rp" by decide]
        have hsrl_child : srl.locals.lookup (ofString "child") = some (.val (.word child0)) := by
          simp [srl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrp_child,
            show ofString "rl" ≠ ofString "child" by decide]
        have hsrl_dst : srl.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          simp [srl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrp_dst,
            show ofString "rl" ≠ ofString "dst" by decide]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret ⊢
        have hcmp_rl : @evalHOLExact 64 F _ srl.toExact (fun a => Classical.propDecidable (srl.memaddrs a))
            (.cmp .lower (.var .local (ofString "rl")) (.const 32)) =
            some (.val (.word (if rlw.toNat < 32 then 1 else 0))) := by
          simp [evalHOLExact, hsrl_rl, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
        rw [hcmp_rl] at hret ⊢; dsimp only at hret ⊢
        by_cases hlt32 : rlw.toNat < 32
        · have hlt32' : memW s (child0.toNat + 16) < 32 := by rw [← hrlw_eq]; exact hlt32
          have hnrb : nodeRefBytes s child0.toNat = rlw.toNat := by
            simp [nodeRefBytes, hc0_nat, hm_ne0, hlt32', hrlw_eq]
          rw [if_pos hlt32, if_neg h10, evaluateHOLFiniteState_seq_line780] at hret ⊢
          rcases hmc : evaluateHOLFiniteState srl
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")]) with ⟨rmc, m2⟩
          have hnt_mc : rmc ≠ some .timeOut := by
            rintro rfl; rw [hmc] at hret; simp at hret
          have hmc_spec := eval_call_memcpy_heap srl
            (.var .local (ofString "dst")) (.var .local (ofString "rp")) (.var .local (ofString "rl"))
            dst0 rpw rlw Rl gw hc hAR_srl
            (by simp [evalHOLExact, hsrl_dst])
            (by simp [evalHOLExact, hsrl_rp])
            (by simp [evalHOLExact, hsrl_rl])
            (fun _ => by
              obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
              exact ⟨iv, hiv, h1, by omega⟩)
            (by rw [hmc]; exact hnt_mc)
          dsimp only at hmc_spec; rw [hmc] at hmc_spec; simp only [hmc] at hret ⊢
          cases rmc with
          | some rmc' =>
            dsimp only at hret
            injection hret with hret'; subst hret'
            exact False.elim (hmc_spec.2 (by simp) (Or.inl ⟨v, rfl⟩))
          | none =>
            dsimp only at hret ⊢
            obtain ⟨heff_m2, hm2_loc, _⟩ := hmc_spec.1 rfl
            have hm2_rl : m2.locals.lookup (ofString "rl") = some (.val (.word rlw)) := by
              rw [hm2_loc]; exact hsrl_rl
            rw [evaluateHOLFiniteState_return] at hret ⊢
            simp only [evalHOLExact, hm2_rl, shapeOfHOLExact, sizeOfShapeWithContextHOL,
              Nat.one_le_ofNat, ↓reduceIte] at hret ⊢
            injection hret with hret'; injection hret' with hv_eq
            have heff_s_srl : HeapByteEff s srl Rl gw :=
              ((HeapByteEff.refl hAR Rl gw).locals_clock srp.locals srp.clock).locals_clock srl.locals srl.clock
            have heff_tot : HeapByteEff s
                { m2.emptyLocalsHOLFinite with
                  locals := HolFiniteMapExact.resVarEq
                    (HolFiniteMapExact.resVarEq m2.emptyLocalsHOLFinite.locals
                      (ofString "rl", srp.locals.lookup (ofString "rl")))
                    (ofString "rp", s.locals.lookup (ofString "rp")) } R24 gw :=
              (hmono_rl s m2 (heff_s_srl.trans heff_m2)).locals_clock _ _
            exact ⟨rlw, hv_eq.symm, hnrb.symm, heff_tot, hmono_cache _ heff_tot⟩
        · have hlt32' : ¬ memW s (child0.toNat + 16) < 32 := by rw [← hrlw_eq]; exact hlt32
          have hnrb : nodeRefBytes s child0.toNat = 33 := by
            simp [nodeRefBytes, hc0_nat, hm_ne0, hlt32']
          rw [if_neg hlt32, if_pos rfl, evaluateHOLFiniteState_skip] at hret ⊢
          dsimp only at hret ⊢
          let contH : ProgHOL 64 :=
            .seq
              (.storeByte (.var .local (ofString "dst")) (.const 160))
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .var .local (ofString "h"),
                   .const 32])
                (.return (.const 33)))
          have hnt_dc : (evaluateHOLFiniteState srl
              (.decCall (ofString "h") .one (ofString "node_hash_cached")
                [.var .local (ofString "child")] contH)).1 ≠ some .timeOut := by
            rintro hto
            change (evaluateHOLFiniteState srl
              (.decCall (ofString "h") .one (ofString "node_hash_cached")
                [.var .local (ofString "child")] contH)).1 = some (.returned v) at hret
            rw [hto] at hret; cases hret
          have hdc := eval_decCall_node_hash_cached srl Nd "h"
            (.var .local (ofString "child")) child0 contH gw
            hc hAR_srl hN hchild_nd (by simp [evalHOLExact, hsrl_child]) hgw hnt_dc
          dsimp only at hdc
          rcases hdc with ⟨hw, mid, hmid_loc, heff24_mid, _, _, hnt_cont, hdc_eq⟩ |
              ⟨_, hno_ret, _, _, _⟩
          · change (evaluateHOLFiniteState srl
                (.decCall (ofString "h") .one (ofString "node_hash_cached")
                  [.var .local (ofString "child")] contH)).1 = some (.returned v) at hret
            rw [hdc_eq] at hret ⊢
            dsimp only at hret ⊢
            have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word hw)) := by
              rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
              rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsrl_dst,
                show ofString "h" ≠ ofString "dst" by decide]
            have hAR_mid : ArenaReady mid := heff24_mid.arena
            have heff_s_mid : HeapByteEff s mid R24 gw := by
              have h0 : HeapByteEff s srl R24 gw :=
                ((HeapByteEff.refl hAR R24 gw).locals_clock srp.locals srp.clock).locals_clock srl.locals srl.clock
              have h1 : HeapByteEff srl mid R24 gw :=
                heff24_mid.mono
                  (fun i hi _ => Or.inl ⟨i, List.mem_append_right _ hi, le_rfl, le_rfl⟩)
                  (fun _ hg => hg)
              exact h0.trans h1
            dsimp only [contH] at hret hnt_cont ⊢
            rw [evaluateHOLFiniteState_seq_line780] at hret hnt_cont ⊢
            rcases hsb : evaluateHOLFiniteState mid
                (.storeByte (.var .local (ofString "dst")) (.const 160)) with ⟨rsb, m3⟩
            simp only [hsb] at hret hnt_cont ⊢
            rcases storeByte_only_none_or_error_local mid (.var .local (ofString "dst")) (.const 160) with hsn | hse
            · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hret hnt_cont ⊢
              obtain ⟨hbre3, hm3_loc⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
                simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
                subst hdst_ev
                obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
                exact ⟨iv, hiv, h1, by omega⟩)
              have heff_m3 : HeapByteEff mid m3 R24 gw :=
                hmono_rl mid m3 (HeapByteEff.of_m11_bre hAR_mid hbre3)
              have hm3_h : m3.locals.lookup (ofString "h") = some (.val (.word hw)) := by
                rw [hm3_loc]; exact hmid_h
              have hm3_dst : m3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
                rw [hm3_loc]; exact hmid_dst
              have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
                rw [BitVec.toNat_add]; change (dst0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
              rw [evaluateHOLFiniteState_seq_line780] at hret hnt_cont ⊢
              rcases hmc : evaluateHOLFiniteState m3
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "dst"), .const 1],
                     .var .local (ofString "h"),
                     .const 32]) with ⟨rmc, m4⟩
              have hnt_mc : rmc ≠ some .timeOut := by
                rintro rfl; rw [hmc] at hnt_cont; exact hnt_cont rfl
              have hmc_spec := eval_call_memcpy_heap m3
                (.op .add [.var .local (ofString "dst"), .const 1])
                (.var .local (ofString "h"))
                (.const 32)
                (dst0 + 1) hw 32 Rl gw heff_m3.arena.1.code heff_m3.arena
                (by simp [evalHOLExact, evalListHOLExact, hm3_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
                (by simp [evalHOLExact, hm3_h])
                (by simp [evalHOLExact])
                (fun _ => by
                  obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
                  have h32 : (32 : BitVec 64).toNat = 32 := rfl
                  exact ⟨iv, hiv, by rw [hdst1_nat]; omega, by rw [hdst1_nat, h32]; omega⟩)
                (by rw [hmc]; exact hnt_mc)
              dsimp only at hmc_spec; rw [hmc] at hmc_spec; simp only [hmc] at hret ⊢
              cases rmc with
              | some rmc' =>
                dsimp only at hret
                injection hret with hret'; subst hret'
                exact False.elim (hmc_spec.2 (by simp) (Or.inl ⟨v, rfl⟩))
              | none =>
                dsimp only at hret ⊢
                obtain ⟨heff_m4, _, _⟩ := hmc_spec.1 rfl
                rw [evaluateHOLFiniteState_return] at hret ⊢
                simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                  Nat.one_le_ofNat, ↓reduceIte] at hret ⊢
                injection hret with hret'; injection hret' with hv_eq
                have heff_tot : HeapByteEff s
                    { m4.emptyLocalsHOLFinite with
                      locals := HolFiniteMapExact.resVarEq
                        (HolFiniteMapExact.resVarEq
                          (HolFiniteMapExact.resVarEq m4.emptyLocalsHOLFinite.locals
                            (ofString "h", srl.locals.lookup (ofString "h")))
                          (ofString "rl", srp.locals.lookup (ofString "rl")))
                        (ofString "rp", s.locals.lookup (ofString "rp")) } R24 gw :=
                  ((heff_s_mid.trans heff_m3).trans (hmono_rl m3 m4 heff_m4)).locals_clock _ _
                exact ⟨33, hv_eq.symm, by rw [hnrb]; rfl, heff_tot, hmono_cache _ heff_tot⟩
            · rw [hsb] at hse; dsimp only at hse; subst hse; simp at hret
          · exact False.elim (hno_ret v hret)

private theorem eval_node_write_ref_nodeHeap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (child0 dst0 : BitVec 64)
    (Rl : List Ivl) (gw : List String) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hN : NodeHeap s Nd)
    (hchild_in : RootIn Nd child0.toNat)
    (hchild_loc : s.locals.lookup (ofString "child") = some (.val (.word child0)))
    (hdst_loc : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hdst_fit : dst0.toNat + nodeRefBytes s child0.toNat ≤ heapEnd)
    (hin_ivl : ∃ iv ∈ Rl, iv.1 ≤ dst0.toNat ∧ dst0.toNat + nodeRefBytes s child0.toNat ≤ iv.1 + iv.2)
    (hgw : "heap_ptr" ∈ gw)
    (hdisj_rl : ∀ e ∈ Rl, 0 < e.2 → ∀ o ∈ nodeExtents s Nd, Disj e o)
    (hdisj_kc : ∀ o ∈ nodeExtents s Nd,
      Disj (bufferRegion s ("keccak_pad", 136)) o ∧
      Disj (bufferRegion s ("keccak_st", 200)) o)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_write_ref)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_write_ref)).2
    ∃ w : BitVec 64,
      v = .val (.word w) ∧
      w.toNat = nodeRefBytes s child0.toNat ∧
      HeapByteEff s post (Rl ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)) gw ∧
      HeapByteEff s post (Rl ++ (nodeCacheIvls Nd ++ keccakBufIvls s)) gw ∧
      NodeHeap post Nd ∧
      nodeExtents post Nd = nodeExtents s Nd ∧
      (∀ n ∈ Nd, memW post n = memW s n ∧ memW post (n + 8) = memW s (n + 8) ∧
        memW post (n + 16) = memW s (n + 16)) ∧
      (∀ m, RootIn Nd m → nodeRefBytes post m = nodeRefBytes s m) := by
  intro post; dsimp only [post]
  obtain ⟨w, hv, hw, heff24, heff_cache⟩ :=
    eval_node_write_ref_heapByteEff s Nd child0 dst0 Rl gw v
      hc hAR hN hchild_in hchild_loc hdst_loc hdst_fit hin_ivl hgw hret
  have heff_reord : HeapByteEff s post (Nd.map (fun n => (n + 24, 8)) ++ (Rl ++ keccakBufIvls s)) gw := by
    refine heff24.mono (fun i hi _ => ?_) (fun _ hg => hg)
    rcases List.mem_append.1 hi with hrl | hrest
    · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_left _ hrl), le_rfl, le_rfl⟩
    · rcases List.mem_append.1 hrest with hm24 | hkc
      · exact Or.inl ⟨i, List.mem_append_left _ hm24, le_rfl, le_rfl⟩
      · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkc), le_rfl, le_rfl⟩
  have hkc_disj := keccakBufIvls_disj_of_buffers hdisj_kc
  obtain ⟨hN_post, hext_post, hw012⟩ :=
    nodeHeap_of_hashOnly_heapByteEff hAR hN heff_reord (fun e he hpos o ho => by
      rcases List.mem_append.1 he with hrl | hkc
      · exact hdisj_rl e hrl hpos o ho
      · exact hkc_disj e hkc o ho)
  refine ⟨w, hv, hw, heff24, heff_cache, hN_post, hext_post, hw012, ?_⟩
  intro m hm
  exact nodeRefBytes_congr (fun n hn => (hw012 n hn).1) (fun n hn => (hw012 n hn).2.2) hm

private theorem eval_decCall_node_write_ref {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (lname : String)
    (childExp dstExp : ExpHOL 64) (child0 dst0 : BitVec 64)
    (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    (hN : NodeHeap s Nd)
    (hchild_in : RootIn Nd child0.toNat)
    (hchild_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) childExp =
      some (.val (.word child0)))
    (hdst_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hdst_fit : dst0.toNat + nodeRefBytes s child0.toNat ≤ heapEnd)
    (hin_ivl : ∃ iv ∈ Rl, iv.1 ≤ dst0.toNat ∧ dst0.toNat + nodeRefBytes s child0.toNat ≤ iv.1 + iv.2)
    (hgw : "heap_ptr" ∈ gw)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "node_write_ref") [childExp, dstExp] cont)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "node_write_ref") [childExp, dstExp] cont)
    (∃ (w : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      w.toNat = nodeRefBytes s child0.toNat ∧
      mid.locals = s.locals.update (ofString lname, .val (.word w)) ∧
      HeapByteEff s mid (Rl ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)) gw ∧
      HeapByteEff s mid (Rl ++ (nodeCacheIvls Nd ++ keccakBufIvls s)) gw ∧
      ((∀ e ∈ Rl, 0 < e.2 → ∀ o ∈ nodeExtents s Nd, Disj e o) →
        (∀ o ∈ nodeExtents s Nd,
          Disj (bufferRegion s ("keccak_pad", 136)) o ∧
          Disj (bufferRegion s ("keccak_st", 200)) o) →
        NodeHeap mid Nd ∧
        nodeExtents mid Nd = nodeExtents s Nd ∧
        (∀ n ∈ Nd, memW mid n = memW s n ∧ memW mid (n + 8) = memW s (n + 8) ∧
          memW mid (n + 16) = memW s (n + 16)) ∧
        (∀ m, RootIn Nd m → nodeRefBytes mid m = nodeRefBytes s m)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      out = ((evaluateHOLFiniteState mid cont).1,
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) })) ∨
    (out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) ∧
      out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧
      (Resumes out.1 →
        HeapByteEff s out.2 (Rl ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)) gw ∧
        HeapByteEff s out.2 (Rl ++ (nodeCacheIvls Nd ++ keccakBufIvls s)) gw)) := by
  intro out; dsimp only [out]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [childExp, dstExp] = some [.val (.word child0), .val (.word dst0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hchild_ev, hdst_ev]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "node_write_ref")
    (ofString "child") (ofString "dst")
    (sourceFnBody Guest.Software.guestFn_node_write_ref) child0 dst0 (by decide)
    (by rw [hc]; exact lookup_node_write_ref)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "child", ValueHOL.val (.word child0))).update
      (ofString "dst", ValueHOL.val (.word dst0))
    set ent := callEntryStateHOLFinite s cmap
    have hAR_ent : ArenaReady ent := ⟨guestInv_callEntry s cmap hAR.1, hAR.2⟩
    have hent_child : ent.locals.lookup (ofString "child") = some (.val (.word child0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "dst" ≠ ofString "child" by decide]
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hN_ent : NodeHeap ent Nd := hN
    have hkc_ent : keccakBufIvls ent = keccakBufIvls s := rfl
    have hnrb_ent : nodeRefBytes ent child0.toNat = nodeRefBytes s child0.toNat := rfl
    rcases hbody : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_node_write_ref) with ⟨rb, sb⟩
    have hnt_ent : rb ≠ some .timeOut := by
      rintro rfl; rw [hbody] at hnt; exact hnt rfl
    simp only [hbody] at hnt ⊢
    cases rb with
    | none =>
      right
      exact ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => False.elim (not_resumes_error hres)⟩
    | some r0 =>
      cases r0 with
      | timeOut => exact absurd rfl hnt_ent
      | returned rv =>
        obtain ⟨w, rfl, hw_nat, heff24_ent, heff_cache_ent⟩ :=
          eval_node_write_ref_heapByteEff ent Nd child0 dst0 Rl gw rv hc hAR_ent hN_ent hchild_in
            hent_child hent_dst (by rw [hnrb_ent]; exact hdst_fit) (by rw [hnrb_ent]; exact hin_ivl)
            hgw (by rw [hbody])
        rw [hbody, hkc_ent] at heff24_ent heff_cache_ent
        rw [hnrb_ent] at hw_nat
        dsimp only at heff24_ent heff_cache_ent
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnt ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word w)) { sb with locals := s.locals }
        have heff_s_ent24 : HeapByteEff s ent (Rl ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)) gw :=
          (HeapByteEff.refl hAR _ gw).locals_clock ent.locals ent.clock
        have heff_s_ent_cache : HeapByteEff s ent (Rl ++ (nodeCacheIvls Nd ++ keccakBufIvls s)) gw :=
          (HeapByteEff.refl hAR _ gw).locals_clock ent.locals ent.clock
        have heff24_mid : HeapByteEff s mid (Rl ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)) gw :=
          (heff_s_ent24.trans heff24_ent).locals_clock mid.locals mid.clock
        have heff_cache_mid : HeapByteEff s mid (Rl ++ (nodeCacheIvls Nd ++ keccakBufIvls s)) gw :=
          (heff_s_ent_cache.trans heff_cache_ent).locals_clock mid.locals mid.clock
        left
        refine ⟨w, mid, hw_nat, rfl, heff24_mid, heff_cache_mid, ?_, hnt, rfl⟩
        intro hdisj_rl hdisj_kc
        have heff_reord : HeapByteEff s mid (Nd.map (fun n => (n + 24, 8)) ++ (Rl ++ keccakBufIvls s)) gw := by
          refine heff24_mid.mono (fun i hi _ => ?_) (fun _ hg => hg)
          rcases List.mem_append.1 hi with hrl | hrest
          · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_left _ hrl), le_rfl, le_rfl⟩
          · rcases List.mem_append.1 hrest with hm24 | hkc
            · exact Or.inl ⟨i, List.mem_append_left _ hm24, le_rfl, le_rfl⟩
            · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkc), le_rfl, le_rfl⟩
        have hkc_disj := keccakBufIvls_disj_of_buffers hdisj_kc
        obtain ⟨hN_mid, hext_mid, hw012_mid⟩ :=
          nodeHeap_of_hashOnly_heapByteEff hAR hN heff_reord (fun e he hpos o ho => by
            rcases List.mem_append.1 he with hrl | hkc
            · exact hdisj_rl e hrl hpos o ho
            · exact hkc_disj e hkc o ho)
        refine ⟨hN_mid, hext_mid, hw012_mid, fun m hm => ?_⟩
        exact nodeRefBytes_congr (fun n hn => (hw012_mid n hn).1) (fun n hn => (hw012_mid n hn).2.2) hm
      | «break» =>
        right
        exact ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => False.elim (not_resumes_error hres)⟩
      | «continue» =>
        right
        exact ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => False.elim (not_resumes_error hres)⟩
      | error =>
        right
        exact ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => False.elim (not_resumes_error hres)⟩
      | finalFfi f =>
        right
        refine ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => ?_⟩
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | exception eid ev =>
        right
        refine ⟨by simp, fun _ => by simp, by simp, by simp, fun hres => ?_⟩
        rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
        · simp at h
        · injection h with h'; injection h' with he1 he2; subst he1 he2
          let R24 : List Ivl := Rl ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)
          let Rc : List Ivl := Rl ++ (nodeCacheIvls Nd ++ keccakBufIvls s)
          have hex_eff : HeapByteEff ent sb R24 gw := by
            have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
            have hhe264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
            have h264_lim : heapLimit ≤ 2 ^ 64 := by decide
            have hb : sourceFnBody Guest.Software.guestFn_node_write_ref =
                .seq
                  (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0))
                    (.seq (.storeByte (.var .local (ofString "dst")) (.const 128)) (.return (.const 1))) .skip)
                  (.seq
                    (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
                      (.seq
                        (.storeByte (.var .local (ofString "dst")) (.const 160))
                        (.seq
                          (.call (some (none, none)) (ofString "memcpy")
                            [.op .add [.var .local (ofString "dst"), .const 1],
                             .load .one (.op .add [.var .local (ofString "child"), .const 24]),
                             .const 32])
                          (.return (.const 33))))
                      .skip)
                    (.seq
                      (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
                        (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip)
                      (.dec (ofString "rp") .one (.load .one (.op .add [.var .local (ofString "child"), .const 8]))
                        (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
                          (.seq
                            (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                              (.seq
                                (.call (some (none, none)) (ofString "memcpy")
                                  [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")])
                                (.return (.var .local (ofString "rl"))))
                              .skip)
                            (.decCall (ofString "h") .one (ofString "node_hash_cached") [.var .local (ofString "child")]
                              (.seq
                                (.storeByte (.var .local (ofString "dst")) (.const 160))
                                (.seq
                                  (.call (some (none, none)) (ofString "memcpy")
                                    [.op .add [.var .local (ofString "dst"), .const 1],
                                     .var .local (ofString "h"),
                                     .const 32])
                                  (.return (.const 33)))))))))) := rfl
            rw [hb, evaluateHOLFiniteState_seq_line780] at hbody
            have hcmp0 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
                (.cmp .equal (.var .local (ofString "child")) (.const 0)) =
                some (.val (.word (if child0 = 0 then 1 else 0))) := by
              simp [evalHOLExact, hent_child, Compiler.Encoders.Asm.wordCmpHOL]
            by_cases hc0 : child0 = 0
            · exfalso
              subst hc0
              rw [evaluateHOLFiniteState_ite, hcmp0, if_pos rfl] at hbody; dsimp only at hbody
              rw [if_neg h10, evaluateHOLFiniteState_seq_line780] at hbody
              rcases storeByte_only_none_or_error_local ent (.var .local (ofString "dst")) (.const 128) with hsn | hse
              · rcases hsb : evaluateHOLFiniteState ent (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
                rw [hsb] at hsn hbody; dsimp only at hsn hbody; subst hsn; dsimp only at hbody
                rw [evaluateHOLFiniteState_return] at hbody
                simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hbody
              · rcases hsb : evaluateHOLFiniteState ent (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
                rw [hsb] at hse hbody; dsimp only at hse hbody; subst hse; simp at hbody
            · have hc0_nat : child0.toNat ≠ 0 := fun h => hc0 (BitVec.eq_of_toNat_eq h)
              have hchild_nd : child0.toNat ∈ Nd := by
                rcases hchild_in with h0 | hm
                · exact absurd h0 hc0_nat
                · exact hm
              rw [evaluateHOLFiniteState_ite, hcmp0, if_neg hc0] at hbody; dsimp only at hbody
              rw [if_pos rfl, evaluateHOLFiniteState_skip] at hbody; dsimp only at hbody
              obtain ⟨_, _, hin_c, hw_c, _⟩ := hN_ent.1 child0.toNat hchild_nd
              have hsz_c := nodeSize_ge32 (memW ent child0.toNat)
              have hhi_c : child0.toNat + nodeSize (memW ent child0.toNat) ≤ 2 ^ 64 := by
                have := hin_c.2; dsimp [nodeIvl] at this; omega
              obtain ⟨kw, hld0, hkw_nat⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 0)
                hw_c (by decide) (by omega) hhi_c
                (e := .op .add [.var .local (ofString "child"), .const 0])
                (by simp [evalHOLExact, evalListHOLExact, hent_child, wordOpHOL, wordOp, valueIsWord, valueWord])
              simp only [Nat.add_zero] at hkw_nat
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hbody
              have hcmp_k : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
                  (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0)) =
                  some (.val (.word (if kw = 0 then 1 else 0))) := by
                unfold evalHOLExact; rw [hld0]; simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
              rw [hcmp_k] at hbody; dsimp only at hbody
              by_cases hkw0 : kw = 0
              · exfalso
                have hm0 : memW s child0.toNat = 0 := by
                  change memW ent child0.toNat = 0; rw [← hkw_nat, hkw0]; rfl
                have hnrb : nodeRefBytes s child0.toNat = 33 := by simp [nodeRefBytes, hc0_nat, hm0]
                rw [if_pos hkw0, if_neg h10, evaluateHOLFiniteState_seq_line780] at hbody
                rcases hsb : evaluateHOLFiniteState ent (.storeByte (.var .local (ofString "dst")) (.const 160)) with ⟨rsb, s1⟩
                rw [hsb] at hbody
                rcases storeByte_only_none_or_error_local ent (.var .local (ofString "dst")) (.const 160) with hsn | hse
                · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hbody
                  obtain ⟨hbre1, hs1_loc⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
                    simp only [evalHOLExact, hent_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
                    subst hdst_ev; obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl; exact ⟨iv, hiv, h1, by omega⟩)
                  have heff_s1 : HeapByteEff ent s1 Rl gw := HeapByteEff.of_m11_bre hAR_ent hbre1
                  have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hs1_loc]; exact hent_dst
                  have hs1_child : s1.locals.lookup (ofString "child") = some (.val (.word child0)) := by rw [hs1_loc]; exact hent_child
                  have hw_c_s1 : WordsOK s1 (child0.toNat, nodeSize (memW ent child0.toNat)) :=
                    P3MptSet.wordsOK_transfer hAR_ent.1 heff_s1.arena.1 hw_c
                  obtain ⟨hw24, hld24_s1, _⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 24)
                    hw_c_s1 (by decide) (by omega) hhi_c
                    (e := .op .add [.var .local (ofString "child"), .const 24])
                    (by simp [evalHOLExact, evalListHOLExact, hs1_child, wordOpHOL, wordOp, valueIsWord, valueWord])
                  have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
                    rw [BitVec.toNat_add]; change (dst0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
                  rw [evaluateHOLFiniteState_seq_line780] at hbody
                  rcases hmc : evaluateHOLFiniteState s1
                      (.call (some (none, none)) (ofString "memcpy")
                        [.op .add [.var .local (ofString "dst"), .const 1],
                         .load .one (.op .add [.var .local (ofString "child"), .const 24]),
                         .const 32]) with ⟨rmc, s2⟩
                  have hnt_mc : rmc ≠ some .timeOut := by
                    rintro rfl; rw [hmc] at hbody; simp at hbody
                  have hmc_spec := eval_call_memcpy_heap s1
                    (.op .add [.var .local (ofString "dst"), .const 1])
                    (.load .one (.op .add [.var .local (ofString "child"), .const 24]))
                    (.const 32)
                    (dst0 + 1) hw24 32 Rl gw heff_s1.arena.1.code heff_s1.arena
                    (by simp [evalHOLExact, evalListHOLExact, hs1_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
                    hld24_s1 (by simp [evalHOLExact])
                    (fun _ => by
                      obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
                      have h32 : (32 : BitVec 64).toNat = 32 := rfl
                      exact ⟨iv, hiv, by rw [hdst1_nat]; omega, by rw [hdst1_nat, h32]; omega⟩)
                    (by rw [hmc]; exact hnt_mc)
                  dsimp only at hmc_spec; rw [hmc] at hmc_spec hbody
                  cases rmc with
                  | some rmc' =>
                    dsimp only at hbody
                    have hfst := congrArg Prod.fst hbody
                    dsimp only at hfst
                    injection hfst with hr; subst hr
                    exact hmc_spec.2 (by simp) (Or.inr ⟨eid, ev, rfl, hne⟩)
                  | none =>
                    dsimp only at hbody
                    have hfst := congrArg Prod.fst hbody
                    dsimp only at hfst
                    rw [evaluateHOLFiniteState_return] at hfst
                    simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hfst
                · rw [hsb] at hse; dsimp only at hse; subst hse; simp at hbody
              · have hm_ne0 : memW s child0.toNat ≠ 0 := by
                  intro h; apply hkw0; apply BitVec.eq_of_toNat_eq
                  change kw.toNat = (0 : BitVec 64).toNat
                  rw [hkw_nat]; exact h
                rw [if_neg hkw0, if_pos rfl, evaluateHOLFiniteState_skip] at hbody; dsimp only at hbody
                rw [evaluateHOLFiniteState_seq_line780] at hbody
                rcases hite3 : evaluateHOLFiniteState ent
                    (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
                      (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨r3, s3⟩
                rw [hite3] at hbody
                cases r3 with
                | some r3' =>
                  dsimp only at hbody
                  have hro_ite3 := evaluate_roEncProg
                    (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
                      (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) rfl ent hc
                  rw [hite3] at hro_ite3; dsimp only at hro_ite3
                  injection hbody with _ hsb_eq
                  rw [← hsb_eq, hro_ite3]
                  exact (HeapByteEff.refl hAR_ent R24 gw).locals_clock _ _
                | none =>
                  have hs3 : s3 = ent := by
                    have hmf := eval_call_mpt_fail_no_none_no_ret ent 13 hc
                    rw [evaluateHOLFiniteState_ite] at hite3
                    split at hite3
                    · split at hite3
                      · rw [evaluateHOLFiniteState_skip] at hite3; exact (Prod.mk.inj hite3).2.symm
                      · exact False.elim (hmf.1 (congrArg Prod.fst hite3))
                    · cases hite3
                  rw [hs3] at hbody; dsimp only at hbody
                  obtain ⟨rpw, hld8, _⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 8)
                    hw_c (by decide) (by omega) hhi_c
                    (e := .op .add [.var .local (ofString "child"), .const 8])
                    (by simp [evalHOLExact, evalListHOLExact, hent_child, wordOpHOL, wordOp, valueIsWord, valueWord])
                  have hsh_rp : shapeEqHOL .one (shapeOfHOLExact (.val (.word rpw) : ValueHOL 64)) = true := by
                    simp [shapeOfHOLExact, shapeEqHOL]
                  rw [evaluateHOLFiniteState_dec_total] at hbody; dsimp only at hbody
                  rw [hld8] at hbody; dsimp only at hbody; rw [if_pos hsh_rp] at hbody
                  set srp := setVarHOLFinite (ofString "rp") (.val (.word rpw)) ent
                  have hAR_srp : ArenaReady srp := ⟨guestInv_setVar _ _ _ hAR_ent.1, hAR_ent.2⟩
                  have hsrp_rp : srp.locals.lookup (ofString "rp") = some (.val (.word rpw)) := by
                    simp [srp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hsrp_child : srp.locals.lookup (ofString "child") = some (.val (.word child0)) := by
                    simp [srp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_child,
                      show ofString "rp" ≠ ofString "child" by decide]
                  have hsrp_dst : srp.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
                    simp [srp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
                      show ofString "rp" ≠ ofString "dst" by decide]
                  obtain ⟨rlw, hld16, hrlw_nat⟩ := eval_load_memW_of_wordsOK (s := srp) (base := child0) (off := 16)
                    hw_c (by decide) (by omega) hhi_c
                    (e := .op .add [.var .local (ofString "child"), .const 16])
                    (by simp [evalHOLExact, evalListHOLExact, hsrp_child, wordOpHOL, wordOp, valueIsWord, valueWord])
                  have hrlw_eq : rlw.toNat = memW s (child0.toNat + 16) := hrlw_nat
                  have hsh_rl : shapeEqHOL .one (shapeOfHOLExact (.val (.word rlw) : ValueHOL 64)) = true := by
                    simp [shapeOfHOLExact, shapeEqHOL]
                  rw [evaluateHOLFiniteState_dec_total] at hbody; dsimp only at hbody
                  rw [hld16] at hbody; dsimp only at hbody; rw [if_pos hsh_rl] at hbody
                  set srl := setVarHOLFinite (ofString "rl") (.val (.word rlw)) srp
                  have hAR_srl : ArenaReady srl := ⟨guestInv_setVar _ _ _ hAR_srp.1, hAR_srp.2⟩
                  have hsrl_rl : srl.locals.lookup (ofString "rl") = some (.val (.word rlw)) := by
                    simp [srl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hsrl_rp : srl.locals.lookup (ofString "rp") = some (.val (.word rpw)) := by
                    simp [srl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrp_rp,
                      show ofString "rl" ≠ ofString "rp" by decide]
                  have hsrl_child : srl.locals.lookup (ofString "child") = some (.val (.word child0)) := by
                    simp [srl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrp_child,
                      show ofString "rl" ≠ ofString "child" by decide]
                  have hsrl_dst : srl.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
                    simp [srl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrp_dst,
                      show ofString "rl" ≠ ofString "dst" by decide]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hbody
                  have hcmp_rl : @evalHOLExact 64 F _ srl.toExact (fun a => Classical.propDecidable (srl.memaddrs a))
                      (.cmp .lower (.var .local (ofString "rl")) (.const 32)) =
                      some (.val (.word (if rlw.toNat < 32 then 1 else 0))) := by
                    simp [evalHOLExact, hsrl_rl, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
                  rw [hcmp_rl] at hbody; dsimp only at hbody
                  by_cases hlt32 : rlw.toNat < 32
                  · exfalso
                    have hlt32' : memW s (child0.toNat + 16) < 32 := by rw [← hrlw_eq]; exact hlt32
                    have hnrb : nodeRefBytes s child0.toNat = rlw.toNat := by
                      simp [nodeRefBytes, hc0_nat, hm_ne0, hlt32', hrlw_eq]
                    rw [if_pos hlt32, if_neg h10, evaluateHOLFiniteState_seq_line780] at hbody
                    rcases hmc : evaluateHOLFiniteState srl
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "dst"), .var .local (ofString "rp"), .var .local (ofString "rl")]) with ⟨rmc, m2⟩
                    have hnt_mc : rmc ≠ some .timeOut := by
                      rintro rfl; rw [hmc] at hbody; simp at hbody
                    have hmc_spec := eval_call_memcpy_heap srl
                      (.var .local (ofString "dst")) (.var .local (ofString "rp")) (.var .local (ofString "rl"))
                      dst0 rpw rlw Rl gw hc hAR_srl
                      (by simp [evalHOLExact, hsrl_dst])
                      (by simp [evalHOLExact, hsrl_rp])
                      (by simp [evalHOLExact, hsrl_rl])
                      (fun _ => by
                        obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
                        exact ⟨iv, hiv, h1, by omega⟩)
                      (by rw [hmc]; exact hnt_mc)
                    dsimp only at hmc_spec; rw [hmc] at hmc_spec hbody
                    cases rmc with
                    | some rmc' =>
                      dsimp only at hbody
                      have hfst := congrArg Prod.fst hbody
                      dsimp only at hfst
                      injection hfst with hr; subst hr
                      exact hmc_spec.2 (by simp) (Or.inr ⟨eid, ev, rfl, hne⟩)
                    | none =>
                      dsimp only at hbody
                      have hfst := congrArg Prod.fst hbody
                      dsimp only at hfst
                      obtain ⟨_, hm2_loc, _⟩ := hmc_spec.1 rfl
                      have hm2_rl : m2.locals.lookup (ofString "rl") = some (.val (.word rlw)) := by
                        rw [hm2_loc]; exact hsrl_rl
                      have hret_m2 : evaluateHOLFiniteState m2 (.return (.var .local (ofString "rl"))) =
                          (some (.returned (.val (.word rlw))), m2.emptyLocalsHOLFinite) := by
                        rw [evaluateHOLFiniteState_return]
                        simp [evalHOLExact, hm2_rl, shapeOfHOLExact, sizeOfShapeWithContextHOL]
                      rw [hret_m2] at hfst
                      simp at hfst
                  · have hlt32' : ¬ memW s (child0.toNat + 16) < 32 := by rw [← hrlw_eq]; exact hlt32
                    have hnrb : nodeRefBytes s child0.toNat = 33 := by
                      simp [nodeRefBytes, hc0_nat, hm_ne0, hlt32']
                    rw [if_neg hlt32, if_pos rfl, evaluateHOLFiniteState_skip] at hbody; dsimp only at hbody
                    let contH : ProgHOL 64 :=
                      .seq
                        (.storeByte (.var .local (ofString "dst")) (.const 160))
                        (.seq
                          (.call (some (none, none)) (ofString "memcpy")
                            [.op .add [.var .local (ofString "dst"), .const 1],
                             .var .local (ofString "h"),
                             .const 32])
                          (.return (.const 33)))
                    have hbody_fst : (evaluateHOLFiniteState srl
                        (.decCall (ofString "h") .one (ofString "node_hash_cached")
                          [.var .local (ofString "child")] contH)).1 = some (.exception eid ev) :=
                      congrArg Prod.fst hbody
                    have hbody_snd : { (evaluateHOLFiniteState srl
                        (.decCall (ofString "h") .one (ofString "node_hash_cached")
                          [.var .local (ofString "child")] contH)).2 with
                        locals := HolFiniteMapExact.resVarEq
                          (HolFiniteMapExact.resVarEq
                            (evaluateHOLFiniteState srl
                              (.decCall (ofString "h") .one (ofString "node_hash_cached")
                                [.var .local (ofString "child")] contH)).2.locals
                            (ofString "rl", srp.locals.lookup (ofString "rl")))
                          (ofString "rp", ent.locals.lookup (ofString "rp")) } = sb :=
                      congrArg Prod.snd hbody
                    have hnt_dc : (evaluateHOLFiniteState srl
                        (.decCall (ofString "h") .one (ofString "node_hash_cached")
                          [.var .local (ofString "child")] contH)).1 ≠ some .timeOut := by
                      rw [hbody_fst]; simp
                    have hdc := eval_decCall_node_hash_cached srl Nd "h"
                      (.var .local (ofString "child")) child0 contH gw
                      hc hAR_srl hN hchild_nd (by simp [evalHOLExact, hsrl_child]) hgw hnt_dc
                    dsimp only at hdc
                    have heff_ent_srl : HeapByteEff ent srl R24 gw :=
                      ((HeapByteEff.refl hAR_ent R24 gw).locals_clock srp.locals srp.clock).locals_clock srl.locals srl.clock
                    rcases hdc with ⟨hw, mid, hmid_loc, heff24_mid, _, _, hnt_cont, hdc_eq⟩ |
                        ⟨_, _, _, _, hres_imp⟩
                    · exfalso
                      rw [hdc_eq] at hbody_fst; dsimp only at hbody_fst
                      have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word hw)) := by
                        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                      have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
                        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsrl_dst,
                          show ofString "h" ≠ ofString "dst" by decide]
                      dsimp only [contH] at hbody_fst hnt_cont
                      rw [evaluateHOLFiniteState_seq_line780] at hbody_fst hnt_cont
                      rcases hsb : evaluateHOLFiniteState mid
                          (.storeByte (.var .local (ofString "dst")) (.const 160)) with ⟨rsb, m3⟩
                      rw [hsb] at hbody_fst hnt_cont
                      rcases storeByte_only_none_or_error_local mid (.var .local (ofString "dst")) (.const 160) with hsn | hse
                      · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hbody_fst hnt_cont
                        obtain ⟨hbre3, hm3_loc⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
                          simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
                          subst hdst_ev; obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl; exact ⟨iv, hiv, h1, by omega⟩)
                        have heff_m3 : HeapByteEff mid m3 Rl gw := HeapByteEff.of_m11_bre heff24_mid.arena hbre3
                        have hm3_h : m3.locals.lookup (ofString "h") = some (.val (.word hw)) := by rw [hm3_loc]; exact hmid_h
                        have hm3_dst : m3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hm3_loc]; exact hmid_dst
                        have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
                          rw [BitVec.toNat_add]; change (dst0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
                        rw [evaluateHOLFiniteState_seq_line780] at hbody_fst hnt_cont
                        rcases hmc : evaluateHOLFiniteState m3
                            (.call (some (none, none)) (ofString "memcpy")
                              [.op .add [.var .local (ofString "dst"), .const 1],
                               .var .local (ofString "h"),
                               .const 32]) with ⟨rmc, m4⟩
                        have hnt_mc : rmc ≠ some .timeOut := by
                          rintro rfl; rw [hmc] at hnt_cont; exact hnt_cont rfl
                        have hmc_spec := eval_call_memcpy_heap m3
                          (.op .add [.var .local (ofString "dst"), .const 1])
                          (.var .local (ofString "h"))
                          (.const 32)
                          (dst0 + 1) hw 32 Rl gw heff_m3.arena.1.code heff_m3.arena
                          (by simp [evalHOLExact, evalListHOLExact, hm3_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
                          (by simp [evalHOLExact, hm3_h])
                          (by simp [evalHOLExact])
                          (fun _ => by
                            obtain ⟨iv, hiv, h1, h2⟩ := hin_ivl
                            have h32 : (32 : BitVec 64).toNat = 32 := rfl
                            exact ⟨iv, hiv, by rw [hdst1_nat]; omega, by rw [hdst1_nat, h32]; omega⟩)
                          (by rw [hmc]; exact hnt_mc)
                        dsimp only at hmc_spec; rw [hmc] at hmc_spec hbody_fst
                        cases rmc with
                        | some rmc' =>
                          dsimp only at hbody_fst
                          injection hbody_fst with hr; subst hr
                          exact hmc_spec.2 (by simp) (Or.inr ⟨eid, ev, rfl, hne⟩)
                        | none =>
                          dsimp only at hbody_fst
                          rw [evaluateHOLFiniteState_return] at hbody_fst
                          simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hbody_fst
                      · rw [hsb] at hse; dsimp only at hse; subst hse; simp at hbody_fst
                    · obtain ⟨heff_dc24, _⟩ := hres_imp (Or.inr ⟨eid, ev, hbody_fst, hne⟩)
                      have hkc_srl : keccakBufIvls srl = keccakBufIvls s := rfl
                      rw [hkc_srl] at heff_dc24
                      have heff_dc_r24 : HeapByteEff srl
                          (evaluateHOLFiniteState srl
                            (.decCall (ofString "h") .one (ofString "node_hash_cached")
                              [.var .local (ofString "child")] contH)).2 R24 gw :=
                        heff_dc24.mono
                          (fun i hi _ => Or.inl ⟨i, List.mem_append_right _ hi, le_rfl, le_rfl⟩)
                          (fun _ hg => hg)
                      rw [← hbody_snd]
                      exact (heff_ent_srl.trans heff_dc_r24).locals_clock _ _
          have heff_s_sb24 : HeapByteEff s sb.emptyLocalsHOLFinite R24 gw :=
            (((HeapByteEff.refl hAR R24 gw).locals_clock ent.locals ent.clock).trans hex_eff).locals_clock _ _
          have heff_s_sb_cache : HeapByteEff s sb.emptyLocalsHOLFinite Rc gw := by
            refine heff_s_sb24.mono (fun i hi _ => ?_) (fun _ hg => hg)
            rcases List.mem_append.1 hi with hrl | hrest
            · exact Or.inl ⟨i, List.mem_append_left _ hrl, le_rfl, le_rfl⟩
            · rcases List.mem_append.1 hrest with hm24 | hkc
              · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
                exact Or.inl ⟨(m + 8, 24),
                  List.mem_append_right _ (List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩)),
                  by dsimp; omega, by dsimp; omega⟩
              · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkc), le_rfl, le_rfl⟩
          exact ⟨heff_s_sb24, heff_s_sb_cache⟩

/-! ## Milestone 2a: `_node_needs_rlp`, encoded byte length, `rlp_encode_bytes` exact, `_node_rlp_begin` -/

private theorem eval__node_needs_rlp_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (child0 : BitVec 64) (v : ValueHOL 64)
    (_hc : s.code = originalRuntimeCode)
    (hN : NodeHeap s Nd)
    (hchild_in : RootIn Nd child0.toNat)
    (hloc : s.locals.lookup (ofString "child") = some (.val (.word child0)))
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_needs_rlp)).1 =
      some (.returned v)) :
    ∃ fw : BitVec 64,
      v = .val (.word fw) ∧
      (fw ≠ 0 → child0.toNat ∈ Nd ∧ 1 ≤ memW s child0.toNat ∧ memW s child0.toNat ≤ 3) ∧
      (fw = 0 → child0.toNat = 0 ∨ memW s child0.toNat = 0 ∨ memW s (child0.toNat + 8) ≠ 0) ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_needs_rlp)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_needs_rlp)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_needs_rlp)).2.clock } := by
  have hb : sourceFnBody Guest.Software.guestFn__node_needs_rlp =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0)) (.return (.const 0)) .skip)
        (.seq
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
            (.return (.const 0)) .skip)
          (.seq
            (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
              (.return (.const 0)) .skip)
            (.return (.const 1)))) := rfl
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  rw [hb, evaluateHOLFiniteState_seq_line780] at hret ⊢
  have hcmp0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "child")) (.const 0)) =
      some (.val (.word (if child0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hloc, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hc0 : child0 = 0
  · subst hc0
    rw [evaluateHOLFiniteState_ite, hcmp0, if_pos rfl] at hret ⊢
    dsimp only at hret ⊢
    rw [if_neg h10, evaluateHOLFiniteState_return] at hret ⊢
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte] at hret ⊢
    injection hret with hr; injection hr with hv_eq; subst hv_eq
    exact ⟨0, rfl, fun h => absurd rfl h, fun _ => Or.inl rfl, by cases s; rfl⟩
  · have h264_lim : heapLimit ≤ 2 ^ 64 := by decide
    have hc0_nat : child0.toNat ≠ 0 := fun h => hc0 (BitVec.eq_of_toNat_eq h)
    have hchild_nd : child0.toNat ∈ Nd := hchild_in.resolve_left hc0_nat
    obtain ⟨hk3, _, hin_c, hw_c, _⟩ := hN.1 child0.toNat hchild_nd
    have hsz_c := nodeSize_ge32 (memW s child0.toNat)
    have hhi_c : child0.toNat + nodeSize (memW s child0.toNat) ≤ 2 ^ 64 := by
      have := hin_c.2; dsimp [nodeIvl] at this; omega
    rw [evaluateHOLFiniteState_ite, hcmp0, if_neg hc0] at hret ⊢
    dsimp only at hret ⊢
    rw [if_pos rfl, evaluateHOLFiniteState_skip] at hret ⊢
    dsimp only at hret ⊢
    obtain ⟨kw, hld0, hkw_nat⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 0)
      hw_c (by decide) (by omega) hhi_c
      (e := .op .add [.var .local (ofString "child"), .const 0])
      (by simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord])
    simp only [Nat.add_zero] at hkw_nat
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret ⊢
    have hcmp1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0)) =
        some (.val (.word (if kw = 0 then 1 else 0))) := by
      unfold evalHOLExact; rw [hld0]; simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp1] at hret ⊢; dsimp only at hret ⊢
    by_cases hkw0 : kw = 0
    · rw [if_pos hkw0, if_neg h10, evaluateHOLFiniteState_return] at hret ⊢
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte] at hret ⊢
      injection hret with hr; injection hr with hv_eq; subst hv_eq
      exact ⟨0, rfl, fun h => absurd rfl h, fun _ => Or.inr (Or.inl (by rw [← hkw_nat, hkw0]; rfl)),
        by cases s; rfl⟩
    · have hm_pos : 1 ≤ memW s child0.toNat := by
        have : kw.toNat ≠ 0 := fun h => hkw0 (BitVec.eq_of_toNat_eq h)
        omega
      rw [if_neg hkw0] at hret ⊢
      rw [if_pos rfl, evaluateHOLFiniteState_skip] at hret ⊢
      dsimp only at hret ⊢
      obtain ⟨rpw, hld8, hrpw_nat⟩ := eval_load_memW_of_wordsOK (base := child0) (off := 8)
        hw_c (by decide) (by omega) hhi_c
        (e := .op .add [.var .local (ofString "child"), .const 8])
        (by simp [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord])
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret ⊢
      have hcmp2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0)) =
          some (.val (.word (if rpw ≠ 0 then 1 else 0))) := by
        unfold evalHOLExact; rw [hld8]; simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp2] at hret ⊢; dsimp only at hret ⊢
      by_cases hrpw0 : rpw ≠ 0
      · rw [if_pos hrpw0, if_neg h10, evaluateHOLFiniteState_return] at hret ⊢
        simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte] at hret ⊢
        injection hret with hr; injection hr with hv_eq; subst hv_eq
        have hm8_ne : memW s (child0.toNat + 8) ≠ 0 := by
          rw [← hrpw_nat]; exact fun h => hrpw0 (BitVec.eq_of_toNat_eq h)
        exact ⟨0, rfl, fun h => absurd rfl h, fun _ => Or.inr (Or.inr hm8_ne), by cases s; rfl⟩
      · rw [if_neg hrpw0] at hret ⊢
        rw [if_pos rfl, evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return] at hret ⊢
        simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte] at hret ⊢
        injection hret with hr; injection hr with hv_eq; subst hv_eq
        exact ⟨1, rfl, fun _ => ⟨hchild_nd, hm_pos, hk3⟩, fun h => absurd h h10, by cases s; rfl⟩

private theorem eval_call_local__node_needs_rlp {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (lname : String)
    (childExp : ExpHOL 64) (child0 : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hN : NodeHeap s Nd)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hchild_in : RootIn Nd child0.toNat)
    (hchild_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) childExp =
      some (.val (.word child0)))
    (hnone : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "_node_needs_rlp")
        [childExp])).1 = none) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "_node_needs_rlp")
        [childExp])
    ∃ fw : BitVec 64,
      (fw ≠ 0 → child0.toNat ∈ Nd ∧ 1 ≤ memW s child0.toNat ∧ memW s child0.toNat ≤ 3) ∧
      (fw = 0 → child0.toNat = 0 ∨ memW s child0.toNat = 0 ∨ memW s (child0.toNat + 8) ≠ 0) ∧
      out.2 = { s with locals := s.locals.update (ofString lname, .val (.word fw)),
                       clock := out.2.clock } := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [childExp] =
      some [.val (.word child0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hchild_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "_node_needs_rlp") (ofString "child")
    (sourceFnBody Guest.Software.guestFn__node_needs_rlp) child0
    (by rw [hc]; exact lookup__node_needs_rlp)
  simp only [ha, hlk] at hnone ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnone
  · simp only [hcz, ↓reduceIte] at hnone ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "child", ValueHOL.val (.word child0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_child : ent.locals.lookup (ofString "child") = some (.val (.word child0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hcal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn__node_needs_rlp) with ⟨rc, sc⟩
    simp only [hcal] at hnone ⊢
    cases rc with
    | none => simp at hnone
    | some r0 =>
      cases r0 with
      | returned rv =>
        obtain ⟨fw, rfl, hnz, hz, hsc_eq⟩ :=
          eval__node_needs_rlp_returned ent Nd child0 rv hc hN hchild_in hent_child (by rw [hcal])
        rw [hcal] at hsc_eq; dsimp only at hsc_eq
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word fw) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word fw)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh, if_pos hval]
        refine ⟨fw, hnz, hz, ?_⟩
        dsimp only [setKvarHOLFinite, setVarHOLFinite]
        rw [hsc_eq]; cases s; rfl
      | _ => simp at hnone

private def rlpBytesLenPure (fb n : Nat) : Nat :=
  if n = 1 ∧ fb < 128 then 1 else rlpHeaderLenPure n + n

private theorem rlpBytesLenPure_bounds (fb n : Nat) :
    1 ≤ rlpBytesLenPure fb n ∧
    rlpBytesLenPure fb n ≤ rlpHeaderLenPure n + n ∧
    rlpBytesLenPure fb n ≤ n + 9 := by
  unfold rlpBytesLenPure
  have hb := rlpHeaderLenPure_bounds n
  split_ifs <;> omega

private theorem eval_rlp_bytes_encoded_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (fbw nw : BitVec 64)
    (hfb : s.locals.lookup (ofString "first_byte") = some (.val (.word fbw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).1 =
      some (.returned v)) :
    ∃ el : BitVec 64,
      v = .val (.word el) ∧ el.toNat = rlpBytesLenPure fbw.toNat nw.toNat := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len =
      .seq
        (.ite (.op .and [
            .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
            .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))])
          (.return (.const 1#64))
          .skip)
        (.decCall (ofString "h") .one (ofString "rlp_header_len") [.var .local (ofString "n")]
          (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [
        .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
        .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))]) =
      some (.val (.word (if nw.toNat = 1 ∧ fbw.toNat < 128 then 1 else 0))) := by
    by_cases hn1 : nw = 1#64 <;> by_cases hfb128 : fbw < 128#64
    · subst hn1
      have hfb_lt : fbw.toNat < 128 := by simpa [BitVec.lt_def] using hfb128
      simp [evalHOLExact, evalListHOLExact, hn, hfb, hfb128, hfb_lt,
        Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
    · subst hn1
      have hfb_nlt : ¬ fbw.toNat < 128 := by simpa [BitVec.lt_def] using hfb128
      simp [evalHOLExact, evalListHOLExact, hn, hfb, hfb128, hfb_nlt,
        Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
    · have hn1_nat : nw.toNat ≠ 1 := fun h => hn1 (BitVec.eq_of_toNat_eq h)
      simp [evalHOLExact, evalListHOLExact, hn, hfb, hn1, hn1_nat, hfb128,
        Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
    · have hn1_nat : nw.toNat ≠ 1 := fun h => hn1 (BitVec.eq_of_toNat_eq h)
      simp [evalHOLExact, evalListHOLExact, hn, hfb, hn1, hn1_nat, hfb128,
        Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hcond] at hret; dsimp only at hret
  by_cases hshort : nw.toNat = 1 ∧ fbw.toNat < 128
  · rw [if_pos hshort, if_neg h10, evaluateHOLFiniteState_return] at hret
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte] at hret
    injection hret with hr; injection hr with hv_eq; subst hv_eq
    exact ⟨1, rfl, by simp [rlpBytesLenPure, hshort]⟩
  · rw [if_neg hshort] at hret
    rw [if_pos rfl, evaluateHOLFiniteState_skip] at hret
    dsimp only at hret
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
    have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "n")] = some [.val (.word nw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
    have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_header_len") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_header_len) nw
      (by rw [hc]; exact lookup_rlp_header_len)
    simp only [hargs, hlk] at hret
    by_cases hclk0 : s.clock = 0
    · simp [hclk0] at hret
    · simp only [hclk0, ↓reduceIte] at hret
      set entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw)))
      have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rc, sc⟩
      simp only [hcal] at hret
      cases rc with
      | none => simp at hret
      | some rc' =>
        cases rc' with
        | returned vc =>
          have hnt_hl : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 ≠
              some .timeOut := by rw [hcal]; simp
          obtain ⟨hret_hl, _⟩ := eval_rlp_header_len_body_exact entry nw hc hent_n hnt_hl
          rw [hcal] at hret_hl; dsimp only at hret_hl
          injection hret_hl with h1; injection h1 with hvc; subst hvc
          set hlw := BitVec.ofNat 64 (rlpHeaderLenPure nw.toNat)
          have hbds := rlpHeaderLenPure_bounds nw.toNat
          have hhl_eq : hlw.toNat = rlpHeaderLenPure nw.toNat := by
            dsimp [hlw]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hlw) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word hlw) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          simp only [hsh, ↓reduceIte] at hret
          let resSt := setVarHOLFinite (ofString "h") (.val (.word hlw)) { sc with locals := s.locals }
          rw [evaluateHOLFiniteState_return] at hret
          have hev_add : @evalHOLExact 64 F _ resSt.toExact (fun a => Classical.propDecidable (resSt.memaddrs a))
              (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
              some (.val (.word (hlw + nw))) := by
            have hne : ofString "h" ≠ ofString "n" := by decide
            simp [resSt, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              hne, Ne.symm hne, hn, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
          have hsz : sizeOfShapeWithContextHOL resSt.structs
              (shapeOfHOLExact (.val (.word (hlw + nw)) : ValueHOL 64)) ≤ 32 := by simp [shapeOfHOLExact]
          rw [hev_add] at hret; dsimp only at hret; rw [if_pos hsz] at hret
          injection hret with hr; injection hr with hr'; subst hr'
          have hsum : (hlw + nw).toNat = rlpHeaderLenPure nw.toNat + nw.toNat := by
            rw [BitVec.toNat_add, hhl_eq]; omega
          exact ⟨hlw + nw, rfl, by simp [rlpBytesLenPure, hshort, hsum]⟩
        | _ => simp at hret

private theorem eval_loadByte_memB_of_some {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {src0 b0 : BitVec 64}
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word src0)))
    (hlb : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.loadByte e) =
      some (.val (.word b0))) :
    s.memaddrs (panByteAlignHOL src0) ∧ b0.toNat = memB s src0.toNat := by
  simp only [evalHOLExact, hsrc] at hlb
  unfold panMemLoadByteHOL at hlb; dsimp only at hlb
  have hbv : BitVec.ofNat 64 src0.toNat = src0 :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt src0.isLt])
  cases hm : s.memory (panByteAlignHOL src0) with
  | word cell =>
    simp only [hm] at hlb
    split at hlb
    · rename_i hdom
      simp only [Option.map, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hlb
      refine ⟨hdom, ?_⟩
      unfold memB
      rw [hbv, hm, ← hlb]
      simp [UInt8.toBitVec]
    · simp at hlb

private theorem eval_rlp_value_encoded_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (pw nw : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).1 =
      some (.returned v)) :
    ∃ vl : BitVec 64,
      v = .val (.word vl) ∧
      vl.toNat = rlpBytesLenPure (if 0 < nw.toNat then memB s pw.toNat else 0) nw.toNat ∧
      (0 < nw.toNat → s.memaddrs (panByteAlignHOL pw)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len =
      .dec (ofString "fb") .one (.const 0)
        (.seq
          (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
            (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
            .skip)
          (.call none (ofString "rlp_bytes_encoded_len")
            [.var .local (ofString "fb"), .var .local (ofString "n")])) := rfl
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  rw [hb, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [hev0] at hret; dsimp only at hret; rw [if_pos hsh0] at hret; dsimp only at hret
  let s1 := setVarHOLFinite (ofString "fb") (.val (.word 0)) s
  have hs1_p : s1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
      show ofString "fb" ≠ ofString "p" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "fb" ≠ ofString "n" by decide]
  have hs1_fb : s1.locals.lookup (ofString "fb") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .lower (.const 0) (.var .local (ofString "n"))) =
      some (.val (.word (if 0 < nw.toNat then 1 else 0))) := by
    simp [evalHOLExact, hs1_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
  rw [hcmp] at hret; dsimp only at hret
  have hcall : ∀ (si : PanSemStateFiniteExact 64 F) (fbw : BitVec 64),
      si.code = originalRuntimeCode →
      si.locals.lookup (ofString "fb") = some (.val (.word fbw)) →
      si.locals.lookup (ofString "n") = some (.val (.word nw)) →
      (evaluateHOLFiniteState si
        (.call none (ofString "rlp_bytes_encoded_len")
          [.var .local (ofString "fb"), .var .local (ofString "n")])).1 = some (.returned v) →
      ∃ vl : BitVec 64, v = .val (.word vl) ∧ vl.toNat = rlpBytesLenPure fbw.toNat nw.toNat := by
    intro si fbw hsi_c hsi_fb hsi_n hrc
    rw [evaluateHOLFiniteState_call] at hrc
    have ha : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
        [.var .local (ofString "fb"), .var .local (ofString "n")] =
        some [.val (.word fbw), .val (.word nw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsi_fb, hsi_n]
    have hlk := pan_two_word_lookup si.code.lookup (ofString "rlp_bytes_encoded_len")
      (ofString "first_byte") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) fbw nw
      (by decide) (by rw [hsi_c]; exact lookup_rlp_bytes_encoded_len)
    simp only [ha, hlk] at hrc
    by_cases hcz : si.clock = 0
    · simp [hcz] at hrc
    · simp only [hcz, ↓reduceIte] at hrc
      let cmap := (HolFiniteMapExact.empty.update (ofString "first_byte", ValueHOL.val (.word fbw))).update
        (ofString "n", ValueHOL.val (.word nw))
      let ent := callEntryStateHOLFinite si cmap
      have hent_fb : ent.locals.lookup (ofString "first_byte") = some (.val (.word fbw)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "first_byte" by decide]
      have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hcal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) with ⟨rc, sc⟩
      have hcal' : evaluateHOLFiniteState (callEntryStateHOLFinite si cmap)
          (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) = (rc, sc) := hcal
      rw [hcal'] at hrc
      cases rc with
      | none => simp at hrc
      | some r0 =>
        cases r0 with
        | returned vc =>
          obtain ⟨vl, rfl, hvl_eq⟩ :=
            eval_rlp_bytes_encoded_len_exact ent hsi_c fbw nw hent_fb hent_n hnw60 vc (by rw [hcal])
          have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word vl) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          simp only [hsh, ↓reduceIte] at hrc
          injection hrc with hr; injection hr with hr'; subst hr'
          exact ⟨vl, rfl, hvl_eq⟩
        | _ => simp at hrc
  by_cases hn_pos : 0 < nw.toNat
  · rw [if_pos hn_pos, if_neg h10, evaluateHOLFiniteState_assign] at hret
    rcases hlb : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.loadByte (.var .local (ofString "p"))) with _ | bv
    · rw [hlb] at hret; simp at hret
    · have hbv_w : ∃ fbw : BitVec 64, bv = .val (.word fbw) := by
        simp only [evalHOLExact, hs1_p] at hlb
        unfold panMemLoadByteHOL at hlb; dsimp only at hlb
        cases hm : s1.memory (panByteAlignHOL pw) with
        | word cell =>
          simp only [hm] at hlb
          split at hlb
          · simp only [Option.map, Option.some.injEq] at hlb; exact ⟨_, hlb.symm⟩
          · simp at hlb
      obtain ⟨fbw, rfl⟩ := hbv_w
      obtain ⟨hdom, hfb_memB⟩ := eval_loadByte_memB_of_some (s := s1) (src0 := pw) (by simp [evalHOLExact, hs1_p]) hlb
      have hvalid : s1.isValidValueHOLFinite VarKind.local (ofString "fb") (.val (.word fbw)) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs1_fb,
          shapeOfHOLExact, shapeEqHOL]
      rw [hlb] at hret; dsimp only at hret; rw [if_pos hvalid] at hret; dsimp only [setKvarHOLFinite] at hret
      let si := setVarHOLFinite (ofString "fb") (.val (.word fbw)) s1
      have hsi_fb : si.locals.lookup (ofString "fb") = some (.val (.word fbw)) := by
        simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsi_n : si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_n,
          show ofString "fb" ≠ ofString "n" by decide]
      obtain ⟨vl, rfl, hvl_eq⟩ := hcall si fbw hc hsi_fb hsi_n hret
      refine ⟨vl, rfl, ?_, fun _ => hdom⟩
      have hmemB_s1 : memB s1 pw.toNat = memB s pw.toNat := rfl
      rw [if_pos hn_pos, ← hmemB_s1, ← hfb_memB]; exact hvl_eq
  · rw [if_neg hn_pos] at hret
    rw [if_pos rfl, evaluateHOLFiniteState_skip] at hret
    dsimp only at hret
    obtain ⟨vl, rfl, hvl_eq⟩ := hcall s1 0 hc hs1_fb hs1_n hret
    refine ⟨vl, rfl, ?_, fun h => absurd h hn_pos⟩
    rw [if_neg hn_pos]; exact hvl_eq

private theorem eval_rlp_bytes_encoded_len_noExn {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (fbw nw : BitVec 64)
    (hfb : s.locals.lookup (ofString "first_byte") = some (.val (.word fbw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (eid : MlS) (ev : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).1 ≠
      some (.exception eid ev) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len =
      .seq
        (.ite (.op .and [
            .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
            .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))])
          (.return (.const 1#64))
          .skip)
        (.decCall (ofString "h") .one (ofString "rlp_header_len") [.var .local (ofString "n")]
          (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [
        .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
        .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))]) =
      some (.val (.word (if nw.toNat = 1 ∧ fbw.toNat < 128 then 1 else 0))) := by
    by_cases hn1 : nw = 1#64 <;> by_cases hfb128 : fbw < 128#64
    · subst hn1
      have hfb_lt : fbw.toNat < 128 := by simpa [BitVec.lt_def] using hfb128
      simp [evalHOLExact, evalListHOLExact, hn, hfb, hfb128, hfb_lt,
        Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
    · subst hn1
      have hfb_nlt : ¬ fbw.toNat < 128 := by simpa [BitVec.lt_def] using hfb128
      simp [evalHOLExact, evalListHOLExact, hn, hfb, hfb128, hfb_nlt,
        Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
    · have hn1_nat : nw.toNat ≠ 1 := fun h => hn1 (BitVec.eq_of_toNat_eq h)
      simp [evalHOLExact, evalListHOLExact, hn, hfb, hn1, hn1_nat, hfb128,
        Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
    · have hn1_nat : nw.toNat ≠ 1 := fun h => hn1 (BitVec.eq_of_toNat_eq h)
      simp [evalHOLExact, evalListHOLExact, hn, hfb, hn1, hn1_nat, hfb128,
        Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hcond]; dsimp only
  by_cases hshort : nw.toNat = 1 ∧ fbw.toNat < 128
  · rw [if_pos hshort, if_neg h10, evaluateHOLFiniteState_return]
    simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  · rw [if_neg hshort]
    rw [if_pos rfl, evaluateHOLFiniteState_skip]; dsimp only
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "n")] = some [.val (.word nw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
    have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_header_len") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_header_len) nw
      (by rw [hc]; exact lookup_rlp_header_len)
    simp only [hargs, hlk]
    by_cases hclk0 : s.clock = 0
    · simp [hclk0]
    · simp only [hclk0, ↓reduceIte]
      set entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw)))
      have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rc, sc⟩
      simp only [hcal]
      cases rc with
      | none => simp
      | some rc' =>
        cases rc' with
        | timeOut => simp
        | exception eid' ev' =>
          have hnt_hl : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 ≠
              some .timeOut := by rw [hcal]; simp
          obtain ⟨hret_hl, _⟩ := eval_rlp_header_len_body_exact entry nw hc hent_n hnt_hl
          rw [hcal] at hret_hl; simp at hret_hl
        | returned vc =>
          dsimp only
          split
          · rw [evaluateHOLFiniteState_return]
            split
            · simp
            · split <;> simp
          · simp
        | «break» | «continue» | error | finalFfi _ => simp

private theorem eval_rlp_value_encoded_len_noExn {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (pw nw : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (eid : MlS) (ev : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).1 ≠
      some (.exception eid ev) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len =
      .dec (ofString "fb") .one (.const 0)
        (.seq
          (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
            (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
            .skip)
          (.call none (ofString "rlp_bytes_encoded_len")
            [.var .local (ofString "fb"), .var .local (ofString "n")])) := rfl
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  rw [hb, evaluateHOLFiniteState_dec_total]; dsimp only
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [hev0]; dsimp only; rw [if_pos hsh0]
  intro hex
  dsimp only at hex
  let s1 := setVarHOLFinite (ofString "fb") (.val (.word 0)) s
  have hs1_p : s1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
      show ofString "fb" ≠ ofString "p" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "fb" ≠ ofString "n" by decide]
  have hs1_fb : s1.locals.lookup (ofString "fb") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hex
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .lower (.const 0) (.var .local (ofString "n"))) =
      some (.val (.word (if 0 < nw.toNat then 1 else 0))) := by
    simp [evalHOLExact, hs1_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
  rw [hcmp] at hex; dsimp only at hex
  have hcall : ∀ (si : PanSemStateFiniteExact 64 F) (fbw : BitVec 64),
      si.code = originalRuntimeCode →
      si.locals.lookup (ofString "fb") = some (.val (.word fbw)) →
      si.locals.lookup (ofString "n") = some (.val (.word nw)) →
      (evaluateHOLFiniteState si
        (.call none (ofString "rlp_bytes_encoded_len")
          [.var .local (ofString "fb"), .var .local (ofString "n")])).1 ≠ some (.exception eid ev) := by
    intro si fbw hsi_c hsi_fb hsi_n hrc
    rw [evaluateHOLFiniteState_call] at hrc
    have ha : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
        [.var .local (ofString "fb"), .var .local (ofString "n")] =
        some [.val (.word fbw), .val (.word nw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsi_fb, hsi_n]
    have hlk := pan_two_word_lookup si.code.lookup (ofString "rlp_bytes_encoded_len")
      (ofString "first_byte") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) fbw nw
      (by decide) (by rw [hsi_c]; exact lookup_rlp_bytes_encoded_len)
    simp only [ha, hlk] at hrc
    by_cases hcz : si.clock = 0
    · simp [hcz] at hrc
    · simp only [hcz, ↓reduceIte] at hrc
      let cmap := (HolFiniteMapExact.empty.update (ofString "first_byte", ValueHOL.val (.word fbw))).update
        (ofString "n", ValueHOL.val (.word nw))
      let ent := callEntryStateHOLFinite si cmap
      have hent_fb : ent.locals.lookup (ofString "first_byte") = some (.val (.word fbw)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "first_byte" by decide]
      have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hno := eval_rlp_bytes_encoded_len_noExn ent hsi_c fbw nw hent_fb hent_n eid ev
      rcases hcal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) with ⟨rc, sc⟩
      have hcal' : evaluateHOLFiniteState (callEntryStateHOLFinite si cmap)
          (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) = (rc, sc) := hcal
      rw [hcal] at hno; rw [hcal'] at hrc
      cases rc with
      | none => simp at hrc
      | some r0 =>
        cases r0 with
        | exception eid' ev' =>
          dsimp only at hrc
          injection hrc with h1; injection h1 with he1 he2; subst he1; subst he2
          exact hno rfl
        | returned vc => dsimp only at hrc; split at hrc <;> simp at hrc
        | _ => simp at hrc
  by_cases hn_pos : 0 < nw.toNat
  · rw [if_pos hn_pos, if_neg h10, evaluateHOLFiniteState_assign] at hex
    rcases hlb : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.loadByte (.var .local (ofString "p"))) with _ | bv
    · rw [hlb] at hex; simp at hex
    · have hbv_w : ∃ fbw : BitVec 64, bv = .val (.word fbw) := by
        simp only [evalHOLExact, hs1_p] at hlb
        unfold panMemLoadByteHOL at hlb; dsimp only at hlb
        cases hm : s1.memory (panByteAlignHOL pw) with
        | word cell =>
          simp only [hm] at hlb
          split at hlb
          · simp only [Option.map, Option.some.injEq] at hlb; exact ⟨_, hlb.symm⟩
          · simp at hlb
      obtain ⟨fbw, rfl⟩ := hbv_w
      have hvalid : s1.isValidValueHOLFinite VarKind.local (ofString "fb") (.val (.word fbw)) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs1_fb,
          shapeOfHOLExact, shapeEqHOL]
      rw [hlb] at hex; dsimp only at hex; rw [if_pos hvalid] at hex; dsimp only [setKvarHOLFinite] at hex
      let si := setVarHOLFinite (ofString "fb") (.val (.word fbw)) s1
      have hsi_fb : si.locals.lookup (ofString "fb") = some (.val (.word fbw)) := by
        simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsi_n : si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_n,
          show ofString "fb" ≠ ofString "n" by decide]
      exact hcall si fbw hc hsi_fb hsi_n hex
  · rw [if_neg hn_pos] at hex
    rw [if_pos rfl, evaluateHOLFiniteState_skip] at hex; dsimp only at hex
    exact hcall s1 0 hc hs1_fb hs1_n hex

private theorem storeByte_local_dst_lt_heapEnd_local {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst0 : BitVec 64) (val : ExpHOL 64)
    (hma : t.memaddrs = ordinaryDomain)
    (hdst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hnone : (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = none) :
    dst0.toNat < heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  simp only [evalHOLExact, hdst] at hnone
  split at hnone
  · split at hnone
    · rename_i m' hst
      unfold panMemStoreByteWord8HOL at hst; dsimp only at hst
      cases hm : t.memory (panByteAlignHOL dst0) with
      | word cell =>
        by_cases hdom : t.memaddrs (panByteAlignHOL dst0)
        · exact (M11.byteAlign_lt_heapEnd hma dst0 hdom).2
        · simp [hm, hdom] at hst
    · simp at hnone
  · simp at hnone

private theorem eval_decCall_rlp_bytes_encoded_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (fbExp nExp : ExpHOL 64)
    (fbw nw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hfb_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) fbExp =
      some (.val (.word fbw)))
    (hn_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_bytes_encoded_len") [fbExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_bytes_encoded_len") [fbExp, nExp] cont)).1 ∨
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_bytes_encoded_len") [fbExp, nExp] cont)).1 = none) :
    ∃ (el : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      el.toNat = rlpBytesLenPure fbw.toNat nw.toNat ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word el)) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_bytes_encoded_len") [fbExp, nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [fbExp, nExp] = some [.val (.word fbw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hfb_ev, hn_ev]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_bytes_encoded_len")
    (ofString "first_byte") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) fbw nw
    (by decide) (by rw [hc]; exact lookup_rlp_bytes_encoded_len)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "first_byte", ValueHOL.val (.word fbw))).update
      (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_fb : ent.locals.lookup (ofString "first_byte") = some (.val (.word fbw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "first_byte" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) rfl ent hc
    rcases hcal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) with ⟨rc, sc⟩
    rw [hcal] at hro; dsimp only at hro
    simp only [hcal] at hnt hres ⊢
    cases rc with
    | none =>
      rcases hres with hr | hn0
      · exact False.elim (not_resumes_error hr)
      · simp at hn0
    | some r0 =>
      cases r0 with
      | timeOut => exact absurd rfl hnt
      | exception eid ev =>
        exact False.elim (eval_rlp_bytes_encoded_len_noExn ent hc fbw nw hent_fb hent_n eid ev (by rw [hcal]))
      | returned vc =>
        obtain ⟨el, rfl, hel_eq⟩ :=
          eval_rlp_bytes_encoded_len_exact ent hc fbw nw hent_fb hent_n hnw60 vc (by rw [hcal])
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word el) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word el) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnt ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word el)) { sc with locals := s.locals }
        have hmid_g : mid.globals = s.globals := by change sc.globals = s.globals; rw [hro]; rfl
        have hmid_m : mid.memory = s.memory := by change sc.memory = s.memory; rw [hro]; rfl
        have heff : R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw := by
          have hsc_eq : mid = { s with locals := mid.locals, clock := mid.clock } := by
            dsimp [mid, setVarHOLFinite]; rw [hro]; cases s; rfl
          rw [hsc_eq]
          exact (R16Shards.WkBlockTxEnc.HeapByteEff.refl hAR Rl gw).locals_clock _ _
        exact ⟨el, mid, hel_eq, hmid_g, hmid_m, rfl, heff, hnt, rfl⟩
      | «break» | «continue» | error =>
        rcases hres with hr | hn0
        · exact False.elim (not_resumes_error hr)
        · simp at hn0
      | finalFfi _ =>
        rcases hres with hr | hn0
        · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        · simp at hn0

private theorem eval_decCall_rlp_value_encoded_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (pExp nExp : ExpHOL 64)
    (pw nw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hn_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_value_encoded_len") [pExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_value_encoded_len") [pExp, nExp] cont)).1 ∨
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_value_encoded_len") [pExp, nExp] cont)).1 = none) :
    ∃ (vl : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      vl.toNat = rlpBytesLenPure (if 0 < nw.toNat then memB s pw.toNat else 0) nw.toNat ∧
      (0 < nw.toNat → s.memaddrs (panByteAlignHOL pw)) ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word vl)) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_value_encoded_len") [pExp, nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [pExp, nExp] = some [.val (.word pw), .val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hp_ev, hn_ev]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_value_encoded_len")
    (ofString "p") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len) pw nw
    (by decide) (by rw [hc]; exact lookup_rlp_value_encoded_len)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "p", ValueHOL.val (.word pw))).update
      (ofString "n", ValueHOL.val (.word nw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_p : ent.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "p" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len) rfl ent hc
    rcases hcal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len) with ⟨rc, sc⟩
    rw [hcal] at hro; dsimp only at hro
    simp only [hcal] at hnt hres ⊢
    cases rc with
    | none =>
      rcases hres with hr | hn0
      · exact False.elim (not_resumes_error hr)
      · simp at hn0
    | some r0 =>
      cases r0 with
      | timeOut => exact absurd rfl hnt
      | exception eid ev =>
        exact False.elim (eval_rlp_value_encoded_len_noExn ent hc pw nw hent_p hent_n eid ev (by rw [hcal]))
      | returned vc =>
        obtain ⟨vl, rfl, hvl_eq, hdom⟩ :=
          eval_rlp_value_encoded_len_exact ent hc pw nw hent_p hent_n hnw60 vc (by rw [hcal])
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word vl) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word vl) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnt ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word vl)) { sc with locals := s.locals }
        have hmid_g : mid.globals = s.globals := by change sc.globals = s.globals; rw [hro]; rfl
        have hmid_m : mid.memory = s.memory := by change sc.memory = s.memory; rw [hro]; rfl
        have heff : R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw := by
          have hsc_eq : mid = { s with locals := mid.locals, clock := mid.clock } := by
            dsimp [mid, setVarHOLFinite]; rw [hro]; cases s; rfl
          rw [hsc_eq]
          exact (R16Shards.WkBlockTxEnc.HeapByteEff.refl hAR Rl gw).locals_clock _ _
        exact ⟨vl, mid, hvl_eq, hdom, hmid_g, hmid_m, rfl, heff, hnt, rfl⟩
      | «break» | «continue» | error =>
        rcases hres with hr | hn0
        · exact False.elim (not_resumes_error hr)
        · simp at hn0
      | finalFfi _ =>
        rcases hres with hr | hn0
        · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        · simp at hn0

private theorem eval_decCall_node_ref_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (lname : String)
    (childExp : ExpHOL 64) (child0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hN : NodeHeap s Nd)
    (hchild_in : RootIn Nd child0.toNat)
    (hchild_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) childExp =
      some (.val (.word child0)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "node_ref_len") [childExp] cont)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "node_ref_len") [childExp] cont)
    (∃ (rl : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      rl.toNat = nodeRefBytes s child0.toNat ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word rl)) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      out = ((evaluateHOLFiniteState mid cont).1,
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) })) ∨
      (out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) ∧
        out.1 ≠ some .break ∧ out.1 ≠ some .continue ∧
        out.2 = { s with locals := out.2.locals, clock := out.2.clock }) := by
  intro out; dsimp only [out]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [childExp] = some [.val (.word child0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hchild_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "node_ref_len") (ofString "child")
    (sourceFnBody Guest.Software.guestFn_node_ref_len) child0
    (by rw [hc]; exact lookup_node_ref_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "child", ValueHOL.val (.word child0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_child : ent.locals.lookup (ofString "child") = some (.val (.word child0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_node_ref_len) rfl ent hc
    rcases hcal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_node_ref_len) with ⟨rc, sc⟩
    rw [hcal] at hro; dsimp only at hro
    simp only [hcal] at hnt ⊢
    cases rc with
    | none =>
      right
      exact ⟨by simp, fun _ => by simp, by simp, by simp, by dsimp [emptyLocalsHOLFinite]; rw [hro]; cases s; rfl⟩
    | some r0 =>
      cases r0 with
      | timeOut => exact absurd rfl hnt
      | returned vc =>
        obtain ⟨rl, rfl, hrl_eq, _⟩ :=
          eval_node_ref_len_exact ent Nd child0 vc hc hN hchild_in hent_child (by rw [hcal])
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word rl) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word rl) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnt ⊢
        left
        let mid := setVarHOLFinite (ofString lname) (.val (.word rl)) { sc with locals := s.locals }
        have hmid_g : mid.globals = s.globals := by change sc.globals = s.globals; rw [hro]; rfl
        have hmid_m : mid.memory = s.memory := by change sc.memory = s.memory; rw [hro]; rfl
        have heff : R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw := by
          have hsc_eq : mid = { s with locals := mid.locals, clock := mid.clock } := by
            dsimp [mid, setVarHOLFinite]; rw [hro]; cases s; rfl
          rw [hsc_eq]
          exact (R16Shards.WkBlockTxEnc.HeapByteEff.refl hAR Rl gw).locals_clock _ _
        exact ⟨rl, mid, hrl_eq, hmid_g, hmid_m, rfl, heff, hnt, rfl⟩
      | exception eid ev =>
        right
        exact ⟨by simp, fun _ => by simp, by simp, by simp, by dsimp [emptyLocalsHOLFinite]; rw [hro]; cases s; rfl⟩
      | «break» | «continue» | error | finalFfi _ =>
        right
        exact ⟨by simp, fun _ => by simp, by simp, by simp, by dsimp [emptyLocalsHOLFinite]; rw [hro]; cases s; rfl⟩

private theorem eval_rlp_encode_bytes_body_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hn60 : n0.toNat < 2 ^ 60)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpBytesLenPure (if 0 < n0.toNat then memB s src0.toNat else 0) n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
    (∀ rv, out.1 = some (.returned rv) →
      ∃ len : BitVec 64, rv = .val (.word len) ∧
        len.toNat = rlpBytesLenPure (if 0 < n0.toNat then memB s src0.toNat else 0) n0.toNat ∧
        dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s out.2 Rl) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_bytes =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 1))
          (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
            (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
              (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) (.return (.const 1)))
              .skip))
          .skip)
        (.decCall (ofString "h") .one (ofString "rlp_write_header")
          [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"),
               .var .local (ofString "n")])
            (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))) := rfl
  dsimp only
  rw [hb] at hnt ⊢
  let tailP : ProgHOL 64 :=
    .decCall (ofString "h") .one (ofString "rlp_write_header")
      [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
           .var .local (ofString "src"),
           .var .local (ofString "n")])
        (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))
  have htail : ∀ (t : PanSemStateFiniteExact 64 F),
      M11.ByteRegionEffect s t Rl →
      t.locals = s.locals →
      ¬ (n0.toNat = 1 ∧ (if 0 < n0.toNat then memB s src0.toNat else 0) < 128) →
      (evaluateHOLFiniteState t tailP).1 ≠ some .timeOut →
      (∀ rv, (evaluateHOLFiniteState t tailP).1 = some (.returned rv) →
        ∃ len : BitVec 64, rv = .val (.word len) ∧
          len.toNat = rlpBytesLenPure (if 0 < n0.toNat then memB s src0.toNat else 0) n0.toNat ∧
          dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s (evaluateHOLFiniteState t tailP).2 Rl) ∧
      (∀ r, (evaluateHOLFiniteState t tailP).1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
    intro t heff_t ht_loc hnot_short hnt_t
    have hlen_eq : rlpBytesLenPure (if 0 < n0.toNat then memB s src0.toNat else 0) n0.toNat =
        rlpHeaderLenPure n0.toNat + n0.toNat := by
      unfold rlpBytesLenPure; rw [if_neg hnot_short]
    have ht_code : t.code = originalRuntimeCode := heff_t.code.trans hcode
    have ht_ma : t.memaddrs = ordinaryDomain := heff_t.memaddrs.trans hma
    have ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [ht_loc]; exact hdst
    have ht_src : t.locals.lookup (ofString "src") = some (.val (.word src0)) := by rw [ht_loc]; exact hsrc
    have ht_n : t.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [ht_loc]; exact hn
    dsimp only [tailP] at hnt_t ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_t ⊢
    have ha : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")] =
        some [.val (.word dst0), .val (.word 128), .val (.word n0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht_dst, ht_n]
    have hlk := pan_three_word_lookup t.code.lookup (ofString "rlp_write_header")
      (ofString "dst") (ofString "base") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 128 n0
      (by decide) (by decide) (by decide)
      (by rw [ht_code]; exact M11.lookup_rlp_write_header)
    simp only [ha, hlk] at hnt_t ⊢
    by_cases hcz : t.clock = 0
    · simp [hcz] at hnt_t
    · simp only [hcz, ↓reduceIte] at hnt_t ⊢
      set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "base", ValueHOL.val (.word 128))).update (ofString "n", ValueHOL.val (.word n0))
      set ent := callEntryStateHOLFinite t cmap
      have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide, show ofString "base" ≠ ofString "dst" by decide]
      have hent_base : ent.locals.lookup (ofString "base") = some (.val (.word 128)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "base" by decide]
      have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hwh : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rwh, swh⟩
      have hnt_wh : rwh ≠ some .timeOut := by
        rintro rfl; rw [hwh] at hnt_t; exact hnt_t rfl
      obtain ⟨hret_wh, hnonret_wh⟩ := R16Shards.WkBlockTxEnc.eval_rlp_write_header_body_exact ent dst0 128 n0 Rl
        ht_code ht_ma hent_dst hent_base hent_n
        (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; rw [hlen_eq] at h2; exact ⟨ivl, hivl, h1, by omega⟩)
        (by rw [hwh]; exact hnt_wh)
      rw [hwh] at hret_wh hnonret_wh
      dsimp only at hret_wh hnonret_wh
      simp only [hwh] at hnt_t ⊢
      cases rwh with
      | none => exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact R16Shards.WkBlockTxEnc.not_resumes_error⟩
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_wh
        | exception eid ev =>
          refine ⟨fun _ h => by simp at h, fun r' hr' _ => ?_⟩
          injection hr' with hr''; subst hr''
          exact hnonret_wh (.exception eid ev) rfl (fun _ h => by cases h)
        | returned rv =>
          obtain ⟨rfl, hdst_lt, heff_wh⟩ := hret_wh rv rfl
          set h := BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat)
          have hbnd := rlpHeaderLenPure_bounds n0.toNat
          have hh_nat : h.toNat = rlpHeaderLenPure n0.toNat := by
            dsimp [h]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          dsimp only at hnt_t ⊢; rw [if_pos hsh] at hnt_t ⊢; dsimp only at hnt_t ⊢
          set mid := setVarHOLFinite (ofString "h") (.val (.word h)) { swh with locals := t.locals }
          have heff_t_mid : M11.ByteRegionEffect t mid Rl :=
            ((M11.ByteRegionEffect.refl t Rl |>.with_locals_clock ent.locals ent.clock).trans heff_wh).with_locals_clock mid.locals mid.clock
          have hmid_code : mid.code = originalRuntimeCode := heff_t_mid.code.trans ht_code
          have hmid_ma : mid.memaddrs = ordinaryDomain := heff_t_mid.memaddrs.trans ht_ma
          have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word h)) := by
            simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_dst,
              show ofString "h" ≠ ofString "dst" by decide]
          have hmid_src : mid.locals.lookup (ofString "src") = some (.val (.word src0)) := by
            simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_src,
              show ofString "h" ≠ ofString "src" by decide]
          have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
            simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_n,
              show ofString "h" ≠ ofString "n" by decide]
          have hdsth_nat : (dst0 + h).toNat = dst0.toNat + h.toNat := by
            have hhe := hdst_lt; rw [R16Shards.WkBlockTxEnc.heapEnd_val] at hhe
            rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
          rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
          rcases hc_mc : evaluateHOLFiniteState mid
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"),
               .var .local (ofString "n")]) with ⟨rmc, smc⟩
          have hnt_mc : rmc ≠ some .timeOut := by
            rintro rfl; rw [hc_mc] at hnt_t; exact hnt_t rfl
          have hmc := M11.eval_call_memcpy_bre_gen mid
            (.op .add [.var .local (ofString "dst"), .var .local (ofString "h")])
            (.var .local (ofString "src"))
            (.var .local (ofString "n"))
            (dst0 + h) src0 n0 Rl hmid_code hmid_ma
            (by simp [evalHOLExact, evalListHOLExact, hmid_dst, hmid_h, wordOpHOL, wordOp, valueIsWord, valueWord])
            (by simp [evalHOLExact, hmid_src])
            (by simp [evalHOLExact, hmid_n])
            (fun off hoff _ => by
              obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; rw [hlen_eq] at h2
              exact ⟨ivl, hivl, by rw [hdsth_nat, hh_nat]; omega, by rw [hdsth_nat, hh_nat]; omega⟩)
            (fun off hoff _ => by
              obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; rw [hlen_eq] at h2
              exact ⟨ivl, hivl, by rw [hdsth_nat, hh_nat]; omega, by rw [hdsth_nat, hh_nat]; omega⟩)
            (by rw [hc_mc]; exact hnt_mc)
          dsimp only at hmc; rw [hc_mc] at hmc; simp only [hc_mc] at hnt_t ⊢
          cases rmc with
          | some r' =>
            dsimp only
            have hnr := hmc.2 (by simp)
            refine ⟨fun rv' hrv' => False.elim (hnr (Or.inl ⟨rv', hrv'⟩)), fun r'' hr'' _ => ?_⟩
            injection hr'' with hr'''; subst hr'''; exact hnr
          | none =>
            dsimp only at hnt_t ⊢
            obtain ⟨heff_mc, hsmc_loc⟩ := hmc.1 rfl
            have hsmc_h : smc.locals.lookup (ofString "h") = some (.val (.word h)) := by
              rw [hsmc_loc]; exact hmid_h
            have hsmc_n : smc.locals.lookup (ofString "n") = some (.val (.word n0)) := by
              rw [hsmc_loc]; exact hmid_n
            rw [evaluateHOLFiniteState_return]
            have hev_ret : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
                some (.val (.word (h + n0))) := by
              simp [evalHOLExact, evalListHOLExact, hsmc_h, hsmc_n, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_ret]; dsimp only
            have hsz : sizeOfShapeWithContextHOL smc.structs (shapeOfHOLExact (.val (.word (h + n0)) : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz]; dsimp only
            have hhn_eq : (h + n0).toNat = rlpBytesLenPure (if 0 < n0.toNat then memB s src0.toNat else 0) n0.toNat := by
              rw [hlen_eq, BitVec.toNat_add, hh_nat, Nat.mod_eq_of_lt (by omega)]
            refine ⟨fun rv' hrv' => ?_, fun r' hr' hnr => ?_⟩
            · injection hrv' with h1; injection h1 with h2
              exact ⟨h + n0, h2.symm, hhn_eq, hdst_lt,
                (((heff_t.trans heff_t_mid).trans heff_mc).with_locals_clock _ _).with_locals_clock _ _⟩
            · injection hr' with hr''; subst hr''; exact absurd rfl (hnr _)
        | «break» | «continue» | error =>
          dsimp only
          exact ⟨fun _ h => by simp at h, fun r' hr' _ => by injection hr' with hr''; subst hr''; exact R16Shards.WkBlockTxEnc.not_resumes_error⟩
        | finalFfi _ =>
          dsimp only
          exact ⟨fun _ h => by simp at h, fun r' hr' _ hr => by
            injection hr' with hr''; subst hr''
            rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hev_n1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "n")) (.const 1)) =
      some (.val (.word (if n0 = 1 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hev_n1] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases hn1 : n0 = 1
  · have hn1_nat : n0.toNat = 1 := by subst hn1; rfl
    have hn_pos : 0 < n0.toNat := by omega
    rw [if_pos hn1, if_neg h10, evaluateHOLFiniteState_dec_total] at hnt ⊢
    dsimp only at hnt ⊢
    rcases hlb : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.loadByte (.var .local (ofString "src"))) with _ | bv
    · simp only [hlb]
      exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact R16Shards.WkBlockTxEnc.not_resumes_error⟩
    · have hbv_w : ∃ b0 : BitVec 64, bv = .val (.word b0) := by
        simp only [evalHOLExact, hsrc] at hlb
        unfold panMemLoadByteHOL at hlb; dsimp only at hlb
        cases hm : s.memory (panByteAlignHOL src0) with
        | word cell =>
          simp only [hm] at hlb; split at hlb
          · simp only [Option.map, Option.some.injEq] at hlb; exact ⟨_, hlb.symm⟩
          · simp at hlb
      obtain ⟨b0, rfl⟩ := hbv_w
      obtain ⟨_, hb0_memB⟩ := eval_loadByte_memB_of_some (s := s) (src0 := src0) (by simp [evalHOLExact, hsrc]) hlb
      have hsh_b : shapeEqHOL .one (shapeOfHOLExact (.val (.word b0) : ValueHOL 64)) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      simp only [hlb] at hnt ⊢
      rw [if_pos hsh_b] at hnt ⊢
      set sb := setVarHOLFinite (ofString "b") (.val (.word b0)) s
      have hsb_b : sb.locals.lookup (ofString "b") = some (.val (.word b0)) := by
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsb_dst : sb.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
          show ofString "b" ≠ ofString "dst" by decide]
      rw [evaluateHOLFiniteState_ite] at hnt ⊢
      have hev_blt : @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a))
          (.cmp .lower (.var .local (ofString "b")) (.const 128)) =
          some (.val (.word (if b0 < 128 then 1 else 0))) := by
        simp [evalHOLExact, hsb_b, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev_blt] at hnt ⊢; dsimp only at hnt ⊢
      by_cases hblt : b0 < 128
      · have hblt_nat : b0.toNat < 128 := by simpa [BitVec.lt_def] using hblt
        have hlen1 : rlpBytesLenPure (if 0 < n0.toNat then memB s src0.toNat else 0) n0.toNat = 1 := by
          rw [if_pos hn_pos, ← hb0_memB]
          simp [rlpBytesLenPure, hn1_nat, hblt_nat]
        rw [if_pos hblt, if_neg h10, evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hst : evaluateHOLFiniteState sb
            (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) with ⟨rst, s1⟩
        simp only [hst] at hnt ⊢
        rcases storeByte_only_none_or_error_local sb (.var .local (ofString "dst")) (.var .local (ofString "b")) with hsn | hse
        · rw [hst] at hsn; dsimp only at hsn; subst hsn; dsimp only
          have hdst_lt := storeByte_local_dst_lt_heapEnd_local sb dst0 _ hma hsb_dst (by rw [hst])
          obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hst (fun addr hdst_ev _ => by
            simp only [evalHOLExact, hsb_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
            subst hdst_ev
            obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; rw [hlen1] at h2
            exact ⟨ivl, hivl, h1, by omega⟩)
          rw [evaluateHOLFiniteState_return]
          simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte]
          have heff_s_sb : M11.ByteRegionEffect s sb Rl :=
            (M11.ByteRegionEffect.refl s Rl).with_locals_clock sb.locals sb.clock
          refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
          · injection hrv with h1; injection h1 with h2
            exact ⟨1, h2.symm, hlen1.symm, hdst_lt,
              ((heff_s_sb.trans heff1).with_locals_clock _ _).with_locals_clock _ _⟩
          · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
        · rw [hst] at hse; dsimp only at hse; subst hse
          exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
      · have hblt_nat : ¬ b0.toNat < 128 := by simpa [BitVec.lt_def] using hblt
        rw [if_neg hblt, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
        dsimp only at hnt ⊢
        let s' : PanSemStateFiniteExact 64 F :=
          { sb with locals := HolFiniteMapExact.resVarEq sb.locals (ofString "b", s.locals.lookup (ofString "b")) }
        have hs'_loc : s'.locals = s.locals := by
          apply HolFiniteMapExact.ext; funext k
          change (HolFiniteMapExact.resVarEq sb.locals (ofString "b", s.locals.lookup (ofString "b"))).lookup k = s.locals.lookup k
          rw [PanRunBounded.resVarEq_lookup]
          by_cases hk : k = ofString "b"
          · subst hk; simp
          · simp [hk, sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        exact htail s' ((M11.ByteRegionEffect.refl s Rl).with_locals_clock s'.locals s'.clock) hs'_loc
          (by rw [if_pos hn_pos, ← hb0_memB]; rintro ⟨_, h⟩; exact hblt_nat h) hnt
  · have hn1_nat : n0.toNat ≠ 1 := fun h => hn1 (BitVec.eq_of_toNat_eq h)
    rw [if_neg hn1, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    exact htail s (M11.ByteRegionEffect.refl s Rl) rfl (fun ⟨h, _⟩ => hn1_nat h) hnt

private theorem eval_decCall_rlp_encode_bytes_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hn60 : n0.toNat < 2 ^ 60)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpBytesLenPure (if 0 < n0.toNat then memB s src0.toNat else 0) n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ∨
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 = none) :
    ∃ (len : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      len.toNat = rlpBytesLenPure (if 0 < n0.toNat then memB s src0.toNat else 0) n0.toNat ∧
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word len)) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact R16Shards.WkBlockTxEnc.lookup_rlp_encode_bytes)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hent_src : ent.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    have hnt_eb : reb ≠ some .timeOut := by
      rintro rfl; rw [heb] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_encode_bytes_body_len_exact ent dst0 src0 n0 Rl
      hcode hAR.1.memaddrs hent_dst hent_src hent_n hn60 hin_ivl (by rw [heb]; exact hnt_eb)
    rw [heb] at hret hnonret
    dsimp only at hret hnonret
    simp only [heb] at hnt hres ⊢
    cases reb with
    | none =>
      rcases hres with hr | hn0
      · exact False.elim (R16Shards.WkBlockTxEnc.not_resumes_error hr)
      · simp at hn0
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_eb
      | exception eid ev =>
        rcases hres with hr | hn0
        · exact False.elim (hnonret (.exception eid ev) rfl (fun _ h => by cases h) hr)
        · simp at hn0
      | returned rv =>
        obtain ⟨len, rfl, hlen_eq, hdst_lt, heff_eb⟩ := hret rv rfl
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only at hnt ⊢
        rw [if_pos hsh] at hnt ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word len))
          { seb with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_eb).with_locals_clock mid.locals mid.clock
        exact ⟨len, mid, hlen_eq, hdst_lt, heff_mid.globals, rfl,
          R16Shards.WkBlockTxEnc.HeapByteEff.of_m11_bre hAR heff_mid, hnt, rfl⟩
      | «break» | «continue» | error =>
        rcases hres with hr | hn0
        · exact False.elim (R16Shards.WkBlockTxEnc.not_resumes_error hr)
        · simp at hn0
      | finalFfi _ =>
        rcases hres with hr | hn0
        · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        · simp at hn0

private theorem lookup__node_rlp_begin :
    originalRuntimeCode.lookup (ofString "_node_rlp_begin") =
      some ([(ofString "fr", .one), (ofString "node", .one)],
        sourceFnBody Guest.Software.guestFn__node_rlp_begin, .one) :=
  lookup_of_guestAst_getElem 281 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_begin) rfl

private theorem lookup__node_rlp_finish :
    originalRuntimeCode.lookup (ofString "_node_rlp_finish") =
      some ([(ofString "fr", .one), (ofString "node", .one)],
        sourceFnBody Guest.Software.guestFn__node_rlp_finish, .one) :=
  lookup_of_guestAst_getElem 282 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_finish) rfl

private theorem lookup__node_rlp_fill :
    originalRuntimeCode.lookup (ofString "_node_rlp_fill") =
      some ([(ofString "node", .one)],
        sourceFnBody Guest.Software.guestFn__node_rlp_fill, .one) :=
  lookup_of_guestAst_getElem 284 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_fill) rfl

private theorem lookup_scratch_alloc :
    originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
  lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

private theorem lookup_scratch_mark :
    originalRuntimeCode.lookup (ofString "scratch_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_scratch_mark, .one) :=
  lookup_of_guestAst_getElem 14 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_mark) rfl

private theorem lookup_scratch_release :
    originalRuntimeCode.lookup (ofString "scratch_release") =
      some ([(ofString "m", .one)],
        sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
  lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_release) rfl

private theorem eval_call_local_alloc_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (nExp : ExpHOL 64)
    (n : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hn_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n)))
    (hgw : "heap_ptr" ∈ gw)
    (hnone : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "alloc") [nExp])).1 = none) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "alloc") [nExp])
    ∃ (hp q : BitVec 64),
      hp.toNat = globN s "heap_ptr" ∧
      hp.toNat % 8 = 0 ∧
      q.toNat = (hp.toNat + n.toNat + 7) / 8 * 8 ∧
      hp.toNat + n.toNat ≤ q.toNat ∧
      q.toNat ≤ heapLimit ∧
      q.toNat % 8 = 0 ∧
      globN out.2 "heap_ptr" = q.toNat ∧
      out.2.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      out.2.memory = s.memory ∧
      out.2.locals = s.locals.update (ofString lname, .val (.word hp)) ∧
      HeapByteEff s out.2 Rl gw := by
  intro out; dsimp only [out]
  obtain ⟨hp, hhp, hhp_nat⟩ := global_heap_ptr_word s hAR.2
  obtain ⟨w_old, hw_old⟩ := hl_old
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [nExp] =
      some [.val (.word n)] := by simp [evalListHOLFinite, evalListHOLExact, hn_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) n (by rw [hcode]; exact WkBlockTxEnc.lookup_alloc)
  simp only [ha, hlk] at hnone ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnone
  · simp only [hcz, ↓reduceIte] at hnone ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word n))
    set ent := callEntryStateHOLFinite s cmap
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
    simp only [hal] at hnone ⊢
    cases ra with
    | none => simp at hnone
    | some r0 =>
      cases r0 with
      | returned rv =>
        have hp_le_cmax : hp.toNat ≤ cMax.toNat := by
          have : cMax.toNat = heapLimit := rfl
          rw [this, hhp_nat]; exact hAR.2.2.1
        have hgen := M13.evaluate_alloc_body_general ent hp n hcode hp_le_cmax hhp hent_n rv (by rw [hal])
        rw [hal] at hgen; dsimp only at hgen
        obtain ⟨rfl, hg_sa, hm_sa, hpq, hqc, hq8⟩ := hgen
        set q : BitVec 64 := (hp + (n + 7)) &&& ((0 : BitVec 64) - 8)
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word hp)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh, if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word hp)) { sa with locals := s.locals }
        have hgb := M13.evaluateHOLFiniteState_guestInv_be ent (sourceFnBody Guest.Software.guestFn_alloc)
          (guestInv_callEntry s cmap hAR.1)
        rw [hal] at hgb
        have hG_mid : GuestInv mid :=
          guestInv_setVar _ _ _ (guestInv_with_locals_clock sa s.locals sa.clock hgb.1)
        have hq_lo : sourceBase ≤ q.toNat := by
          have := hAR.2.1; rw [← hhp_nat] at this; omega
        have hAR_mid : ArenaReady mid :=
          arenaReady_update_heap_ptr hG_mid hAR.2 hg_sa hq_lo hqc hq8
        have hq_nat : q.toNat = (hp.toNat + n.toNat + 7) / 8 * 8 := by
          have hhl264 : heapLimit < 2 ^ 64 := by decide
          have hn_lt : hp.toNat + (n.toNat + 7) < 2 ^ 64 := by omega
          have h1 : (n + 7).toNat = n.toNat + 7 := by
            rw [BitVec.toNat_add]; change (n.toNat + 7) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          have h2 : (hp + (n + 7)).toNat = hp.toNat + n.toNat + 7 := by
            rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hn_lt]; omega
          have h3 := and_neg8_toNat (hp + (n + 7))
          change q.toNat = _ at h3
          rw [h3, h2]
        have hmid_hp : globN mid "heap_ptr" = q.toNat := by
          change globN sa "heap_ptr" = q.toNat
          unfold globN; rw [hg_sa]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hmid_fp : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := by
          change globN sa "frame_mem_ptr" = globN s "frame_mem_ptr"
          unfold globN; rw [hg_sa]; simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
        have hmid_sp : globN mid "scratch_ptr" = globN s "scratch_ptr" := by
          change globN sa "scratch_ptr" = globN s "scratch_ptr"
          unfold globN; rw [hg_sa]; simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
        have heff_mid : HeapByteEff s mid Rl gw := by
          refine ⟨hAR_mid, hG_mid.memaddrs.trans hAR.1.memaddrs.symm,
            by rw [← hhp_nat, hmid_hp]; omega, hmid_fp, by rw [hmid_sp], hgb.2, ?_,
            fun a h => False.elim (h (by change sa.memory a = s.memory a; rw [hm_sa]; rfl)),
            fun a h => False.elim (h (by change sa.memory a = s.memory a; rw [hm_sa]; rfl)),
            fun b _ h => False.elim (h (by
              unfold memB
              have hm_b : mid.memory (panByteAlignHOL (BitVec.ofNat 64 b)) =
                  s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
                change sa.memory _ = s.memory _; rw [hm_sa]; rfl
              have hbe_b : mid.be = s.be := hgb.2
              rw [hm_b, hbe_b]))⟩
          intro k hk
          have hne : k ≠ ofString "heap_ptr" := fun heq =>
            hk (List.mem_map.2 ⟨"heap_ptr", hgw, heq.symm⟩)
          change s.globals.lookup k = sa.globals.lookup k
          rw [hg_sa]; simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
        exact ⟨hp, q, hhp_nat, by rw [hhp_nat]; exact hAR.2.2.2.2.2.2.1,
          hq_nat, hpq, hqc, hq8, hmid_hp, hg_sa, hm_sa, rfl, heff_mid⟩
      | _ => simp at hnone

private def ValidRlpFrame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (fr : Nat) : Prop :=
  fr % 8 = 0 ∧
  Inside (fr, 48) (globN s "scratch_ptr") scratchEnd ∧
  WordsOK s (fr, 48) ∧
  memW s (fr + 8) ∈ Nd ∧
  1 ≤ memW s (memW s (fr + 8)) ∧ memW s (memW s (fr + 8)) ≤ 3 ∧
  memW s (fr + 16) ≤ 16 ∧
  memW s (fr + 40) < 2 ^ 41 ∧
  (memW s (memW s (fr + 8)) = 3 → memW s (fr + 40) = 0) ∧
  (memW s (memW s (fr + 8)) = 1 →
    1 ≤ memW s (fr + 32) ∧
    memW s (fr + 32) ≤ memW s (memW s (fr + 8) + 40) / 2 + 1 ∧
    Inside (memW s (fr + 24), memW s (fr + 32)) sourceBase (globN s "heap_ptr") ∧
    (∀ o ∈ nodeExtents s Nd, Disj (memW s (fr + 24), memW s (fr + 32)) o) ∧
    (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      Disj (memW s (fr + 24), memW s (fr + 32)) (bufferRegion s gs)) ∧
    rlpBytesLenPure (memB s (memW s (fr + 24))) (memW s (fr + 32)) +
      rlpBytesLenPure 128 (memW s (memW s (fr + 8) + 56)) ≤ memW s (fr + 40) + 1 ∧
    (0 < memW s (memW s (fr + 8) + 56) →
      s.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW s (memW s (fr + 8) + 48)))))) ∧
  (memW s (memW s (fr + 8)) = 2 →
    1 ≤ memW s (fr + 32) ∧
    memW s (fr + 32) ≤ memW s (memW s (fr + 8) + 40) / 2 + 1 ∧
    Inside (memW s (fr + 24), memW s (fr + 32)) sourceBase (globN s "heap_ptr") ∧
    (∀ o ∈ nodeExtents s Nd, Disj (memW s (fr + 24), memW s (fr + 32)) o) ∧
    (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      Disj (memW s (fr + 24), memW s (fr + 32)) (bufferRegion s gs)) ∧
    memW s (fr + 40) = rlpBytesLenPure (memB s (memW s (fr + 24))) (memW s (fr + 32)))

private theorem validRlpFrame_of_heapByteEff_disj {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {fr : Nat}
    {Rl : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (_hN : NodeHeap s Nd)
    (hext_eq : nodeExtents post Nd = nodeExtents s Nd)
    (hbuf_eq : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      bufferRegion post gs = bufferRegion s gs)
    (hw_nd_eq : ∀ n ∈ Nd, memW post n = memW s n ∧
      (1 ≤ memW s n → memW post (n + 40) = memW s (n + 40)) ∧
      (memW s n = 1 → memW post (n + 48) = memW s (n + 48) ∧ memW post (n + 56) = memW s (n + 56)))
    (heff : HeapByteEff s post Rl gw)
    (hfr_disj : ∀ iv ∈ Rl, 0 < iv.2 → Disj iv (fr, 48))
    (hcb_disj_Rl : ∀ iv ∈ Rl, 0 < iv.2 →
      (memW s (memW s (fr + 8)) = 1 ∨ memW s (memW s (fr + 8)) = 2) →
      Disj iv (memW s (fr + 24), memW s (fr + 32)))
    (hv : ValidRlpFrame s Nd fr) :
    ValidRlpFrame post Nd fr := by
  obtain ⟨hfr8, hfr_in, hfr_W, hnd_in, hk1, hk3, hidx, hpay, hk3_pay, hk1_pay, hk2_pay⟩ := hv
  have hse : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have h264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hsp_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := heff.sp_le
  have hfr_in_post : Inside (fr, 48) (globN post "scratch_ptr") scratchEnd :=
    ⟨hsp_le.trans hfr_in.1, hfr_in.2⟩
  have hfr_W_post : WordsOK post (fr, 48) := by
    refine ⟨hfr8, hfr_W.2.1, ?_⟩
    intro k hk
    obtain ⟨w, hdom, _⟩ := hfr_W.2.2 k hk
    have hdom' : post.memaddrs (BitVec.ofNat 64 (fr + 8 * k)) := heff.memaddrs.symm ▸ hdom
    rcases hm : post.memory (BitVec.ofNat 64 (fr + 8 * k)) with ⟨w'⟩
    exact ⟨w', hdom', hm⟩
  have hword_eq : ∀ off, off % 8 = 0 → off + 8 ≤ 48 → memW post (fr + off) = memW s (fr + off) := by
    intro off hoff8 hoff_le
    obtain ⟨hfr_lo, hfr_hi⟩ := hfr_in
    dsimp only at hfr_lo hfr_hi
    apply memW_eq_of_heapByteEff_disj hAs heff (by omega)
      (Or.inr ⟨by omega, by omega⟩) (by omega)
    intro iv hiv hpos
    have hdj := hfr_disj iv hiv hpos
    dsimp [Disj] at hdj ⊢
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  have hw8 := hword_eq 8 (by decide) (by decide)
  have hw16 := hword_eq 16 (by decide) (by decide)
  have hw24 := hword_eq 24 (by decide) (by decide)
  have hw32 := hword_eq 32 (by decide) (by decide)
  have hw40 := hword_eq 40 (by decide) (by decide)
  have hnd_in' : memW post (fr + 8) ∈ Nd := hw8 ▸ hnd_in
  obtain ⟨hk_eq0, hn40_fn, hn_leaf_fn⟩ := hw_nd_eq _ hnd_in
  have hk_eq : memW post (memW post (fr + 8)) = memW s (memW s (fr + 8)) := by rw [hw8, hk_eq0]
  have hn40_eq : memW post (memW post (fr + 8) + 40) = memW s (memW s (fr + 8) + 40) := by
    rw [hw8, hn40_fn hk1]
  have hcb_byte_eq : (memW s (memW s (fr + 8)) = 1 ∨ memW s (memW s (fr + 8)) = 2) →
      1 ≤ memW s (fr + 32) → Inside (memW s (fr + 24), memW s (fr + 32)) sourceBase (globN s "heap_ptr") →
      memB post (memW s (fr + 24)) = memB s (memW s (fr + 24)) := by
    intro h12 hcl1 hcb_in
    obtain ⟨hcb_lo, hcb_hi⟩ := hcb_in
    dsimp only at hcb_lo hcb_hi
    have hhp_hi := hAs.2.2.1
    have hb_lt : memW s (fr + 24) < 2 ^ 64 := by omega
    by_contra hne
    rcases heff.byte_frame (memW s (fr + 24)) hb_lt hne with
      ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
    · have hpos : 0 < iv.2 := by omega
      have hdj := hcb_disj_Rl iv hiv hpos h12
      dsimp [Disj] at hdj; rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
    · have := hAs.2.2.2.1; have : heapLimit ≤ scratchStart := by decide
      dsimp [freeGap] at hfg1 hfg2; omega
    · dsimp [heapFree] at hhf1 hhf2; omega
  refine ⟨hfr8, hfr_in_post, hfr_W_post, hnd_in',
    by rw [hk_eq]; exact hk1, by rw [hk_eq]; exact hk3,
    by rw [hw16]; exact hidx, by rw [hw40]; exact hpay,
    fun h3 => by rw [hw40]; exact hk3_pay (hk_eq ▸ h3), ?_, ?_⟩
  · intro h1
    have h1s : memW s (memW s (fr + 8)) = 1 := hk_eq ▸ h1
    have hn48_eq : memW post (memW post (fr + 8) + 48) = memW s (memW s (fr + 8) + 48) := by
      rw [hw8, (hn_leaf_fn h1s).1]
    have hn56_eq : memW post (memW post (fr + 8) + 56) = memW s (memW s (fr + 8) + 56) := by
      rw [hw8, (hn_leaf_fn h1s).2]
    obtain ⟨hcl1, hcl_hi, hcb_in, hcb_disj, hcb_kb, hpay_lo, hdom1⟩ := hk1_pay h1s
    have hcb_b := hcb_byte_eq (Or.inl h1s) hcl1 hcb_in
    refine ⟨by rw [hw32]; exact hcl1, by rw [hw32, hn40_eq]; exact hcl_hi,
      ⟨by rw [hw24]; exact hcb_in.1, by rw [hw24, hw32]; exact hcb_in.2.trans heff.hp_le⟩,
      fun o ho => by rw [hext_eq] at ho; rw [hw24, hw32]; exact hcb_disj o ho,
      fun gs hgs => by rw [hbuf_eq gs hgs, hw24, hw32]; exact hcb_kb gs hgs,
      by rw [hw40, hw24, hw32, hn56_eq, hcb_b]; exact hpay_lo, ?_⟩
    intro hpos
    rw [hn56_eq] at hpos
    rw [hn48_eq]
    exact heff.memaddrs.symm ▸ hdom1 hpos
  · intro h2
    have h2s : memW s (memW s (fr + 8)) = 2 := hk_eq ▸ h2
    obtain ⟨hcl1, hcl_hi, hcb_in, hcb_disj, hcb_kb, hpay2⟩ := hk2_pay h2s
    have hcb_b := hcb_byte_eq (Or.inr h2s) hcl1 hcb_in
    refine ⟨by rw [hw32]; exact hcl1, by rw [hw32, hn40_eq]; exact hcl_hi,
      ⟨by rw [hw24]; exact hcb_in.1, by rw [hw24, hw32]; exact hcb_in.2.trans heff.hp_le⟩,
      fun o ho => by rw [hext_eq] at ho; rw [hw24, hw32]; exact hcb_disj o ho,
      fun gs hgs => by rw [hbuf_eq gs hgs, hw24, hw32]; exact hcb_kb gs hgs, ?_⟩
    rw [hw40, hw24, hw32, hcb_b, hpay2]

private def noReturnLocal : ProgHOL 64 → Bool
  | .seq a b => noReturnLocal a && noReturnLocal b
  | .ite _ a b => noReturnLocal a && noReturnLocal b
  | .while _ a => noReturnLocal a
  | .dec _ _ _ a => noReturnLocal a
  | .decCall _ _ _ _ a => noReturnLocal a
  | .call (some (_, none)) _ _ => true
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturnLocal {F : Type} (p : ProgHOL 64) (hp : noReturnLocal p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | dec nm sh init body =>
    have hb : noReturnLocal body = true := by simpa [shape, noReturnLocal] using hp
    have rem := evaluateHOLFiniteState_clock_le s (.dec nm sh init body)
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · rename_i val _
      split
      · have hclk : (setVarHOLFinite nm val s).clock = s.clock := rfl
        exact evaluate_noReturnLocal body hb (setVarHOLFinite nm val s) v
      · simp
  | decCall nm sh fn args cont =>
    have hb : noReturnLocal cont = true := by simpa [shape, noReturnLocal] using hp
    subst shape
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp
    · split
      · simp
      · rename_i body callee rs _
        split
        · simp
        · rename_i nonzero
          dsimp only
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = out at cl ⊢
          rcases out with ⟨r, st⟩
          dsimp only at cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          rcases r with _ | (_ | _ | _ | _ | rv | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try simp)
          split
          · have small : (if s.clock - 1 < st.clock then s.clock - 1 else st.clock) < s.clock := by
              split <;> omega
            exact evaluate_noReturnLocal cont hb _ v
          · simp
  | call info fn args =>
    have hinfo : ∃ d, info = some (d, none) := by
      rcases info with _ | ⟨d, _ | _⟩
      · simp [shape, noReturnLocal] at hp
      · exact ⟨d, rfl⟩
      · simp [shape, noReturnLocal] at hp
    subst shape
    obtain ⟨d, rfl⟩ := hinfo
    rw [evaluateHOLFiniteState_call]
    split
    · simp
    · split
      · simp
      · rename_i body callee _ _
        split
        · simp
        · generalize evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = out
          rcases out with ⟨r, st⟩
          rcases r with _ | (_ | _ | _ | _ | rv | _ | _)
          all_goals (try simp)
          split
          · cases d with
            | none => simp
            | some d =>
              rcases d with ⟨kind, name⟩
              dsimp only
              split <;> cases kind <;> simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite]
          · simp
  | seq a b =>
    have hab : noReturnLocal a = true ∧ noReturnLocal b = true := by
      simpa [shape, noReturnLocal, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnLocal a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    have mclk : m.clock ≤ s.clock := rem
    cases r with
    | some _ => exact ha
    | none => exact evaluate_noReturnLocal b hab.2 m v
  | ite _ a b =>
    have hab : noReturnLocal a = true ∧ noReturnLocal b = true := by
      simpa [shape, noReturnLocal, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnLocal b hab.2 s v
      · exact evaluate_noReturnLocal a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : noReturnLocal body = true := by simpa [shape, noReturnLocal] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnLocal body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact evaluate_noReturnLocal (.while cond body) (by simpa [noReturnLocal] using hb) mid v
          | some r1 =>
            cases r1 with
            | «continue» => exact evaluate_noReturnLocal (.while cond body) (by simpa [noReturnLocal] using hb) mid v
            | returned _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noReturnLocal] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | exact Or.inl dec_lt
      | exact Or.inl smaller
      | omega

private theorem eval__node_rlp_begin_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (frw nodew : BitVec 64)
    (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (hN : NodeHeap s Nd) (hKS : KeccakBufsSafe s Nd)
    (hfr_loc : s.locals.lookup (ofString "fr") = some (.val (.word frw)))
    (hnode_loc : s.locals.lookup (ofString "node") = some (.val (.word nodew)))
    (hfr_in : Inside (frw.toNat, 48) (globN s "scratch_ptr") scratchEnd)
    (hfr_W : WordsOK s (frw.toNat, 48))
    (hnode_in : nodew.toNat ∈ Nd)
    (hk1 : 1 ≤ memW s nodew.toNat)
    (hfr8_eq : memW s (frw.toNat + 8) = nodew.toNat)
    (hfr16_le : memW s (frw.toNat + 16) ≤ 16)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_rlp_begin)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_rlp_begin)).2
    v = .val (.word 0) ∧
    HeapByteEff s post [(frw.toNat + 24, 24)] ["heap_ptr"] ∧
    NodeHeap post Nd ∧
    nodeExtents post Nd = nodeExtents s Nd ∧
    KeccakBufsSafe post Nd ∧
    (∀ n ∈ Nd, ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
      memW post (n + off) = memW s (n + off)) ∧
    ValidRlpFrame post Nd frw.toNat := by
  intro post; dsimp only [post]
  have hse : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have h264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhl_he : heapLimit ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  obtain ⟨hk_le3, hal_nd, hin_nd, hw_nd, _, _, hkey_nd, _, hleaf_v, _⟩ := hN.1 nodew.toNat hnode_in
  have hnd_hi : nodew.toNat + nodeSize (memW s nodew.toNat) ≤ heapEnd :=
    hin_nd.2.trans hhl_he
  have hsz_ge32 := nodeSize_ge32 (memW s nodew.toNat)
  have hb_eq : sourceFnBody Guest.Software.guestFn__node_rlp_begin =
      .dec (ofString "k") .one (.load .one (.op .add [.var .local (ofString "node"), .const 0]))
        (.dec (ofString "payload") .one (.const 0)
          (.dec (ofString "cbuf") .one (.const 0)
            (.dec (ofString "clen") .one (.const 0)
              (.seq
                (.ite (.cmp .notEqual (.var .local (ofString "k")) (.const 3))
                  (.dec (ofString "nlen") .one (.load .one (.op .add [.var .local (ofString "node"), .const 40]))
                    (.seq
                      (.call (some (some (VarKind.local, ofString "cbuf"), none)) (ofString "alloc")
                        [.op .add [.shift .lsr (.var .local (ofString "nlen")) (.const 1), .const 2]])
                      (.dec (ofString "isl") .one (.const 0)
                        (.seq
                          (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
                            (.assign .local (ofString "isl") (.const 1))
                            .skip)
                          (.seq
                            (.call (some (some (VarKind.local, ofString "clen"), none))
                              (ofString "nibble_list_to_compact")
                              [.load .one (.op .add [.var .local (ofString "node"), .const 32]),
                               .var .local (ofString "nlen"),
                               .var .local (ofString "isl"),
                               .var .local (ofString "cbuf")])
                            (.decCall (ofString "el") .one (ofString "rlp_bytes_encoded_len")
                              [.loadByte (.var .local (ofString "cbuf")), .var .local (ofString "clen")]
                              (.seq
                                (.assign .local (ofString "payload") (.var .local (ofString "el")))
                                (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
                                  (.decCall (ofString "vl") .one (ofString "rlp_value_encoded_len")
                                    [.load .one (.op .add [.var .local (ofString "node"), .const 48]),
                                     .load .one (.op .add [.var .local (ofString "node"), .const 56])]
                                    (.assign .local (ofString "payload")
                                      (.op .add [.var .local (ofString "payload"), .var .local (ofString "vl")])))
                                  .skip))))))))
                  .skip)
                (.seq
                  (.store (.op .add [.var .local (ofString "fr"), .const 24]) (.var .local (ofString "cbuf")))
                  (.seq
                    (.store (.op .add [.var .local (ofString "fr"), .const 32]) (.var .local (ofString "clen")))
                    (.seq
                      (.store (.op .add [.var .local (ofString "fr"), .const 40]) (.var .local (ofString "payload")))
                      (.return (.const 0))))))))) := rfl
  rw [hb_eq] at hret
  obtain ⟨kw, hkw_ev, hkw_nat⟩ := eval_load_memW_of_wordsOK (off := 0) hw_nd (by decide) (by omega)
    (by omega) (e := .op .add [.var .local (ofString "node"), .const 0])
    (by simp [evalHOLExact, evalListHOLExact, hnode_loc, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
  simp only [Nat.add_zero] at hkw_nat
  rw [evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  rw [hkw_ev] at hret
  have hsh_k : shapeEqHOL .one (shapeOfHOLExact (.val (.word kw) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hret; rw [if_pos hsh_k] at hret; dsimp only at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  have hsh_0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have hev0 : ∀ (t : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.const 0) =
        some (.val (.word 0)) := fun _ => rfl
  dsimp only at hret; rw [hev0] at hret; dsimp only at hret; rw [if_pos hsh_0] at hret; dsimp only at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret; rw [hev0] at hret; dsimp only at hret; rw [if_pos hsh_0] at hret; dsimp only at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret; rw [hev0] at hret; dsimp only at hret; rw [if_pos hsh_0] at hret; dsimp only at hret
  let s0 := setVarHOLFinite (ofString "clen") (.val (.word 0))
    (setVarHOLFinite (ofString "cbuf") (.val (.word 0))
      (setVarHOLFinite (ofString "payload") (.val (.word 0))
        (setVarHOLFinite (ofString "k") (.val (.word kw)) s)))
  have hs0_AR : ArenaReady s0 := ⟨guestInv_setVar _ _ _ (guestInv_setVar _ _ _
    (guestInv_setVar _ _ _ (guestInv_setVar _ _ _ hAR.1))), hAR.2⟩
  have hs0_eff : HeapByteEff s s0 [] ["heap_ptr"] :=
    (HeapByteEff.refl hAR [] ["heap_ptr"]).locals_clock s0.locals s0.clock
  have hs0_k : s0.locals.lookup (ofString "k") = some (.val (.word kw)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "clen" ≠ ofString "k" by decide,
      show ofString "cbuf" ≠ ofString "k" by decide,
      show ofString "payload" ≠ ofString "k" by decide]
  have hs0_pay : s0.locals.lookup (ofString "payload") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "clen" ≠ ofString "payload" by decide,
      show ofString "cbuf" ≠ ofString "payload" by decide]
  have hs0_cbuf : s0.locals.lookup (ofString "cbuf") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "clen" ≠ ofString "cbuf" by decide]
  have hs0_clen : s0.locals.lookup (ofString "clen") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_node : s0.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnode_loc,
      show ofString "clen" ≠ ofString "node" by decide,
      show ofString "cbuf" ≠ ofString "node" by decide,
      show ofString "payload" ≠ ofString "node" by decide,
      show ofString "k" ≠ ofString "node" by decide]
  have hs0_fr : s0.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hfr_loc,
      show ofString "clen" ≠ ofString "fr" by decide,
      show ofString "cbuf" ≠ ofString "fr" by decide,
      show ofString "payload" ≠ ofString "fr" by decide,
      show ofString "k" ≠ ofString "fr" by decide]
  set pIte : ProgHOL 64 :=
    .ite (.cmp .notEqual (.var .local (ofString "k")) (.const 3))
      (.dec (ofString "nlen") .one (.load .one (.op .add [.var .local (ofString "node"), .const 40]))
        (.seq
          (.call (some (some (VarKind.local, ofString "cbuf"), none)) (ofString "alloc")
            [.op .add [.shift .lsr (.var .local (ofString "nlen")) (.const 1), .const 2]])
          (.dec (ofString "isl") .one (.const 0)
            (.seq
              (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
                (.assign .local (ofString "isl") (.const 1))
                .skip)
              (.seq
                (.call (some (some (VarKind.local, ofString "clen"), none))
                  (ofString "nibble_list_to_compact")
                  [.load .one (.op .add [.var .local (ofString "node"), .const 32]),
                   .var .local (ofString "nlen"),
                   .var .local (ofString "isl"),
                   .var .local (ofString "cbuf")])
                (.decCall (ofString "el") .one (ofString "rlp_bytes_encoded_len")
                  [.loadByte (.var .local (ofString "cbuf")), .var .local (ofString "clen")]
                  (.seq
                    (.assign .local (ofString "payload") (.var .local (ofString "el")))
                    (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
                      (.decCall (ofString "vl") .one (ofString "rlp_value_encoded_len")
                        [.load .one (.op .add [.var .local (ofString "node"), .const 48]),
                         .load .one (.op .add [.var .local (ofString "node"), .const 56])]
                        (.assign .local (ofString "payload")
                          (.op .add [.var .local (ofString "payload"), .var .local (ofString "vl")])))
                      .skip))))))))
      .skip
  set pStores : ProgHOL 64 :=
    .seq
      (.store (.op .add [.var .local (ofString "fr"), .const 24]) (.var .local (ofString "cbuf")))
      (.seq
        (.store (.op .add [.var .local (ofString "fr"), .const 32]) (.var .local (ofString "clen")))
        (.seq
          (.store (.op .add [.var .local (ofString "fr"), .const 40]) (.var .local (ofString "payload")))
          (.return (.const 0))))
  change (evaluateHOLFiniteState s0 (.seq pIte pStores)).1 = some (.returned v) at hret
  have hpost_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_rlp_begin)).2 =
      ({ (evaluateHOLFiniteState s0 (.seq pIte pStores)).2 with
         locals := (HolFiniteMapExact.resVarEq
           (HolFiniteMapExact.resVarEq
             (HolFiniteMapExact.resVarEq
               (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s0 (.seq pIte pStores)).2.locals
                 (ofString "clen", (setVarHOLFinite (ofString "cbuf") (.val (.word 0))
                   (setVarHOLFinite (ofString "payload") (.val (.word 0))
                     (setVarHOLFinite (ofString "k") (.val (.word kw)) s))).locals.lookup (ofString "clen")))
               (ofString "cbuf", (setVarHOLFinite (ofString "payload") (.val (.word 0))
                 (setVarHOLFinite (ofString "k") (.val (.word kw)) s)).locals.lookup (ofString "cbuf")))
             (ofString "payload", (setVarHOLFinite (ofString "k") (.val (.word kw)) s).locals.lookup (ofString "payload")))
           (ofString "k", s.locals.lookup (ofString "k"))) } : PanSemStateFiniteExact 64 F) := by
    rw [hb_eq, evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hkw_ev]; dsimp only; rw [if_pos hsh_k]; dsimp only
    rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev0]; dsimp only; rw [if_pos hsh_0]; dsimp only
    rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev0]; dsimp only; rw [if_pos hsh_0]; dsimp only
    rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev0]; dsimp only; rw [if_pos hsh_0]
  rw [hpost_eq]
  rw [evaluateHOLFiniteState_seq_line780] at hret
  rcases h1 : evaluateHOLFiniteState s0 pIte with ⟨r1, s1⟩
  simp only [h1] at hret
  have hpIte_noRet : ∀ rv, r1 ≠ some (.returned rv) := by
    intro rv hrv
    have hnr := evaluate_noReturnLocal pIte rfl s0 rv
    rw [h1] at hnr; exact hnr hrv
  cases r1 with
  | some r1' =>
    dsimp only at hret
    injection hret with h; subst h
    exact False.elim (hpIte_noRet v rfl)
  | none =>
    dsimp only at hret
    have hs1_props :
        ∃ (cbufw clenw payw : BitVec 64),
          s1.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
          s1.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) ∧
          s1.locals.lookup (ofString "clen") = some (.val (.word clenw)) ∧
          s1.locals.lookup (ofString "payload") = some (.val (.word payw)) ∧
          payw.toNat < 2 ^ 41 ∧
          HeapByteEff s s1 [] ["heap_ptr"] ∧
          (memW s nodew.toNat = 3 → payw.toNat = 0) ∧
          (memW s nodew.toNat = 1 →
            1 ≤ clenw.toNat ∧ clenw.toNat ≤ memW s (nodew.toNat + 40) / 2 + 1 ∧
            Inside (cbufw.toNat, clenw.toNat) sourceBase (globN s1 "heap_ptr") ∧
            (∀ o ∈ nodeExtents s Nd, Disj (cbufw.toNat, clenw.toNat) o) ∧
            (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
              Disj (cbufw.toNat, clenw.toNat) (bufferRegion s gs)) ∧
            rlpBytesLenPure (memB s1 cbufw.toNat) clenw.toNat +
              rlpBytesLenPure 128 (memW s (nodew.toNat + 56)) ≤ payw.toNat + 1 ∧
            (0 < memW s (nodew.toNat + 56) →
              s.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW s (nodew.toNat + 48)))))) ∧
          (memW s nodew.toNat = 2 →
            1 ≤ clenw.toNat ∧ clenw.toNat ≤ memW s (nodew.toNat + 40) / 2 + 1 ∧
            Inside (cbufw.toNat, clenw.toNat) sourceBase (globN s1 "heap_ptr") ∧
            (∀ o ∈ nodeExtents s Nd, Disj (cbufw.toNat, clenw.toNat) o) ∧
            (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
              Disj (cbufw.toNat, clenw.toNat) (bufferRegion s gs)) ∧
            payw.toNat = rlpBytesLenPure (memB s1 cbufw.toNat) clenw.toNat) := by
      dsimp only [pIte] at h1
      rw [evaluateHOLFiniteState_ite] at h1
      have hcmp3 : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "k")) (.const 3)) =
          some (.val (.word (if kw = 3 then 0 else 1))) := by
        simp [evalHOLExact, hs0_k, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp3] at h1; dsimp only at h1
      by_cases hk3_eq : kw = 3
      · rw [if_pos hk3_eq] at h1
        rw [evaluateHOLFiniteState_skip] at h1
        injection h1 with _ hs1_eq; subst hs1_eq
        have hkw3 : memW s nodew.toNat = 3 := by rw [← hkw_nat, hk3_eq]; rfl
        exact ⟨0, 0, 0, hs0_fr, hs0_cbuf, hs0_clen, hs0_pay, by decide, hs0_eff,
          fun _ => rfl, fun h1 => by omega, fun h2 => by omega⟩
      · rw [if_neg hk3_eq] at h1
        have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        rw [if_neg h10] at h1
        have hk12 : memW s nodew.toNat = 1 ∨ memW s nodew.toNat = 2 := by
          have : kw.toNat ≠ 3 := fun h => hk3_eq (BitVec.eq_of_toNat_eq h)
          omega
        have hsz_ge56 : 56 ≤ nodeSize (memW s nodew.toNat) := by
          rcases hk12 with h | h <;> simp [nodeSize, h]
        have hs0_W_nd : WordsOK s0 (nodeIvl s nodew.toNat) :=
          P3MptSet.wordsOK_transfer hAR.1 hs0_AR.1 hw_nd
        obtain ⟨nlenw, hnlen_ev, hnlen_nat⟩ := eval_load_memW_of_wordsOK (s := s0) (off := 40) hs0_W_nd (by decide) (by omega)
          (by omega) (e := .op .add [.var .local (ofString "node"), .const 40])
          (by simp [evalHOLExact, evalListHOLExact, hs0_node, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
        have hnlen_nat : nlenw.toNat = memW s (nodew.toNat + 40) := hnlen_nat
        have hnlen_hi : nlenw.toNat ≤ heapLimit := by
          rcases hkey_nd hk12 with hz | ⟨_, _, hin_k, _⟩
          · rw [hnlen_nat, hz]; decide
          · rw [hnlen_nat]; have := hin_k.2; dsimp at this; omega
        have hhl_val : heapLimit < 2 ^ 35 := by decide
        rw [evaluateHOLFiniteState_dec_total] at h1; dsimp only at h1
        rw [hnlen_ev] at h1; dsimp only at h1
        have hsh_nl : shapeEqHOL .one (shapeOfHOLExact (.val (.word nlenw) : ValueHOL 64)) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh_nl] at h1
        let sa0 := setVarHOLFinite (ofString "nlen") (.val (.word nlenw)) s0
        have hsa0_AR : ArenaReady sa0 := ⟨guestInv_setVar _ _ _ hs0_AR.1, hs0_AR.2⟩
        have hsa0_nlen : sa0.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
          simp [sa0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsa0_cbuf : sa0.locals.lookup (ofString "cbuf") = some (.val (.word 0)) := by
          simp [sa0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_cbuf,
            show ofString "nlen" ≠ ofString "cbuf" by decide]
        obtain ⟨hn1, hn2, hseq1⟩ := seq_none_rel sa0 _ _ (congrArg Prod.fst h1)
        have hcap_ev : @evalHOLExact 64 F _ sa0.toExact (fun a => Classical.propDecidable (sa0.memaddrs a))
            (.op .add [.shift .lsr (.var .local (ofString "nlen")) (.const 1), .const 2]) =
            some (.val (.word ((nlenw >>> 1) + 2))) := by
          simp [evalHOLExact, evalListHOLExact, hsa0_nlen, wordOpHOL, wordOp, wordShiftHOL,
            valueIsWord, valueWord, BitVec.add_zero]
        have hcap_nat : ((nlenw >>> 1) + 2).toNat = nlenw.toNat / 2 + 2 := by
          have hlsr : (nlenw >>> (1 : Nat)).toNat = nlenw.toNat / 2 := by
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          rw [BitVec.toNat_add]
          change ((nlenw >>> (1 : Nat)).toNat + 2) % 2 ^ 64 = _
          rw [hlsr]
          exact Nat.mod_eq_of_lt (by omega)
        obtain ⟨cbufw, q_cb, hcb_hp, _, hq_cb_nat, hcb_le_q, hq_cb_hi, _, hhp_sa1, _, hm_sa1, hloc_sa1, heff_alloc⟩ :=
          eval_call_local_alloc_none sa0 "cbuf" _ ((nlenw >>> 1) + 2) [] ["heap_ptr"]
            hc hsa0_AR ⟨0, hsa0_cbuf⟩ hcap_ev (by simp) hn1
        let sa1 := (evaluateHOLFiniteState sa0
          (.call (some (some (VarKind.local, ofString "cbuf"), none)) (ofString "alloc")
            [.op .add [.shift .lsr (.var .local (ofString "nlen")) (.const 1), .const 2]])).2
        have hsa1_AR : ArenaReady sa1 := heff_alloc.arena
        have hsa1_N : NodeHeap sa1 Nd :=
          (nodeHeap_of_heapByteEff_disj hsa0_AR hN heff_alloc (fun _ h => by simp at h)).1
        have hsa1_cbuf : sa1.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
          rw [hloc_sa1]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hsa1_nlen : sa1.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
          rw [hloc_sa1]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsa0_nlen,
            show ofString "cbuf" ≠ ofString "nlen" by decide]
        have hsa1_k : sa1.locals.lookup (ofString "k") = some (.val (.word kw)) := by
          rw [hloc_sa1]; simp [sa0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_k,
            show ofString "cbuf" ≠ ofString "k" by decide,
            show ofString "nlen" ≠ ofString "k" by decide]
        have hsa1_node : sa1.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
          rw [hloc_sa1]; simp [sa0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_node,
            show ofString "cbuf" ≠ ofString "node" by decide,
            show ofString "nlen" ≠ ofString "node" by decide]
        have hsa1_clen : sa1.locals.lookup (ofString "clen") = some (.val (.word 0)) := by
          rw [hloc_sa1]; simp [sa0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_clen,
            show ofString "cbuf" ≠ ofString "clen" by decide,
            show ofString "nlen" ≠ ofString "clen" by decide]
        have hsa1_pay : sa1.locals.lookup (ofString "payload") = some (.val (.word 0)) := by
          rw [hloc_sa1]; simp [sa0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_pay,
            show ofString "cbuf" ≠ ofString "payload" by decide,
            show ofString "nlen" ≠ ofString "payload" by decide]
        have hsa1_fr : sa1.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
          rw [hloc_sa1]; simp [sa0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_fr,
            show ofString "cbuf" ≠ ofString "fr" by decide,
            show ofString "nlen" ≠ ofString "fr" by decide]
        change (evaluateHOLFiniteState sa1 _).1 = none at hn2
        rw [evaluateHOLFiniteState_dec_total] at hn2
        dsimp only at hn2; rw [hev0] at hn2; dsimp only at hn2; rw [if_pos hsh_0] at hn2; dsimp only at hn2
        let sa2 := setVarHOLFinite (ofString "isl") (.val (.word 0)) sa1
        obtain ⟨hn3, hn4, hseq2⟩ := seq_none_rel sa2 _ _ hn2
        let islw : BitVec 64 := if kw = 1 then 1 else 0
        let sa3 := (evaluateHOLFiniteState sa2
          (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
            (.assign .local (ofString "isl") (.const 1)) .skip)).2
        have hsa3_eq : sa3 = setVarHOLFinite (ofString "isl") (.val (.word islw)) sa1 := by
          dsimp [sa3, sa2, islw]
          rw [evaluateHOLFiniteState_ite]
          have hcmp1 : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "isl") (.val (.word 0#64)) sa1).toExact
              (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "isl") (.val (.word 0#64)) sa1).memaddrs a))
              (.cmp .equal (.var .local (ofString "k")) (.const 1#64)) =
              some (.val (.word (if kw = 1#64 then 1#64 else 0#64))) := by
            simp [evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa1_k,
              show ofString "isl" ≠ ofString "k" by decide, Compiler.Encoders.Asm.wordCmpHOL]
          rw [hcmp1]; dsimp only
          by_cases hk1_eq : kw = 1#64
          · rw [if_pos hk1_eq]
            have h10' : ¬ ((1#64 : BitVec 64) = 0) := by decide
            rw [if_neg h10', evaluateHOLFiniteState_assign]
            have hev1 : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "isl") (.val (.word 0#64)) sa1).toExact
                (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "isl") (.val (.word 0#64)) sa1).memaddrs a))
                (.const 1#64) = some (.val (.word 1#64)) := by simp [evalHOLExact]
            have hcond_isl : isValidValueHOLFinite (setVarHOLFinite (ofString "isl") (.val (.word 0#64)) sa1)
                .local (ofString "isl") (.val (.word 1#64)) = true := by
              simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
                toExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, shapeOfHOLExact, shapeEqHOL]
            rw [hev1]; dsimp only; rw [if_pos hcond_isl]; dsimp only [setKvarHOLFinite, setVarHOLFinite]
            congr 1
            apply HolFiniteMapExact.ext; funext key
            simp only [HolFiniteMapExact.lookup_update_pointwise, FUPDATE_HOL]
            by_cases hk : key = ofString "isl" <;> simp [hk]
          · rw [if_neg hk1_eq]; simp [evaluateHOLFiniteState_skip]
        obtain ⟨hn5, hn6, hseq3⟩ := seq_none_rel sa3 _ _ hn4
        have hsa3_AR : ArenaReady sa3 := by rw [hsa3_eq]; exact ⟨guestInv_setVar _ _ _ hsa1_AR.1, hsa1_AR.2⟩
        have hsa3_N : NodeHeap sa3 Nd := by rw [hsa3_eq]; exact hsa1_N
        have hsa3_c : sa3.code = originalRuntimeCode := by
          rw [hsa3_eq]; exact (evaluateHOLFiniteState_metadata sa0 _).1.trans hc
        have hsa3_node : sa3.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
          rw [hsa3_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa1_node,
            show ofString "isl" ≠ ofString "node" by decide]
        have hsa3_nlen : sa3.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
          rw [hsa3_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa1_nlen,
            show ofString "isl" ≠ ofString "nlen" by decide]
        have hsa3_isl : sa3.locals.lookup (ofString "isl") = some (.val (.word islw)) := by
          rw [hsa3_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsa3_cbuf : sa3.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
          rw [hsa3_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa1_cbuf,
            show ofString "isl" ≠ ofString "cbuf" by decide]
        have hsa3_clen : sa3.locals.lookup (ofString "clen") = some (.val (.word 0)) := by
          rw [hsa3_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa1_clen,
            show ofString "isl" ≠ ofString "clen" by decide]
        have hsa3_W_nd : WordsOK sa3 (nodeIvl s nodew.toNat) := by
          rw [hsa3_eq]
          refine ⟨hw_nd.1, hw_nd.2.1, fun i hi => ?_⟩
          obtain ⟨w, hd, hm⟩ := hw_nd.2.2 i hi
          exact ⟨w, heff_alloc.memaddrs.symm ▸ hd, by change sa1.memory _ = _; rw [hm_sa1]; exact hm⟩
        obtain ⟨nibsw, hnibs_ev, _⟩ := eval_load_memW_of_wordsOK (off := 32) hsa3_W_nd (by decide) (by omega)
          (by omega) (e := .op .add [.var .local (ofString "node"), .const 32])
          (by simp [evalHOLExact, evalListHOLExact, hsa3_node, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
        have hcb_cap_hi : cbufw.toNat + (nlenw.toNat / 2 + 2) ≤ globN sa3 "heap_ptr" := by
          have : globN sa3 "heap_ptr" = q_cb.toNat := by rw [hsa3_eq]; exact hhp_sa1
          rw [this]; rw [hcap_nat] at hcb_le_q; exact hcb_le_q
        obtain ⟨clenw, hcl1, hcl_bound, hloc_sa4, heff_nlc, hsa4_N, _⟩ :=
          eval_call_local_nibble_list_to_compact_nodeHeap sa3 Nd "clen"
            (.load .one (.op .add [.var .local (ofString "node"), .const 32]))
            (.var .local (ofString "nlen"))
            (.var .local (ofString "isl"))
            (.var .local (ofString "cbuf"))
            nibsw nlenw islw cbufw (nlenw.toNat / 2 + 2) [(cbufw.toNat, nlenw.toNat / 2 + 2)] ["heap_ptr"]
            hsa3_c hsa3_AR hsa3_N ⟨0, hsa3_clen⟩
            hnibs_ev (by simp [evalHOLExact, hsa3_nlen]) (by simp [evalHOLExact, hsa3_isl])
            (by simp [evalHOLExact, hsa3_cbuf])
            (hcb_cap_hi.trans hsa3_AR.2.2.1)
            (by omega) (by omega)
            (Or.inl ⟨(cbufw.toNat, nlenw.toNat / 2 + 2), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
            (fun iv hiv _ o ho => by
              simp only [List.mem_singleton] at hiv; subst hiv
              have hext_s : nodeExtents sa3 Nd = nodeExtents s Nd := by
                rw [hsa3_eq]
                exact (nodeHeap_of_heapByteEff_disj hsa0_AR hN heff_alloc (fun _ h => by simp at h)).2
              rw [hext_s] at ho
              unfold nodeExtents at ho
              obtain ⟨m, hm, hm_iv⟩ := List.mem_flatMap.1 ho
              have hcb_ge : globN s "heap_ptr" ≤ cbufw.toNat := by
                have : globN sa0 "heap_ptr" = globN s "heap_ptr" := rfl
                omega
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hm_iv
              rcases hm_iv with rfl | rfl
              · have hal_m := (hN.1 m hm).2.1
                rcases hal_m with ⟨_, hhi_m⟩ | ⟨hlo_m, _⟩
                · exact Or.inr (Or.inr (Or.inr (by dsimp [nodeIvl] at hhi_m ⊢; omega)))
                · have hss : heapLimit ≤ scratchStart := by decide
                  have := hAR.2.2.2.1; have := hAR.2.2.2.2.1; have := hsa3_AR.2.2.1
                  exact Or.inr (Or.inr (Or.inl (by dsimp [nodeIvl] at hlo_m ⊢; omega)))
              · unfold nodePath
                split_ifs with hp_cond
                · rcases (hN.1 m hm).2.2.2.2.2.2.1 hp_cond.1 with hz | ⟨_, hal_p, _, _⟩
                  · exact absurd hz hp_cond.2
                  · rcases hal_p with ⟨_, hhi_p⟩ | ⟨hlo_p, _⟩
                    · exact Or.inr (Or.inr (Or.inr (by dsimp only at hhi_p ⊢; omega)))
                    · have hss : heapLimit ≤ scratchStart := by decide
                      have := hAR.2.2.2.1; have := hAR.2.2.2.2.1; have := hsa3_AR.2.2.1
                      exact Or.inr (Or.inr (Or.inl (by dsimp only at hlo_p ⊢; omega)))
                · exact Or.inr (Or.inl rfl))
            hn5
        let sa4 := (evaluateHOLFiniteState sa3
          (.call (some (some (VarKind.local, ofString "clen"), none))
            (ofString "nibble_list_to_compact")
            [.load .one (.op .add [.var .local (ofString "node"), .const 32]),
             .var .local (ofString "nlen"),
             .var .local (ofString "isl"),
             .var .local (ofString "cbuf")])).2
        have hsa4_c : sa4.code = originalRuntimeCode :=
          (evaluateHOLFiniteState_metadata sa3 _).1.trans hsa3_c
        have hsa4_AR : ArenaReady sa4 := heff_nlc.arena
        have heff_s_sa4 : HeapByteEff s sa4 [] ["heap_ptr"] := by
          have heff_nlc_empty : HeapByteEff sa0 sa4 [] ["heap_ptr"] := by
            have heff_sa0_sa3 : HeapByteEff sa0 sa3 [] ["heap_ptr"] := by
              rw [hsa3_eq]; exact heff_alloc.locals_clock _ _
            have heff_sa0_sa3' : HeapByteEff sa0 sa3 [(cbufw.toNat, nlenw.toNat / 2 + 2)] ["heap_ptr"] :=
              heff_sa0_sa3.mono (fun _ hi _ => by simp at hi) (fun _ hg => hg)
            exact (heff_sa0_sa3'.trans heff_nlc).mono
              (fun i hi _ => by
                simp only [List.mem_singleton] at hi; subst hi
                have : globN sa0 "heap_ptr" = globN s "heap_ptr" := rfl
                exact Or.inr (Or.inr ⟨by omega, (hcb_cap_hi.trans hsa3_AR.2.2.1)⟩))
              (fun _ hg => hg)
          exact (hs0_eff.locals_clock sa0.locals sa0.clock).trans heff_nlc_empty
        have hsa4_cbuf : sa4.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
          rw [hloc_sa4]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsa3_cbuf,
            show ofString "clen" ≠ ofString "cbuf" by decide]
        have hsa4_clen : sa4.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
          rw [hloc_sa4]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hsa4_k : sa4.locals.lookup (ofString "k") = some (.val (.word kw)) := by
          rw [hloc_sa4]; simp [hsa3_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa1_k,
            show ofString "clen" ≠ ofString "k" by decide,
            show ofString "isl" ≠ ofString "k" by decide]
        have hsa4_node : sa4.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
          rw [hloc_sa4]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsa3_node,
            show ofString "clen" ≠ ofString "node" by decide]
        have hsa4_pay : sa4.locals.lookup (ofString "payload") = some (.val (.word 0)) := by
          rw [hloc_sa4]; simp [hsa3_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa1_pay,
            show ofString "clen" ≠ ofString "payload" by decide,
            show ofString "isl" ≠ ofString "payload" by decide]
        have hsa4_fr : sa4.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
          rw [hloc_sa4]; simp [hsa3_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa1_fr,
            show ofString "clen" ≠ ofString "fr" by decide,
            show ofString "isl" ≠ ofString "fr" by decide]
        change (evaluateHOLFiniteState sa4 _).1 = none at hn6
        have hcb_dom : sa4.memaddrs (panByteAlignHOL cbufw) := by
          have hsb : sourceBase ≤ cbufw.toNat := by rw [hcb_hp]; exact hAR.2.1
          have hcb_hi : cbufw.toNat < heapEnd := by
            have := hcb_cap_hi.trans (hsa3_AR.2.2.1.trans hhl_he); omega
          have hcb8 : cbufw.toNat % 8 = 0 := by rw [hcb_hp]; exact hAR.2.2.2.2.2.2.1
          have halign_eq : panByteAlignHOL cbufw = cbufw := by
            have ha := panByteAlign_toNat64 cbufw
            exact BitVec.eq_of_toNat_eq (by omega)
          rw [halign_eq, hsa4_AR.1.memaddrs, ordinaryDomain_iff]
          exact ⟨hcb8, hsb, hcb_hi⟩
        have hfb_ev : @evalHOLExact 64 F _ sa4.toExact (fun a => Classical.propDecidable (sa4.memaddrs a))
            (.loadByte (.var .local (ofString "cbuf"))) =
            some (.val (.word (BitVec.ofNat 64 (memB sa4 cbufw.toNat)))) := by
          simp only [evalHOLExact, hsa4_cbuf]
          unfold panMemLoadByteHOL; dsimp only
          have hbv : BitVec.ofNat 64 cbufw.toNat = cbufw :=
            BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cbufw.isLt])
          cases hm : sa4.memory (panByteAlignHOL cbufw) with
          | word cell =>
            simp only [hm, hcb_dom, ↓reduceIte, Option.map, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
            unfold memB
            rw [hbv, hm]
        have hfb_nat : (BitVec.ofNat 64 (memB sa4 cbufw.toNat)).toNat = memB sa4 cbufw.toNat := by
          unfold memB
          cases sa4.memory (panByteAlignHOL (BitVec.ofNat 64 cbufw.toNat)) with
          | word cell =>
            dsimp only
            have hlt : (panGetByteHOL (BitVec.ofNat 64 cbufw.toNat) cell sa4.be).toNat < 256 :=
              UInt8.toNat_lt _
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        set pK1Ite : ProgHOL 64 :=
          .ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
            (.decCall (ofString "vl") .one (ofString "rlp_value_encoded_len")
              [.load .one (.op .add [.var .local (ofString "node"), .const 48]),
               .load .one (.op .add [.var .local (ofString "node"), .const 56])]
              (.assign .local (ofString "payload")
                (.op .add [.var .local (ofString "payload"), .var .local (ofString "vl")])))
            .skip
        obtain ⟨elw, mid_el, hel_eq, hmid_el_g, hmid_el_m, hmid_el_l, heff_el, _, hdec_el⟩ :=
          eval_decCall_rlp_bytes_encoded_len_exact sa4 "el"
            (.loadByte (.var .local (ofString "cbuf"))) (.var .local (ofString "clen"))
            (BitVec.ofNat 64 (memB sa4 cbufw.toNat)) clenw
            (.seq (.assign .local (ofString "payload") (.var .local (ofString "el"))) pK1Ite)
            [] ["heap_ptr"]
            hsa4_c hsa4_AR hfb_ev (by simp [evalHOLExact, hsa4_clen]) (by omega)
            (by rw [hn6]; simp) (Or.inr hn6)
        rw [hfb_nat] at hel_eq
        have hn6_mid : (evaluateHOLFiniteState mid_el
            (.seq (.assign .local (ofString "payload") (.var .local (ofString "el"))) pK1Ite)).1 = none := by
          have := congrArg Prod.fst hdec_el; dsimp only at this; rw [← this]; exact hn6
        obtain ⟨hn7, hn8, hseq4⟩ := seq_none_rel mid_el
          (.assign .local (ofString "payload") (.var .local (ofString "el"))) pK1Ite hn6_mid
        have hmid_el_el : mid_el.locals.lookup (ofString "el") = some (.val (.word elw)) := by
          rw [hmid_el_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hmid_el_pay : mid_el.locals.lookup (ofString "payload") = some (.val (.word 0)) := by
          rw [hmid_el_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsa4_pay,
            show ofString "el" ≠ ofString "payload" by decide]
        let sa5 := (evaluateHOLFiniteState mid_el (.assign .local (ofString "payload") (.var .local (ofString "el")))).2
        have hsa5_eq : sa5 = setVarHOLFinite (ofString "payload") (.val (.word elw)) mid_el := by
          dsimp [sa5]; rw [evaluateHOLFiniteState_assign]
          simp [evalHOLExact, hmid_el_el, isValidValueHOLFinite, lookupKvarHOLFinite, hmid_el_pay,
            shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setVarHOLFinite]
        have hsa5_c : sa5.code = originalRuntimeCode := by
          rw [hsa5_eq]; exact heff_el.arena.1.code
        have hsa5_AR : ArenaReady sa5 := by
          rw [hsa5_eq]; exact ⟨guestInv_setVar _ _ _ heff_el.arena.1, heff_el.arena.2⟩
        have heff_s_sa5 : HeapByteEff s sa5 [] ["heap_ptr"] := by
          rw [hsa5_eq]; exact (heff_s_sa4.trans heff_el).locals_clock _ _
        have hsa5_pay : sa5.locals.lookup (ofString "payload") = some (.val (.word elw)) := by
          rw [hsa5_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsa5_k : sa5.locals.lookup (ofString "k") = some (.val (.word kw)) := by
          rw [hsa5_eq]; simp [setVarHOLFinite, hmid_el_l, HolFiniteMapExact.lookup_update, FUPDATE, hsa4_k,
            show ofString "payload" ≠ ofString "k" by decide, show ofString "el" ≠ ofString "k" by decide]
        have hsa5_node : sa5.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
          rw [hsa5_eq]; simp [setVarHOLFinite, hmid_el_l, HolFiniteMapExact.lookup_update, FUPDATE, hsa4_node,
            show ofString "payload" ≠ ofString "node" by decide, show ofString "el" ≠ ofString "node" by decide]
        have hsa5_cbuf : sa5.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
          rw [hsa5_eq]; simp [setVarHOLFinite, hmid_el_l, HolFiniteMapExact.lookup_update, FUPDATE, hsa4_cbuf,
            show ofString "payload" ≠ ofString "cbuf" by decide, show ofString "el" ≠ ofString "cbuf" by decide]
        have hsa5_clen : sa5.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
          rw [hsa5_eq]; simp [setVarHOLFinite, hmid_el_l, HolFiniteMapExact.lookup_update, FUPDATE, hsa4_clen,
            show ofString "payload" ≠ ofString "clen" by decide, show ofString "el" ≠ ofString "clen" by decide]
        have hsa5_fr : sa5.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
          rw [hsa5_eq]; simp [setVarHOLFinite, hmid_el_l, HolFiniteMapExact.lookup_update, FUPDATE, hsa4_fr,
            show ofString "payload" ≠ ofString "fr" by decide, show ofString "el" ≠ ofString "fr" by decide]
        have hmem_sa5_sa4 : sa5.memory = sa4.memory ∧ sa5.be = sa4.be := by
          rw [hsa5_eq]; exact ⟨hmid_el_m, heff_el.be⟩
        have hcb_ge : globN s "heap_ptr" ≤ cbufw.toNat := by
          have : globN sa0 "heap_ptr" = globN s "heap_ptr" := rfl
          omega
        have hcb_in_sa4 : Inside (cbufw.toNat, clenw.toNat) sourceBase (globN sa4 "heap_ptr") := by
          refine ⟨by have := hAR.2.1; omega, ?_⟩
          have : cbufw.toNat + clenw.toNat ≤ globN sa3 "heap_ptr" := by
            have : globN sa3 "heap_ptr" = globN sa1 "heap_ptr" := by rw [hsa3_eq]; rfl
            omega
          exact this.trans heff_nlc.hp_le
        have hcb_disj_nd : ∀ o ∈ nodeExtents s Nd, Disj (cbufw.toNat, clenw.toNat) o := by
          intro o ho
          have hcb_hi_hl : cbufw.toNat + clenw.toNat ≤ heapLimit :=
            hcb_in_sa4.2.trans hsa4_AR.2.2.1
          unfold nodeExtents at ho
          obtain ⟨m, hm, hm_iv⟩ := List.mem_flatMap.1 ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm_iv
          rcases hm_iv with rfl | rfl
          · rcases (hN.1 m hm).2.1 with h_in_hp | h_in_sp
            · obtain ⟨_, hhi⟩ := h_in_hp
              dsimp [nodeIvl] at hhi ⊢
              exact Or.inr (Or.inr (Or.inr (by omega)))
            · obtain ⟨hlo, _⟩ := h_in_sp
              have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
              dsimp [nodeIvl] at hlo ⊢
              have : heapLimit ≤ scratchStart := by decide
              exact Or.inr (Or.inr (Or.inl (by omega)))
          · unfold nodePath
            split_ifs with hp_cond
            · rcases (hN.1 m hm).2.2.2.2.2.2.1 hp_cond.1 with hz | ⟨_, hal_p, _, _⟩
              · exact absurd hz hp_cond.2
              · rcases hal_p with h_in_hp | h_in_sp
                · obtain ⟨_, hhi⟩ := h_in_hp
                  dsimp only at hhi
                  exact Or.inr (Or.inr (Or.inr (by omega)))
                · obtain ⟨hlo, _⟩ := h_in_sp
                  have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
                  dsimp only at hlo
                  have : heapLimit ≤ scratchStart := by decide
                  exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inr (Or.inl rfl)
        let sIte := (evaluateHOLFiniteState sa5 pK1Ite).2
        have hstate_s1 : s1 = ({ sIte with
            locals := (HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq sIte.locals
                  (ofString "el", sa4.locals.lookup (ofString "el")))
                (ofString "isl", sa1.locals.lookup (ofString "isl")))
              (ofString "nlen", s0.locals.lookup (ofString "nlen"))) } : PanSemStateFiniteExact 64 F) := by
          have hs1_a := (Prod.mk.inj h1).2.symm
          rw [hseq1] at hs1_a
          dsimp only [sa1] at hs1_a ⊢
          rw [evaluateHOLFiniteState_dec_total] at hs1_a
          dsimp only at hs1_a; rw [hev0] at hs1_a; dsimp only at hs1_a; rw [if_pos hsh_0] at hs1_a; dsimp only at hs1_a
          rw [hseq2, hseq3, hdec_el] at hs1_a; dsimp only at hs1_a
          rw [hseq4] at hs1_a; exact hs1_a
        change (evaluateHOLFiniteState sa5 _).1 = none at hn8
        have hcmp_k1 : @evalHOLExact 64 F _ sa5.toExact (fun a => Classical.propDecidable (sa5.memaddrs a))
            (.cmp .equal (.var .local (ofString "k")) (.const 1)) =
            some (.val (.word (if kw = 1 then 1 else 0))) := by
          simp [evalHOLExact, hsa5_k, Compiler.Encoders.Asm.wordCmpHOL]
        rw [evaluateHOLFiniteState_ite] at hn8
        rw [hcmp_k1] at hn8; dsimp only at hn8
        have hel_bound : elw.toNat ≤ nlenw.toNat / 2 + 10 := by
          have hb := (rlpBytesLenPure_bounds (memB sa4 cbufw.toNat) clenw.toNat).2.2
          omega
        have hcb_disj_kb : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
            Disj (cbufw.toNat, clenw.toNat) (bufferRegion s gs) := by
          intro gs hgs
          have hcb_hi_hl : cbufw.toNat + clenw.toNat ≤ heapLimit :=
            hcb_in_sa4.2.trans hsa4_AR.2.2.1
          rcases (hKS gs hgs).1 with h0 | hal_kb
          · exact Or.inr (Or.inl h0)
          · rcases hal_kb with ⟨_, hhi⟩ | ⟨hlo, _⟩
            · dsimp [bufferRegion] at hhi ⊢
              exact Or.inr (Or.inr (Or.inr (by omega)))
            · have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
              dsimp [bufferRegion] at hlo ⊢
              have : heapLimit ≤ scratchStart := by decide
              exact Or.inr (Or.inr (Or.inl (by omega)))
        by_cases hk1_eq : kw = 1
        · rw [if_pos hk1_eq, if_neg h10] at hn8
          have hkw1 : memW s nodew.toNat = 1 := by rw [← hkw_nat, hk1_eq]; rfl
          have hsz1 : nodeSize (memW s nodew.toNat) = 64 := by simp [nodeSize, hkw1]
          have hsa5_W_nd : WordsOK sa5 (nodeIvl s nodew.toNat) :=
            P3MptSet.wordsOK_transfer hAR.1 hsa5_AR.1 hw_nd
          have hnd_al8 : nodew.toNat % 8 = 0 := hw_nd.1
          have hmemW_sa5_nd : ∀ off, off % 8 = 0 → off + 8 ≤ 64 →
              memW sa5 (nodew.toNat + off) = memW s (nodew.toNat + off) := by
            intro off hoff8 hoff_le
            apply memW_eq_of_heapByteEff_disj hAR heff_s_sa5 (by omega)
            · rcases hal_nd with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
              · dsimp [nodeIvl] at hlo hhi
                exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
              · dsimp [nodeIvl] at hlo hhi
                exact Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩
            · omega
            · intro _ h; simp at h
          obtain ⟨vpw, hvp_ev, hvp_nat⟩ := eval_load_memW_of_wordsOK (off := 48) hsa5_W_nd (by decide)
            (by dsimp [nodeIvl]; omega) (by dsimp [nodeIvl]; omega)
            (e := .op .add [.var .local (ofString "node"), .const 48])
            (by simp [evalHOLExact, evalListHOLExact, hsa5_node, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
          obtain ⟨vlw, hvl_ev, hvl_nat⟩ := eval_load_memW_of_wordsOK (off := 56) hsa5_W_nd (by decide)
            (by dsimp [nodeIvl]; omega) (by dsimp [nodeIvl]; omega)
            (e := .op .add [.var .local (ofString "node"), .const 56])
            (by simp [evalHOLExact, evalListHOLExact, hsa5_node, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
          rw [hmemW_sa5_nd 48 (by decide) (by decide)] at hvp_nat
          rw [hmemW_sa5_nd 56 (by decide) (by decide)] at hvl_nat
          have hvl_lt : vlw.toNat < 2 ^ 40 := by rw [hvl_nat]; exact hleaf_v hkw1
          obtain ⟨vencw, mid_vl, hvenc_eq, hvp_dom, hmid_vl_g, hmid_vl_m, hmid_vl_l, heff_vl, _, hdec_vl⟩ :=
            eval_decCall_rlp_value_encoded_len_exact sa5 "vl"
              (.load .one (.op .add [.var .local (ofString "node"), .const 48]))
              (.load .one (.op .add [.var .local (ofString "node"), .const 56]))
              vpw vlw _ [] ["heap_ptr"] hsa5_c hsa5_AR hvp_ev hvl_ev (by omega)
              (by rw [hn8]; simp) (Or.inr hn8)
          let sa6 := setVarHOLFinite (ofString "payload") (.val (.word (elw + vencw))) mid_vl
          have hasg_vl : (evaluateHOLFiniteState mid_vl
              (.assign .local (ofString "payload")
                (.op .add [.var .local (ofString "payload"), .var .local (ofString "vl")]))).2 = sa6 := by
            rw [evaluateHOLFiniteState_assign]
            have hm_pay : mid_vl.locals.lookup (ofString "payload") = some (.val (.word elw)) := by
              rw [hmid_vl_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsa5_pay,
                show ofString "vl" ≠ ofString "payload" by decide]
            have hm_vl : mid_vl.locals.lookup (ofString "vl") = some (.val (.word vencw)) := by
              rw [hmid_vl_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            simp [sa6, evalHOLExact, evalListHOLExact, hm_pay, hm_vl, wordOpHOL, wordOp,
              valueIsWord, valueWord, BitVec.add_zero, isValidValueHOLFinite, lookupKvarHOLFinite,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setVarHOLFinite]
          have hite_sa5 : sIte = ({ sa6 with locals :=
              (HolFiniteMapExact.resVarEq sa6.locals (ofString "vl", sa5.locals.lookup (ofString "vl"))) } :
              PanSemStateFiniteExact 64 F) := by
            change (evaluateHOLFiniteState sa5 pK1Ite).2 = _
            dsimp only [pK1Ite]
            rw [evaluateHOLFiniteState_ite, hcmp_k1]; dsimp only
            rw [if_pos hk1_eq, if_neg h10, hdec_vl]; dsimp only; rw [hasg_vl]
          rw [hite_sa5] at hstate_s1; dsimp only at hstate_s1
          have heff_s_s1 : HeapByteEff s s1 [] ["heap_ptr"] := by
            rw [hstate_s1]; exact ((heff_s_sa5.trans heff_vl).locals_clock _ _).locals_clock _ _
          have hs1_m_sa4 : s1.memory = sa4.memory ∧ s1.be = sa4.be := by
            rw [hstate_s1]; exact ⟨hmid_vl_m.trans hmem_sa5_sa4.1, heff_vl.be.trans hmem_sa5_sa4.2⟩
          have hcb_b_s1 : memB s1 cbufw.toNat = memB sa4 cbufw.toNat := by
            unfold memB; rw [hs1_m_sa4.1, hs1_m_sa4.2]
          have hvenc_bound : vencw.toNat ≤ vlw.toNat + 9 :=
            hvenc_eq.trans_le ((rlpBytesLenPure_bounds _ vlw.toNat).2.2)
          have hpay_nat : (elw + vencw).toNat = elw.toNat + vencw.toNat := by
            rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
          refine ⟨cbufw, clenw, elw + vencw, ?_, ?_, ?_, ?_, by omega, heff_s_s1,
            fun h3 => by omega, ?_, fun h2 => by omega⟩
          · rw [hstate_s1, resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide),
              resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sa6, setVarHOLFinite, hmid_vl_l, HolFiniteMapExact.lookup_update, FUPDATE, hsa5_fr,
              show ofString "payload" ≠ ofString "fr" by decide, show ofString "vl" ≠ ofString "fr" by decide]
          · rw [hstate_s1, resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide),
              resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sa6, setVarHOLFinite, hmid_vl_l, HolFiniteMapExact.lookup_update, FUPDATE, hsa5_cbuf,
              show ofString "payload" ≠ ofString "cbuf" by decide, show ofString "vl" ≠ ofString "cbuf" by decide]
          · rw [hstate_s1, resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide),
              resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sa6, setVarHOLFinite, hmid_vl_l, HolFiniteMapExact.lookup_update, FUPDATE, hsa5_clen,
              show ofString "payload" ≠ ofString "clen" by decide, show ofString "vl" ≠ ofString "clen" by decide]
          · rw [hstate_s1, resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide),
              resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sa6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          · intro _
            have hhp_le : globN sa4 "heap_ptr" ≤ globN s1 "heap_ptr" := by
              rw [hstate_s1]; change globN sa4 "heap_ptr" ≤ globN mid_vl "heap_ptr"
              have hhp_sa5 : globN sa5 "heap_ptr" = globN mid_el "heap_ptr" := by
                rw [hsa5_eq]; rfl
              exact heff_el.hp_le.trans (hhp_sa5 ▸ heff_vl.hp_le)
            refine ⟨hcl1, by rw [← hnlen_nat]; exact hcl_bound,
              ⟨hcb_in_sa4.1, hcb_in_sa4.2.trans hhp_le⟩, hcb_disj_nd, hcb_disj_kb, ?_, ?_⟩
            · rw [hpay_nat, hel_eq, hcb_b_s1, hvenc_eq, ← hvl_nat]
              have h128_le : rlpBytesLenPure 128 vlw.toNat ≤
                  rlpBytesLenPure (if 0 < vlw.toNat then memB sa5 vpw.toNat else 0) vlw.toNat + 1 := by
                by_cases hv1 : vlw.toNat = 1
                · rw [hv1]; unfold rlpBytesLenPure rlpHeaderLenPure; split_ifs <;> omega
                · unfold rlpBytesLenPure
                  rw [if_neg (by omega), if_neg (by omega)]
                  omega
              omega
            · intro hpos
              rw [← hvl_nat] at hpos
              have hbv_vp : BitVec.ofNat 64 (memW s (nodew.toNat + 48)) = vpw := by
                rw [← hvp_nat]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt vpw.isLt])
              rw [hbv_vp]; exact heff_s_sa5.memaddrs ▸ hvp_dom hpos
        · rw [if_neg hk1_eq] at hn8
          have hkw2 : memW s nodew.toNat = 2 := by
            have : kw.toNat ≠ 1 := fun h => hk1_eq (BitVec.eq_of_toNat_eq h)
            rcases hk12 with h1 | h2
            · exfalso; exact this (by rw [hkw_nat, h1])
            · exact h2
          have hite_sa5 : sIte = sa5 := by
            change (evaluateHOLFiniteState sa5 pK1Ite).2 = sa5
            dsimp only [pK1Ite]
            rw [evaluateHOLFiniteState_ite, hcmp_k1]; dsimp only
            rw [if_neg hk1_eq]; simp [evaluateHOLFiniteState_skip]
          rw [hite_sa5] at hstate_s1
          have heff_s_s1 : HeapByteEff s s1 [] ["heap_ptr"] := by
            rw [hstate_s1]; exact heff_s_sa5.locals_clock _ _
          have hcb_b_s1 : memB s1 cbufw.toNat = memB sa4 cbufw.toNat := by
            have hms1 : s1.memory = sa4.memory ∧ s1.be = sa4.be := by
              rw [hstate_s1]; exact ⟨hmem_sa5_sa4.1, hmem_sa5_sa4.2⟩
            unfold memB; rw [hms1.1, hms1.2]
          refine ⟨cbufw, clenw, elw, ?_, ?_, ?_, ?_, by omega, heff_s_s1,
            fun h3 => by omega, fun h1 => by omega, ?_⟩
          · rw [hstate_s1, resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide),
              resVarEq_lookup_ne _ _ _ _ (by decide)]
            exact hsa5_fr
          · rw [hstate_s1, resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide),
              resVarEq_lookup_ne _ _ _ _ (by decide)]
            exact hsa5_cbuf
          · rw [hstate_s1, resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide),
              resVarEq_lookup_ne _ _ _ _ (by decide)]
            exact hsa5_clen
          · rw [hstate_s1, resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide),
              resVarEq_lookup_ne _ _ _ _ (by decide)]
            exact hsa5_pay
          · intro _
            have hhp_le : globN sa4 "heap_ptr" ≤ globN s1 "heap_ptr" := by
              rw [hstate_s1]; change globN sa4 "heap_ptr" ≤ globN sa5 "heap_ptr"
              rw [hsa5_eq]; exact heff_el.hp_le
            exact ⟨hcl1, by rw [← hnlen_nat]; exact hcl_bound,
              ⟨hcb_in_sa4.1, hcb_in_sa4.2.trans hhp_le⟩, hcb_disj_nd, hcb_disj_kb,
              by rw [hel_eq, hcb_b_s1]⟩
    obtain ⟨cbufw, clenw, payw, hs1_fr, hs1_cbuf, hs1_clen, hs1_pay, hpay_lt,
      heff_s1, hk3_p, hk1_p, hk2_p⟩ := hs1_props
    have hs1_AR : ArenaReady s1 := heff_s1.arena
    have hfr_hi : frw.toNat + 48 ≤ heapEnd := hfr_in.2.trans hse
    have hs1_fr_W : WordsOK s1 (frw.toNat, 48) :=
      P3MptSet.wordsOK_transfer hAR.1 hs1_AR.1 hfr_W
    obtain ⟨hn_st1, hl_st1, hg_st1, hw24_st1, hmem_st1, heff_st1⟩ :=
      eval_store_memW_at (base := frw) (w := cbufw) (off := 24) (len := 48)
        (Rl := [(frw.toNat + 24, 24)]) (gw := ["heap_ptr"])
        hs1_AR hs1_fr_W (by decide) (by decide) hfr_hi
        ⟨(frw.toNat + 24, 24), List.Mem.head _, by omega, by omega⟩
        (dstExp := .op .add [.var .local (ofString "fr"), .const 24])
        (valExp := .var .local (ofString "cbuf"))
        (by simp [evalHOLExact, evalListHOLExact, hs1_fr, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
        (by simp [evalHOLExact, hs1_cbuf])
    let st1 := (evaluateHOLFiniteState s1
      (.store (.op .add [.var .local (ofString "fr"), .const 24]) (.var .local (ofString "cbuf")))).2
    have hl_st1' : st1.locals = s1.locals := hl_st1
    have hg_st1' : st1.globals = s1.globals := hg_st1
    have hst1_fr_W : WordsOK st1 (frw.toNat, 48) :=
      P3MptSet.wordsOK_transfer hAR.1 heff_st1.arena.1 hfr_W
    obtain ⟨hn_st2, hl_st2, hg_st2, hw32_st2, hmem_st2, heff_st2⟩ :=
      eval_store_memW_at (s := st1) (base := frw) (w := clenw) (off := 32) (len := 48)
        (Rl := [(frw.toNat + 24, 24)]) (gw := ["heap_ptr"])
        heff_st1.arena hst1_fr_W (by decide) (by decide) hfr_hi
        ⟨(frw.toNat + 24, 24), List.Mem.head _, by omega, by omega⟩
        (dstExp := .op .add [.var .local (ofString "fr"), .const 32])
        (valExp := .var .local (ofString "clen"))
        (by simp [evalHOLExact, evalListHOLExact, hl_st1', hs1_fr,
          wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
        (by simp [evalHOLExact, hl_st1', hs1_clen])
    let st2 := (evaluateHOLFiniteState st1
      (.store (.op .add [.var .local (ofString "fr"), .const 32]) (.var .local (ofString "clen")))).2
    have hl_st2' : st2.locals = s1.locals := hl_st2.trans hl_st1'
    have hg_st2' : st2.globals = s1.globals := hg_st2.trans hg_st1'
    have hst2_fr_W : WordsOK st2 (frw.toNat, 48) :=
      P3MptSet.wordsOK_transfer hAR.1 heff_st2.arena.1 hfr_W
    obtain ⟨hn_st3, hl_st3, hg_st3, hw40_st3, hmem_st3, heff_st3⟩ :=
      eval_store_memW_at (s := st2) (base := frw) (w := payw) (off := 40) (len := 48)
        (Rl := [(frw.toNat + 24, 24)]) (gw := ["heap_ptr"])
        heff_st2.arena hst2_fr_W (by decide) (by decide) hfr_hi
        ⟨(frw.toNat + 24, 24), List.Mem.head _, by omega, by omega⟩
        (dstExp := .op .add [.var .local (ofString "fr"), .const 40])
        (valExp := .var .local (ofString "payload"))
        (by simp [evalHOLExact, evalListHOLExact, hl_st2', hs1_fr,
          wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
        (by simp [evalHOLExact, hl_st2', hs1_pay])
    let st3 := (evaluateHOLFiniteState st2
      (.store (.op .add [.var .local (ofString "fr"), .const 40]) (.var .local (ofString "payload")))).2
    have hpStores_ev : evaluateHOLFiniteState s1 pStores =
        (some (.returned (.val (.word 0))), emptyLocalsHOLFinite st3) := by
      dsimp only [pStores]
      rw [evaluateHOLFiniteState_seq_line780]
      have he1 : evaluateHOLFiniteState s1
          (.store (.op .add [.var .local (ofString "fr"), .const 24]) (.var .local (ofString "cbuf"))) =
          (none, st1) := Prod.ext hn_st1 rfl
      rw [he1]; dsimp only
      rw [evaluateHOLFiniteState_seq_line780]
      have he2 : evaluateHOLFiniteState st1
          (.store (.op .add [.var .local (ofString "fr"), .const 32]) (.var .local (ofString "clen"))) =
          (none, st2) := Prod.ext hn_st2 rfl
      rw [he2]; dsimp only
      rw [evaluateHOLFiniteState_seq_line780]
      have he3 : evaluateHOLFiniteState st2
          (.store (.op .add [.var .local (ofString "fr"), .const 40]) (.var .local (ofString "payload"))) =
          (none, st3) := Prod.ext hn_st3 rfl
      rw [he3]; dsimp only
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hpStores_ev] at hret
    injection hret with hv0
    injection hv0 with hv0'; subst hv0'
    have hseq_s0 : (evaluateHOLFiniteState s0 (.seq pIte pStores)).2 = emptyLocalsHOLFinite st3 := by
      rw [evaluateHOLFiniteState_seq_line780, h1]; dsimp only; rw [hpStores_ev]
    rw [hseq_s0]; dsimp only
    let eSt3 := emptyLocalsHOLFinite st3
    let postSt : PanSemStateFiniteExact 64 F := { eSt3 with
      locals := (HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq eSt3.locals
              (ofString "clen", (setVarHOLFinite (ofString "cbuf") (.val (.word 0))
                (setVarHOLFinite (ofString "payload") (.val (.word 0))
                  (setVarHOLFinite (ofString "k") (.val (.word kw)) s))).locals.lookup (ofString "clen")))
            (ofString "cbuf", (setVarHOLFinite (ofString "payload") (.val (.word 0))
              (setVarHOLFinite (ofString "k") (.val (.word kw)) s)).locals.lookup (ofString "cbuf")))
          (ofString "payload", (setVarHOLFinite (ofString "k") (.val (.word kw)) s).locals.lookup (ofString "payload")))
        (ofString "k", s.locals.lookup (ofString "k"))) }
    change (.val (.word 0) : ValueHOL 64) = (.val (.word 0) : ValueHOL 64) ∧
      HeapByteEff s postSt [(frw.toNat + 24, 24)] ["heap_ptr"] ∧
      NodeHeap postSt Nd ∧
      nodeExtents postSt Nd = nodeExtents s Nd ∧
      KeccakBufsSafe postSt Nd ∧
      (∀ n ∈ Nd, ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
        memW postSt (n + off) = memW s (n + off)) ∧
      ValidRlpFrame postSt Nd frw.toNat
    have heff_s1_expanded : HeapByteEff s s1 [(frw.toNat + 24, 24)] ["heap_ptr"] :=
      heff_s1.mono (fun x hx => by simp at hx) (fun x hx => hx)
    have heff_post : HeapByteEff s postSt [(frw.toNat + 24, 24)] ["heap_ptr"] := by
      dsimp [postSt, emptyLocalsHOLFinite]
      exact ((((heff_s1_expanded.trans heff_st1).trans heff_st2).trans heff_st3).locals_clock _ _).locals_clock _ _
    have hpost_m : postSt.memory = st3.memory ∧ postSt.be = st3.be ∧ postSt.globals = s1.globals :=
      ⟨rfl, rfl, hg_st3.trans (hg_st2.trans hg_st1)⟩
    have hnd_disj_fr : ∀ n ∈ Nd, ∀ off, off + 8 ≤ nodeSize (memW s n) →
        Disj (n + off, 8) (frw.toNat + 24, 24) := by
      intro n hn off hoff
      have hin_n := (hN.1 n hn).2.2.1
      have hss : heapLimit ≤ scratchStart := by decide
      have hhi_n : n + nodeSize (memW s n) ≤ globN s "scratch_ptr" :=
        hin_n.2.trans (hss.trans (hAR.2.2.2.1.trans hAR.2.2.2.2.1))
      obtain ⟨hfr_lo, _⟩ := hfr_in
      dsimp only at hfr_lo
      exact Or.inr (Or.inr (Or.inl (by dsimp [nodeIvl] at hin_n; omega)))
    have hnd_memW_eq : ∀ n ∈ Nd, ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
        memW postSt (n + off) = memW s (n + off) := by
      intro n hn off hoff8 hoff_le
      obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
      have hn8 : n % 8 = 0 := hw_n.1
      apply memW_eq_of_heapByteEff_disj hAR heff_post (by omega)
      · rcases hal_n with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
        · exact Or.inl ⟨by dsimp [nodeIvl] at hlo; omega, by dsimp [nodeIvl] at hhi; omega⟩
        · exact Or.inr ⟨by dsimp [nodeIvl] at hlo; omega, by dsimp [nodeIvl] at hhi; omega⟩
      · have := hin_n.2.trans hhl_he; dsimp [nodeIvl] at this; omega
      · intro iv hiv _
        simp only [List.mem_singleton] at hiv; subst hiv
        exact hnd_disj_fr n hn off hoff_le
    have hag_post : AllocatorGrows s postSt := ⟨heff_post.hp_le, heff_post.sp_le⟩
    have hN_post : NodeHeap postSt Nd ∧ nodeExtents postSt Nd = nodeExtents s Nd := by
      apply nodeHeap_congr_cache hAR.1 heff_post.arena.1 hag_post hN
      · intro n hn k hk _ _ _
        have hsz_mod := nodeSize_mod8 (memW s n)
        exact hnd_memW_eq n hn (8 * k) (by omega) (by omega)
      · intro n hn
        have hsz_n := nodeSize_ge32 (memW s n)
        rw [hnd_memW_eq n hn 16 (by decide) (by omega)]
        exact (hN.1 n hn).2.2.2.2.2.2.2.1
      · intro n hn hk12 h40 j hj
        obtain ⟨_, _, _, _, _, _, hkey_n, _⟩ := hN.1 n hn
        rcases hkey_n hk12 with hz | ⟨_, hal_p, hin_p, _⟩
        · exact absurd hz h40
        · apply memB_eq_of_heapByteEff_disj hAR heff_post
          · rcases hal_p with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
            · exact Or.inl ⟨by dsimp only at hlo; omega, by dsimp only at hhi; omega⟩
            · exact Or.inr ⟨by dsimp only at hlo; omega, by dsimp only at hhi; omega⟩
          · have := hin_p.2.trans hhl_he; dsimp only at this; omega
          · intro iv hiv _
            simp only [List.mem_singleton] at hiv; subst hiv
            have hss : heapLimit ≤ scratchStart := by decide
            have hhi_p := hin_p.2.trans (hss.trans (hAR.2.2.2.1.trans hAR.2.2.2.2.1))
            obtain ⟨hfr_lo, _⟩ := hfr_in; dsimp only at hfr_lo hhi_p
            exact Or.inr (Or.inr (Or.inr (by omega)))
    have hkp_eq : globN postSt "keccak_pad" = globN s "keccak_pad" := by
      unfold globN; rw [← heff_post.globals (ofString "keccak_pad") (by decide)]
    have hks_eq : globN postSt "keccak_st" = globN s "keccak_st" := by
      unfold globN; rw [← heff_post.globals (ofString "keccak_st") (by decide)]
    have hKS_post : KeccakBufsSafe postSt Nd :=
      keccakBufsSafe_of_grows hKS hag_post
        (fun gs hgs => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
          rcases hgs with rfl | rfl
          · simp [bufferRegion, hkp_eq]
          · simp [bufferRegion, hks_eq])
        hN_post.2
    have hw_fr_post : memW postSt (frw.toNat + 8) = nodew.toNat ∧
        memW postSt (frw.toNat + 16) = memW s (frw.toNat + 16) ∧
        memW postSt (frw.toNat + 24) = cbufw.toNat ∧
        memW postSt (frw.toNat + 32) = clenw.toNat ∧
        memW postSt (frw.toNat + 40) = payw.toNat := by
      obtain ⟨hfr_lo, hfr_hi⟩ := hfr_in
      have hfr8_al : frw.toNat % 8 = 0 := hfr_W.1
      dsimp only at hfr_lo hfr_hi
      have hw8 : memW postSt (frw.toNat + 8) = memW s (frw.toNat + 8) :=
        memW_eq_of_heapByteEff_disj hAR heff_post (by omega)
          (Or.inr ⟨by omega, by omega⟩) (by omega)
          (fun iv hiv _ => by simp at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by omega))))
      have hw16 : memW postSt (frw.toNat + 16) = memW s (frw.toNat + 16) :=
        memW_eq_of_heapByteEff_disj hAR heff_post (by omega)
          (Or.inr ⟨by omega, by omega⟩) (by omega)
          (fun iv hiv _ => by simp at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by omega))))
      have hw24 : memW postSt (frw.toNat + 24) = cbufw.toNat := by
        unfold memW; rw [hpost_m.1, hmem_st3 _ (by omega) (by omega),
          hmem_st2 _ (by omega) (by omega)]; exact hw24_st1
      have hw32 : memW postSt (frw.toNat + 32) = clenw.toNat := by
        unfold memW; rw [hpost_m.1, hmem_st3 _ (by omega) (by omega)]; exact hw32_st2
      have hw40 : memW postSt (frw.toNat + 40) = payw.toNat := hw40_st3
      exact ⟨hw8.trans hfr8_eq, hw16, hw24, hw32, hw40⟩
    refine ⟨rfl, heff_post, hN_post.1, hN_post.2, hKS_post, hnd_memW_eq, ?_⟩
    obtain ⟨hw8_p, hw16_p, hw24_p, hw32_p, hw40_p⟩ := hw_fr_post
    have hsp_eq : globN postSt "scratch_ptr" = globN s "scratch_ptr" := by
      unfold globN; rw [← heff_post.globals (ofString "scratch_ptr") (by decide)]
    have hhp_post_s1 : globN postSt "heap_ptr" = globN s1 "heap_ptr" := by
      unfold globN; rw [hpost_m.2.2]
    have hfr_W_post : WordsOK postSt (frw.toNat, 48) :=
      P3MptSet.wordsOK_transfer hAR.1 heff_post.arena.1 hfr_W
    have hk_post_eq : memW postSt nodew.toNat = memW s nodew.toNat :=
      hnd_memW_eq nodew.toNat hnode_in 0 (by decide) (by omega)
    have hcb_b_post_s1 : (memW s nodew.toNat = 1 ∨ memW s nodew.toNat = 2) →
        1 ≤ clenw.toNat → Inside (cbufw.toNat, clenw.toNat) sourceBase (globN s1 "heap_ptr") →
        memB postSt cbufw.toNat = memB s1 cbufw.toNat := by
      intro _ hcl1 hcb_in
      obtain ⟨hcb_lo, hcb_hi⟩ := hcb_in
      dsimp only at hcb_lo hcb_hi
      have heff_s1_post : HeapByteEff s1 postSt [(frw.toNat + 24, 24)] ["heap_ptr"] := by
        dsimp [postSt, emptyLocalsHOLFinite]
        exact (((heff_st1.trans heff_st2).trans heff_st3).locals_clock _ _).locals_clock _ _
      apply memB_eq_of_heapByteEff_disj hs1_AR heff_s1_post
      · exact Or.inl ⟨by omega, by omega⟩
      · have := hs1_AR.2.2.1.trans hhl_he; omega
      · intro iv hiv _
        simp only [List.mem_singleton] at hiv; subst hiv
        have hss : heapLimit ≤ scratchStart := by decide
        have h1 := hs1_AR.2.2.1
        have h2 := hAR.2.2.2.1.trans hAR.2.2.2.2.1
        obtain ⟨hfr_lo, _⟩ := hfr_in; dsimp only at hfr_lo
        exact Or.inr (Or.inr (Or.inr (by omega)))
    refine ⟨hfr_W.1, by rw [hsp_eq]; exact hfr_in, hfr_W_post,
      by rw [hw8_p]; exact hnode_in,
      by rw [hw8_p, hk_post_eq]; exact hk1,
      by rw [hw8_p, hk_post_eq]; exact hk_le3,
      by rw [hw16_p]; exact hfr16_le,
      by rw [hw40_p]; exact hpay_lt,
      fun h3 => by rw [hw40_p]; exact hk3_p (by rwa [hw8_p, hk_post_eq] at h3),
      ?_, ?_⟩
    · intro h1_post
      have h1s : memW s nodew.toNat = 1 := by rwa [hw8_p, hk_post_eq] at h1_post
      have hsz1 : nodeSize (memW s nodew.toNat) = 64 := by simp [nodeSize, h1s]
      have hbuf_post_eq : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
          bufferRegion postSt gs = bufferRegion s gs := by
        intro gs hgs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
        rcases hgs with rfl | rfl
        · simp [bufferRegion, hkp_eq]
        · simp [bufferRegion, hks_eq]
      obtain ⟨hcl1, hcl_hi, hcb_in, hcb_disj, hcb_kb, hpay1, hdom1⟩ := hk1_p h1s
      have hcb_b := hcb_b_post_s1 (Or.inl h1s) hcl1 hcb_in
      have hn40_eq := hnd_memW_eq nodew.toNat hnode_in 40 (by decide) (by omega)
      have hn48_eq := hnd_memW_eq nodew.toNat hnode_in 48 (by decide) (by omega)
      have hn56_eq := hnd_memW_eq nodew.toNat hnode_in 56 (by decide) (by omega)
      refine ⟨by rw [hw32_p]; exact hcl1,
        by rw [hw32_p, hw8_p, hn40_eq]; exact hcl_hi,
        by rw [hw24_p, hw32_p, hhp_post_s1]; exact hcb_in,
        fun o ho => by rw [hN_post.2] at ho; rw [hw24_p, hw32_p]; exact hcb_disj o ho,
        fun gs hgs => by rw [hbuf_post_eq gs hgs, hw24_p, hw32_p]; exact hcb_kb gs hgs,
        ?_, ?_⟩
      · rw [hw40_p, hw24_p, hw32_p, hw8_p, hn56_eq, hcb_b]
        exact hpay1
      · intro hpos
        rw [hw8_p, hn56_eq] at hpos
        rw [hw8_p, hn48_eq]
        exact heff_post.memaddrs.symm ▸ hdom1 hpos
    · intro h2_post
      have h2s : memW s nodew.toNat = 2 := by rwa [hw8_p, hk_post_eq] at h2_post
      have hsz2 : nodeSize (memW s nodew.toNat) = 56 := by simp [nodeSize, h2s]
      obtain ⟨hcl1, hcl_hi, hcb_in, hcb_disj, hcb_kb, hpay2⟩ := hk2_p h2s
      have hcb_b := hcb_b_post_s1 (Or.inr h2s) hcl1 hcb_in
      have hn40_eq := hnd_memW_eq nodew.toNat hnode_in 40 (by decide) (by omega)
      have hbuf_post_eq : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
          bufferRegion postSt gs = bufferRegion s gs := by
        intro gs hgs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
        rcases hgs with rfl | rfl
        · simp [bufferRegion, hkp_eq]
        · simp [bufferRegion, hks_eq]
      refine ⟨by rw [hw32_p]; exact hcl1,
        by rw [hw32_p, hw8_p, hn40_eq]; exact hcl_hi,
        by rw [hw24_p, hw32_p, hhp_post_s1]; exact hcb_in,
        fun o ho => by rw [hN_post.2] at ho; rw [hw24_p, hw32_p]; exact hcb_disj o ho,
        fun gs hgs => by rw [hbuf_post_eq gs hgs, hw24_p, hw32_p]; exact hcb_kb gs hgs,
        by rw [hw40_p, hw24_p, hw32_p, hcb_b, hpay2]⟩

private theorem eval_call__node_rlp_begin_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (frExp nodeExp : ExpHOL 64)
    (frw nodew : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hN : NodeHeap s Nd)
    (hKS : KeccakBufsSafe s Nd)
    (hfr_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
      some (.val (.word frw)))
    (hnode_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
      some (.val (.word nodew)))
    (hfr_in : Inside (frw.toNat, 48) (globN s "scratch_ptr") scratchEnd)
    (hfr_W : WordsOK s (frw.toNat, 48))
    (hnode_in : nodew.toNat ∈ Nd)
    (hk1 : 1 ≤ memW s nodew.toNat)
    (hfr8_eq : memW s (frw.toNat + 8) = nodew.toNat)
    (hfr16_le : memW s (frw.toNat + 16) ≤ 16)
    (hnone : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "_node_rlp_begin") [frExp, nodeExp])).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "_node_rlp_begin") [frExp, nodeExp])).2
    post.locals = s.locals ∧
    HeapByteEff s post [(frw.toNat + 24, 24)] ["heap_ptr"] ∧
    NodeHeap post Nd ∧
    nodeExtents post Nd = nodeExtents s Nd ∧
    KeccakBufsSafe post Nd ∧
    (∀ n ∈ Nd, ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
      memW post (n + off) = memW s (n + off)) ∧
    memW post frw.toNat = memW s frw.toNat ∧
    ValidRlpFrame post Nd frw.toNat := by
  intro post; dsimp only [post]
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [frExp, nodeExp] = some [.val (.word frw), .val (.word nodew)] := by
    simp [evalListHOLFinite, evalListHOLExact, hfr_ev, hnode_ev]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "_node_rlp_begin")
    (ofString "fr") (ofString "node")
    (sourceFnBody Guest.Software.guestFn__node_rlp_begin) frw nodew
    (by decide) (by rw [hc]; exact lookup__node_rlp_begin)
  simp only [ha, hlk] at hnone ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnone
  · simp only [hcz, ↓reduceIte] at hnone ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "fr", ValueHOL.val (.word frw))).update
      (ofString "node", ValueHOL.val (.word nodew))
    set ent := callEntryStateHOLFinite s cmap
    have hent_fr : ent.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "node" ≠ ofString "fr" by decide]
    have hent_node : ent.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hent_AR : ArenaReady ent := localsFree_arenaReady s _ _ hAR
    rcases hcal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn__node_rlp_begin) with ⟨rc, sc⟩
    simp only [hcal] at hnone ⊢
    cases rc with
    | none => simp at hnone
    | some rc' =>
      cases rc' with
      | returned vc =>
        obtain ⟨rfl, heff_ent, hN_sc, hext_sc, hKS_sc, hnd_w, hv_sc⟩ :=
          eval__node_rlp_begin_returned ent Nd frw nodew vc hc hent_AR hN hKS
            hent_fr hent_node hfr_in hfr_W hnode_in hk1 hfr8_eq hfr16_le (by rw [hcal])
        rw [hcal] at heff_ent hN_sc hext_sc hKS_sc hnd_w hv_sc
        dsimp only at heff_ent hN_sc hext_sc hKS_sc hnd_w hv_sc
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only; rw [if_pos hsh]; dsimp only
        have heff0 : HeapByteEff s ent [(frw.toNat + 24, 24)] ["heap_ptr"] :=
          (HeapByteEff.refl hAR [(frw.toNat + 24, 24)] ["heap_ptr"]).locals_clock ent.locals ent.clock
        have heff_out : HeapByteEff s { sc with locals := s.locals } [(frw.toNat + 24, 24)] ["heap_ptr"] :=
          (heff0.trans heff_ent).locals_clock s.locals sc.clock
        have hse : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
        obtain ⟨hfr_lo, hfr_hi⟩ := hfr_in; dsimp only at hfr_lo hfr_hi
        have hw0_eq : memW { sc with locals := s.locals } frw.toNat = memW s frw.toNat :=
          memW_eq_of_heapByteEff_disj hAR heff_out hfr_W.1
            (Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩)
            (by omega)
            (fun iv hiv _ => by simp at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by omega))))
        have hW_out : WordsOK { sc with locals := s.locals } (frw.toNat, 48) :=
          P3MptSet.wordsOK_transfer heff_ent.arena.1 heff_out.arena.1 hv_sc.2.2.1
        have hv_out : ValidRlpFrame { sc with locals := s.locals } Nd frw.toNat := by
          obtain ⟨h1, h2, _, h4⟩ := hv_sc
          exact ⟨h1, h2, hW_out, h4⟩
        exact ⟨rfl, heff_out, hN_sc, hext_sc, hKS_sc, hnd_w, hw0_eq, hv_out⟩
      | _ => simp at hnone

/-! ## Milestone 2b: `_node_rlp_finish` write-frame and invariant preservation -/

private def finishLenLoopBody : ProgHOL 64 :=
  .decCall (ofString "rl2") .one (ofString "node_ref_len")
    [.load .one (.op .add [.var .local (ofString "node"), .const 32,
      .panop .mul [.var .local (ofString "i"), .const 8]])]
    (.seq
      (.assign .local (ofString "payload")
        (.op .add [.var .local (ofString "payload"), .var .local (ofString "rl2")]))
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const 1])))

private def finishLenLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.const 16)) finishLenLoopBody

private def branchRefsLenSum {F : Type} (s : PanSemStateFiniteExact 64 F)
    (node : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    nodeRefBytes s (memW s (node + 32 + 8 * (16 - (k + 1)))) + branchRefsLenSum s node k

private theorem branchRefsLenSum_le {F : Type} (s : PanSemStateFiniteExact 64 F)
    (node : Nat) : ∀ k, branchRefsLenSum s node k ≤ 33 * k
  | 0 => by simp [branchRefsLenSum]
  | k + 1 => by
    have h1 := nodeRefBytes_le33 s (memW s (node + 32 + 8 * (16 - (k + 1))))
    have h2 := branchRefsLenSum_le s node k
    unfold branchRefsLenSum
    omega

private theorem branchRefsLenSum_congr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {node : Nat}
    (hbr : ∀ i < 16, RootIn Nd (memW s (node + 32 + 8 * i)))
    (hch_eq : ∀ i < 16, memW post (node + 32 + 8 * i) = memW s (node + 32 + 8 * i))
    (hnrb_eq : ∀ m, RootIn Nd m → nodeRefBytes post m = nodeRefBytes s m) :
    ∀ k ≤ 16, branchRefsLenSum post node k = branchRefsLenSum s node k
  | 0, _ => rfl
  | k + 1, hk => by
    have hi : 16 - (k + 1) < 16 := by omega
    simp only [branchRefsLenSum, hch_eq _ hi, hnrb_eq _ (hbr _ hi),
      branchRefsLenSum_congr hbr hch_eq hnrb_eq k (by omega)]

private theorem eval_finishLenLoop_none {F : Type} :
    ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (nodew frw kw payw cbufw clenw iw : BitVec 64),
      s.clock ≤ clk →
      s.code = originalRuntimeCode →
      ArenaReady s →
      NodeHeap s Nd →
      nodew.toNat ∈ Nd →
      memW s nodew.toNat = 3 →
      iw.toNat ≤ 16 →
      payw.toNat ≤ 33 * iw.toNat →
      s.locals.lookup (ofString "node") = some (.val (.word nodew)) →
      s.locals.lookup (ofString "fr") = some (.val (.word frw)) →
      s.locals.lookup (ofString "k") = some (.val (.word kw)) →
      s.locals.lookup (ofString "payload") = some (.val (.word payw)) →
      s.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) →
      s.locals.lookup (ofString "clen") = some (.val (.word clenw)) →
      s.locals.lookup (ofString "i") = some (.val (.word iw)) →
      (evaluateHOLFiniteState s finishLenLoop).1 = none →
      let post := (evaluateHOLFiniteState s finishLenLoop).2
      ∃ payw' : BitVec 64,
        payw'.toNat = payw.toNat + branchRefsLenSum s nodew.toNat (16 - iw.toNat) ∧
        post.globals = s.globals ∧
        post.memory = s.memory ∧
        post.be = s.be ∧
        HeapByteEff s post [] ["heap_ptr"] ∧
        post.locals.lookup (ofString "node") = some (.val (.word nodew)) ∧
        post.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
        post.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
        post.locals.lookup (ofString "payload") = some (.val (.word payw')) ∧
        post.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) ∧
        post.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
  intro clk
  induction clk with
  | zero =>
    intro s Nd nodew frw kw payw cbufw clenw iw hclk _ hAR _ _ _ hi16 _ hln hlf hlk hlp hlcb hlcl hli hnone post
    dsimp only [post]
    rw [finishLenLoop, evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    have hcnd : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.const 16)) =
        some (.val (.word (if iw.toNat < 16 then 1 else 0))) := by
      have h16 : (16#64).toNat = 16 := rfl
      simp [evalHOLFinite, evalHOLExact, hli, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw 16#64 (by omega) (by decide), h16]
    rw [hcnd] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hlt : iw.toNat < 16
    · have hk0 : s.clock = 0 := by omega
      simp [hlt, hk0] at hnone
    · simp only [hlt, ↓reduceIte]
      have hi_eq : 16 - iw.toNat = 0 := by omega
      exact ⟨payw, by rw [hi_eq]; simp [branchRefsLenSum], rfl, rfl, rfl,
        HeapByteEff.refl hAR [] ["heap_ptr"], hln, hlf, hlk, hlp, hlcb, hlcl⟩
  | succ clk ih =>
    intro s Nd nodew frw kw payw cbufw clenw iw hclk hc hAR hN hnode_in hk3 hi16 hpay_le
      hln hlf hlk hlp hlcb hlcl hli hnone post
    dsimp only [post]
    rw [finishLenLoop, evaluateHOLFiniteState_while_fixClockRewrite, ← finishLenLoop] at hnone ⊢
    have hcnd : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.const 16)) =
        some (.val (.word (if iw.toNat < 16 then 1 else 0))) := by
      have h16 : (16#64).toNat = 16 := rfl
      simp [evalHOLFinite, evalHOLExact, hli, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw 16#64 (by omega) (by decide), h16]
    rw [hcnd] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hlt : iw.toNat < 16
    · have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos hlt, if_pos h10] at hnone ⊢
      by_cases hcz : s.clock = 0
      · simp [hcz] at hnone
      · rw [if_neg hcz] at hnone ⊢
        let sd := decClockHOLFinite s
        have hsd_AR : ArenaReady sd := localsFree_arenaReady s s.locals (s.clock - 1) hAR
        have h264 : heapLimit < 2 ^ 64 := by decide
        obtain ⟨_, _, hin_nd, hw_nd, _, hbr_nd, _⟩ := hN.1 nodew.toNat hnode_in
        have hsz3 : nodeSize (memW s nodew.toNat) = 176 := by simp [nodeSize, hk3]
        have hsd_W_nd : WordsOK sd (nodeIvl s nodew.toNat) :=
          P3MptSet.wordsOK_transfer hAR.1 hsd_AR.1 hw_nd
        have hmul_eq : iw * (8 : BitVec 64) = BitVec.ofNat 64 (8 * iw.toNat) := by
          apply BitVec.eq_of_toNat_eq
          have h8 : ((8 : BitVec 64)).toNat = 8 := rfl
          rw [BitVec.toNat_mul, h8, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hoff_eq : BitVec.ofNat 64 32 + iw * BitVec.ofNat 64 8 = BitVec.ofNat 64 (32 + 8 * iw.toNat) := by
          change (32 : BitVec 64) + iw * 8 = BitVec.ofNat 64 (32 + 8 * iw.toNat)
          apply BitVec.eq_of_toNat_eq
          have h32 : ((32 : BitVec 64)).toNat = 32 := rfl
          rw [hmul_eq, BitVec.toNat_add, h32, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        obtain ⟨chw, hch_ev, hch_nat⟩ :=
          eval_load_memW_of_wordsOK (s := sd) (base := nodew) (off := 32 + 8 * iw.toNat)
            hsd_W_nd (by omega) (by change 32 + 8 * iw.toNat + 8 ≤ nodeSize (memW s nodew.toNat); omega)
            (by have := hin_nd.2; dsimp [nodeIvl] at this; omega)
            (e := .op .add [.var .local (ofString "node"), .const 32,
              .panop .mul [.var .local (ofString "i"), .const 8]])
            (by
              have hsd_n : sd.locals.lookup (ofString "node") = some (.val (.word nodew)) := hln
              have hsd_i : sd.locals.lookup (ofString "i") = some (.val (.word iw)) := hli
              simp [evalHOLExact, evalListHOLExact, hsd_n, hsd_i,
                wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, BitVec.add_zero, hoff_eq])
        have hch_nat' : chw.toNat = memW s (nodew.toNat + 32 + 8 * iw.toNat) := by
          have : nodew.toNat + (32 + 8 * iw.toNat) = nodew.toNat + 32 + 8 * iw.toNat := by omega
          change chw.toNat = memW s (nodew.toNat + (32 + 8 * iw.toNat)) at hch_nat
          simpa [this] using hch_nat
        have hch_root : RootIn Nd chw.toNat := by rw [hch_nat']; exact hbr_nd hk3 iw.toNat hlt
        have hclk_b := evaluateHOLFiniteState_clock_le sd finishLenLoopBody
        rcases hb_ev : evaluateHOLFiniteState (decClockHOLFinite s) finishLenLoopBody with ⟨rb, sb⟩
        have hb_ev' : evaluateHOLFiniteState sd finishLenLoopBody = (rb, sb) := hb_ev
        simp only [hb_ev] at hnone ⊢
        rw [hb_ev'] at hclk_b
        have hnt_b : rb ≠ some .timeOut := by
          rintro rfl; simp [fixClockHOLFinite] at hnone
        have hdc := eval_decCall_node_ref_len_exact sd Nd "rl2"
          (.load .one (.op .add [.var .local (ofString "node"), .const 32,
            .panop .mul [.var .local (ofString "i"), .const 8]]))
          chw
          (.seq
            (.assign .local (ofString "payload")
              (.op .add [.var .local (ofString "payload"), .var .local (ofString "rl2")]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))
          [] ["heap_ptr"] hc hsd_AR hN hch_root hch_ev
          (by change (evaluateHOLFiniteState sd finishLenLoopBody).1 ≠ _; rw [hb_ev']; exact hnt_b)
        dsimp only at hdc
        change (∃ _ _, _) ∨ _ at hdc
        rcases hdc with ⟨rlw, mid, hrl_eq, hmid_g, hmid_m, hmid_l, heff_mid, _, hdc_eq⟩ |
            ⟨hne_b, _, hnb_b, hnc_b, _⟩
        · change evaluateHOLFiniteState sd finishLenLoopBody = _ at hdc_eq
          have hmid_pay : mid.locals.lookup (ofString "payload") = some (.val (.word payw)) := by
            rw [hmid_l]; simp [sd, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlp,
              show ofString "rl2" ≠ ofString "payload" by decide]
          have hmid_rl2 : mid.locals.lookup (ofString "rl2") = some (.val (.word rlw)) := by
            rw [hmid_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hmid_i : mid.locals.lookup (ofString "i") = some (.val (.word iw)) := by
            rw [hmid_l]; simp [sd, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hli,
              show ofString "rl2" ≠ ofString "i" by decide]
          have hasg_ev : evaluateHOLFiniteState mid
              (.seq
                (.assign .local (ofString "payload")
                  (.op .add [.var .local (ofString "payload"), .var .local (ofString "rl2")]))
                (.assign .local (ofString "i")
                  (.op .add [.var .local (ofString "i"), .const 1]))) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1)))
                (setVarHOLFinite (ofString "payload") (.val (.word (payw + rlw))) mid)) := by
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            have hne_pi : ofString "payload" ≠ ofString "i" := by decide
            simp [evalHOLExact, evalListHOLExact, hmid_pay, hmid_rl2, hmid_i, hne_pi, Ne.symm hne_pi,
              wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero,
              isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
              setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              evaluateHOLFiniteState_assign]
          rw [hasg_ev] at hdc_eq
          rw [hb_ev'] at hdc_eq
          have hrb_none : rb = none := congrArg Prod.fst hdc_eq
          have hsb_eq : sb = { mid with
              locals := HolFiniteMapExact.resVarEq
                ((setVarHOLFinite (ofString "i") (.val (.word (iw + 1)))
                  (setVarHOLFinite (ofString "payload") (.val (.word (payw + rlw))) mid)).locals)
                (ofString "rl2", sd.locals.lookup (ofString "rl2")) } :=
            congrArg Prod.snd hdc_eq
          subst hrb_none
          dsimp only at hnone ⊢
          have hrl_le : rlw.toNat ≤ 33 := hrl_eq.trans_le (nodeRefBytes_le33 sd chw.toNat)
          have hpay_add_nat : (payw + rlw).toNat = payw.toNat + rlw.toNat := by
            rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
          have hiw1_nat : (iw + 1).toNat = iw.toNat + 1 := by
            have h1v : ((1 : BitVec 64)).toNat = 1 := rfl
            rw [BitVec.toNat_add, h1v]; exact Nat.mod_eq_of_lt (by omega)
          have hsb_g : sb.globals = s.globals := by rw [hsb_eq]; exact hmid_g
          have hsb_m : sb.memory = s.memory := by rw [hsb_eq]; exact hmid_m
          have hsb_be : sb.be = s.be := by rw [hsb_eq]; exact heff_mid.be
          have heff_s_sb : HeapByteEff s sb [] ["heap_ptr"] := by
            rw [hsb_eq]
            exact (((HeapByteEff.refl hAR [] ["heap_ptr"]).locals_clock sd.locals sd.clock).trans heff_mid).locals_clock _ _
          have hsb_c : sb.code = originalRuntimeCode := heff_s_sb.arena.1.code
          have hsb_N : NodeHeap sb Nd := by
            obtain ⟨hN', _⟩ := nodeHeap_of_heapByteEff_disj hAR hN heff_s_sb (by intro _ h; simp at h)
            exact hN'
          have hsb_node_k : memW sb nodew.toNat = 3 := by
            unfold memW; rw [hsb_m]; exact hk3
          have hsb_ln : sb.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hln,
              show ofString "i" ≠ ofString "node" by decide,
              show ofString "payload" ≠ ofString "node" by decide,
              show ofString "rl2" ≠ ofString "node" by decide]
          have hsb_lf : sb.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlf,
              show ofString "i" ≠ ofString "fr" by decide,
              show ofString "payload" ≠ ofString "fr" by decide,
              show ofString "rl2" ≠ ofString "fr" by decide]
          have hsb_lk : sb.locals.lookup (ofString "k") = some (.val (.word kw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlk,
              show ofString "i" ≠ ofString "k" by decide,
              show ofString "payload" ≠ ofString "k" by decide,
              show ofString "rl2" ≠ ofString "k" by decide]
          have hsb_lp : sb.locals.lookup (ofString "payload") = some (.val (.word (payw + rlw))) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "payload" by decide]
          have hsb_lcb : sb.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlcb,
              show ofString "i" ≠ ofString "cbuf" by decide,
              show ofString "payload" ≠ ofString "cbuf" by decide,
              show ofString "rl2" ≠ ofString "cbuf" by decide]
          have hsb_lcl : sb.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlcl,
              show ofString "i" ≠ ofString "clen" by decide,
              show ofString "payload" ≠ ofString "clen" by decide,
              show ofString "rl2" ≠ ofString "clen" by decide]
          have hsb_li : sb.locals.lookup (ofString "i") = some (.val (.word (iw + 1))) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hclk_sb : sb.clock ≤ clk := by
            change sb.clock ≤ s.clock - 1 at hclk_b; omega
          obtain ⟨payw', hpayw'_eq, hg_post, hm_post, hbe_post, heff_rest,
            hln_p, hlf_p, hlk_p, hlp_p, hlcb_p, hlcl_p⟩ :=
            ih sb Nd nodew frw kw (payw + rlw) cbufw clenw (iw + 1)
              hclk_sb hsb_c heff_s_sb.arena hsb_N hnode_in hsb_node_k
              (by rw [hiw1_nat]; omega) (by rw [hpay_add_nat, hiw1_nat]; omega)
              hsb_ln hsb_lf hsb_lk hsb_lp hsb_lcb hsb_lcl hsb_li hnone
          have hsum_sb_eq : branchRefsLenSum sb nodew.toNat (16 - (iw + 1).toNat) =
              branchRefsLenSum s nodew.toNat (16 - (iw + 1).toNat) := by
            apply branchRefsLenSum_congr (hbr_nd hk3)
            · intro j _; unfold memW; rw [hsb_m]
            · intro m hm; apply nodeRefBytes_congr
              · intro n _; unfold memW; rw [hsb_m]
              · intro n _; unfold memW; rw [hsb_m]
              · exact hm
            · omega
          have hrem_step : 16 - iw.toNat = (16 - (iw.toNat + 1)) + 1 := by omega
          have hidx_step : 16 - ((16 - (iw.toNat + 1)) + 1) = iw.toNat := by omega
          have hpay_final : payw'.toNat =
              payw.toNat + branchRefsLenSum s nodew.toNat (16 - iw.toNat) := by
            rw [hpayw'_eq, hsum_sb_eq, hpay_add_nat, hiw1_nat, hrem_step,
              branchRefsLenSum, hidx_step, hrl_eq, hch_nat']
            change payw.toNat + nodeRefBytes s (memW s (nodew.toNat + 32 + 8 * iw.toNat)) +
                branchRefsLenSum s nodew.toNat (16 - (iw.toNat + 1)) = _
            omega
          exact ⟨payw', hpay_final, hg_post.trans hsb_g, hm_post.trans hsb_m,
            hbe_post.trans hsb_be, heff_s_sb.trans heff_rest,
            hln_p, hlf_p, hlk_p, hlp_p, hlcb_p, hlcl_p⟩
        · exfalso
          change (evaluateHOLFiniteState sd finishLenLoopBody).1 ≠ none at hne_b
          change (evaluateHOLFiniteState sd finishLenLoopBody).1 ≠ some .break at hnb_b
          change (evaluateHOLFiniteState sd finishLenLoopBody).1 ≠ some .continue at hnc_b
          rw [hb_ev'] at hne_b hnb_b hnc_b
          cases rb with
          | none => exact hne_b rfl
          | some r' =>
            cases r' with
            | «break» => exact hnb_b rfl
            | «continue» => exact hnc_b rfl
            | _ => simp [fixClockHOLFinite] at hnone
    · simp only [hlt, ↓reduceIte]
      have hi_eq : 16 - iw.toNat = 0 := by omega
      exact ⟨payw, by rw [hi_eq]; simp [branchRefsLenSum], rfl, rfl, rfl,
        HeapByteEff.refl hAR [] ["heap_ptr"], hln, hlf, hlk, hlp, hlcb, hlcl⟩

private theorem node_nonHash_memW_eq_of_hashOnly_heapByteEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {extra : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (heff : HeapByteEff s post (Nd.map (fun n => (n + 24, 8)) ++ extra) gw)
    (hextra_disj : ∀ e ∈ extra, 0 < e.2 → ∀ o ∈ nodeExtents s Nd, Disj e o)
    {n off : Nat} (hn : n ∈ Nd) (hoff8 : off % 8 = 0)
    (hoff_lt : off + 8 ≤ nodeSize (memW s n)) (hoff_ne24 : off ≠ 24) :
    memW post (n + off) = memW s (n + off) := by
  have hcf : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ e ∈ extra, CellHitsPos a.toNat e) ∨
      CellHitsPos a.toNat (freeGap s) ∨
      CellHitsPos a.toNat (heapFree s) ∨
      (∃ m ∈ Nd, a.toNat = m + 24) := by
    intro a hne
    have hdom := heff.out_dom a hne
    have ha8 : a.toNat % 8 = 0 := by
      rw [hAs.1.memaddrs, ordinaryDomain_iff] at hdom; exact hdom.1
    rcases heff.cell_frame a hne with ⟨iv, hiv, hpos, hc1, hc2⟩ | hfg | hhf
    · rcases List.mem_append.1 hiv with hm24 | hex
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
        have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
        dsimp only at hc1 hc2
        exact Or.inr (Or.inr (Or.inr ⟨m, hm, by omega⟩))
      · exact Or.inl ⟨iv, hex, hpos, hc1, hc2⟩
    · exact Or.inr (Or.inl hfg)
    · exact Or.inr (Or.inr (Or.inl hhf))
  exact node_memW_eq_of_hashOnly_cell_frame hAs hN hextra_disj hcf hn hoff8 hoff_lt hoff_ne24

private def finishWriteLoopBody : ProgHOL 64 :=
  .decCall (ofString "w4") .one (ofString "node_write_ref")
    [.load .one (.op .add [.var .local (ofString "node"), .const 32,
      .panop .mul [.var .local (ofString "j"), .const 8]]),
     .op .add [.var .local (ofString "buf"), .var .local (ofString "off")]]
    (.seq
      (.assign .local (ofString "off")
        (.op .add [.var .local (ofString "off"), .var .local (ofString "w4")]))
      (.assign .local (ofString "j")
        (.op .add [.var .local (ofString "j"), .const 1])))

private def finishWriteLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "j")) (.const 16)) finishWriteLoopBody

private theorem eval_finishWriteLoop_none {F : Type} :
    ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (nodew frw kw payw cbufw clenw hlw bufw offw jw : BitVec 64)
      (bufLen : Nat),
      s.clock ≤ clk →
      s.code = originalRuntimeCode →
      ArenaReady s →
      NodeHeap s Nd →
      KeccakBufsSafe s Nd →
      nodew.toNat ∈ Nd →
      memW s nodew.toNat = 3 →
      jw.toNat ≤ 16 →
      bufw.toNat + bufLen ≤ heapLimit →
      offw.toNat + branchRefsLenSum s nodew.toNat (16 - jw.toNat) ≤ bufLen →
      (∀ o ∈ nodeExtents s Nd, Disj (bufw.toNat, bufLen) o) →
      s.locals.lookup (ofString "node") = some (.val (.word nodew)) →
      s.locals.lookup (ofString "fr") = some (.val (.word frw)) →
      s.locals.lookup (ofString "k") = some (.val (.word kw)) →
      s.locals.lookup (ofString "payload") = some (.val (.word payw)) →
      s.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) →
      s.locals.lookup (ofString "clen") = some (.val (.word clenw)) →
      s.locals.lookup (ofString "hl") = some (.val (.word hlw)) →
      s.locals.lookup (ofString "buf") = some (.val (.word bufw)) →
      s.locals.lookup (ofString "off") = some (.val (.word offw)) →
      s.locals.lookup (ofString "j") = some (.val (.word jw)) →
      (evaluateHOLFiniteState s finishWriteLoop).1 = none →
      let post := (evaluateHOLFiniteState s finishWriteLoop).2
      ∃ offw' : BitVec 64,
        offw'.toNat = offw.toNat + branchRefsLenSum s nodew.toNat (16 - jw.toNat) ∧
        HeapByteEff s post
          ([(bufw.toNat, bufLen)] ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s))
          ["heap_ptr"] ∧
        NodeHeap post Nd ∧
        nodeExtents post Nd = nodeExtents s Nd ∧
        KeccakBufsSafe post Nd ∧
        (∀ n ∈ Nd, ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) → off ≠ 24 →
          memW post (n + off) = memW s (n + off)) ∧
        post.locals.lookup (ofString "node") = some (.val (.word nodew)) ∧
        post.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
        post.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
        post.locals.lookup (ofString "payload") = some (.val (.word payw)) ∧
        post.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) ∧
        post.locals.lookup (ofString "clen") = some (.val (.word clenw)) ∧
        post.locals.lookup (ofString "hl") = some (.val (.word hlw)) ∧
        post.locals.lookup (ofString "buf") = some (.val (.word bufw)) ∧
        post.locals.lookup (ofString "off") = some (.val (.word offw')) := by
  intro clk
  induction clk with
  | zero =>
    intro s Nd nodew frw kw payw cbufw clenw hlw bufw offw jw bufLen
      hclk _ hAR hN hKS _ _ hj16 _ _ _
      hln hlf hlk hlp hlcb hlcl hlhl hlb hlo hlj hnone post
    dsimp only [post]
    rw [finishWriteLoop, evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    have hcnd : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "j")) (.const 16)) =
        some (.val (.word (if jw.toNat < 16 then 1 else 0))) := by
      have h16 : (16#64).toNat = 16 := rfl
      simp [evalHOLFinite, evalHOLExact, hlj, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small jw 16#64 (by omega) (by decide), h16]
    rw [hcnd] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hlt : jw.toNat < 16
    · have hk0 : s.clock = 0 := by omega
      simp [hlt, hk0] at hnone
    · simp only [hlt, ↓reduceIte]
      have hj_eq : 16 - jw.toNat = 0 := by omega
      exact ⟨offw, by rw [hj_eq]; simp [branchRefsLenSum],
        HeapByteEff.refl hAR _ ["heap_ptr"], hN, rfl, hKS,
        fun _ _ _ _ _ _ => rfl, hln, hlf, hlk, hlp, hlcb, hlcl, hlhl, hlb, hlo⟩
  | succ clk ih =>
    intro s Nd nodew frw kw payw cbufw clenw hlw bufw offw jw bufLen
      hclk hc hAR hN hKS hnode_in hk3 hj16 hbuf_hi hoff_fit hbuf_disj
      hln hlf hlk hlp hlcb hlcl hlhl hlb hlo hlj hnone post
    dsimp only [post]
    rw [finishWriteLoop, evaluateHOLFiniteState_while_fixClockRewrite, ← finishWriteLoop] at hnone ⊢
    have hcnd : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "j")) (.const 16)) =
        some (.val (.word (if jw.toNat < 16 then 1 else 0))) := by
      have h16 : (16#64).toNat = 16 := rfl
      simp [evalHOLFinite, evalHOLExact, hlj, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small jw 16#64 (by omega) (by decide), h16]
    rw [hcnd] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hlt : jw.toNat < 16
    · have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos hlt, if_pos h10] at hnone ⊢
      by_cases hcz : s.clock = 0
      · simp [hcz] at hnone
      · rw [if_neg hcz] at hnone ⊢
        let sd := decClockHOLFinite s
        have hsd_AR : ArenaReady sd := localsFree_arenaReady s s.locals (s.clock - 1) hAR
        have hhl_he : heapLimit ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
        have hhe264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
        have h264 : heapLimit < 2 ^ 64 := by decide
        obtain ⟨_, _, hin_nd, hw_nd, _, hbr_nd, _⟩ := hN.1 nodew.toNat hnode_in
        have hsz3 : nodeSize (memW s nodew.toNat) = 176 := by simp [nodeSize, hk3]
        have hsd_W_nd : WordsOK sd (nodeIvl s nodew.toNat) :=
          P3MptSet.wordsOK_transfer hAR.1 hsd_AR.1 hw_nd
        have hmul_eq : jw * (8 : BitVec 64) = BitVec.ofNat 64 (8 * jw.toNat) := by
          apply BitVec.eq_of_toNat_eq
          have h8 : ((8 : BitVec 64)).toNat = 8 := rfl
          rw [BitVec.toNat_mul, h8, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hoff_eq : BitVec.ofNat 64 32 + jw * BitVec.ofNat 64 8 = BitVec.ofNat 64 (32 + 8 * jw.toNat) := by
          change (32 : BitVec 64) + jw * 8 = BitVec.ofNat 64 (32 + 8 * jw.toNat)
          apply BitVec.eq_of_toNat_eq
          have h32 : ((32 : BitVec 64)).toNat = 32 := rfl
          rw [hmul_eq, BitVec.toNat_add, h32, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        obtain ⟨chw, hch_ev, hch_nat⟩ :=
          eval_load_memW_of_wordsOK (s := sd) (base := nodew) (off := 32 + 8 * jw.toNat)
            hsd_W_nd (by omega) (by change 32 + 8 * jw.toNat + 8 ≤ nodeSize (memW s nodew.toNat); omega)
            (by have := hin_nd.2; dsimp [nodeIvl] at this; omega)
            (e := .op .add [.var .local (ofString "node"), .const 32,
              .panop .mul [.var .local (ofString "j"), .const 8]])
            (by
              have hsd_n : sd.locals.lookup (ofString "node") = some (.val (.word nodew)) := hln
              have hsd_j : sd.locals.lookup (ofString "j") = some (.val (.word jw)) := hlj
              simp [evalHOLExact, evalListHOLExact, hsd_n, hsd_j,
                wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, BitVec.add_zero, hoff_eq])
        have hch_nat' : chw.toNat = memW s (nodew.toNat + 32 + 8 * jw.toNat) := by
          have : nodew.toNat + (32 + 8 * jw.toNat) = nodew.toNat + 32 + 8 * jw.toNat := by omega
          change chw.toNat = memW s (nodew.toNat + (32 + 8 * jw.toNat)) at hch_nat
          simpa [this] using hch_nat
        have hch_root : RootIn Nd chw.toNat := by rw [hch_nat']; exact hbr_nd hk3 jw.toNat hlt
        have hrem_step : 16 - jw.toNat = (16 - (jw.toNat + 1)) + 1 := by omega
        have hidx_step : 16 - ((16 - (jw.toNat + 1)) + 1) = jw.toNat := by omega
        have hsum_unfold : branchRefsLenSum s nodew.toNat (16 - jw.toNat) =
            nodeRefBytes s chw.toNat + branchRefsLenSum s nodew.toNat (16 - (jw.toNat + 1)) := by
          rw [hrem_step, branchRefsLenSum, hidx_step, hch_nat']
        have hdst_add_nat : (bufw + offw).toNat = bufw.toNat + offw.toNat := by
          rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
        have hdst_ev : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")]) =
            some (.val (.word (bufw + offw))) := by
          have hsd_b : sd.locals.lookup (ofString "buf") = some (.val (.word bufw)) := hlb
          have hsd_o : sd.locals.lookup (ofString "off") = some (.val (.word offw)) := hlo
          simp [evalHOLExact, evalListHOLExact, hsd_b, hsd_o,
            wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
        have hclk_b := evaluateHOLFiniteState_clock_le sd finishWriteLoopBody
        rcases hb_ev : evaluateHOLFiniteState (decClockHOLFinite s) finishWriteLoopBody with ⟨rb, sb⟩
        have hb_ev' : evaluateHOLFiniteState sd finishWriteLoopBody = (rb, sb) := hb_ev
        simp only [hb_ev] at hnone ⊢
        rw [hb_ev'] at hclk_b
        have hnt_b : rb ≠ some .timeOut := by
          rintro rfl; simp [fixClockHOLFinite] at hnone
        have hdc := eval_decCall_node_write_ref sd Nd "w4"
          (.load .one (.op .add [.var .local (ofString "node"), .const 32,
            .panop .mul [.var .local (ofString "j"), .const 8]]))
          (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")])
          chw (bufw + offw)
          (.seq
            (.assign .local (ofString "off")
              (.op .add [.var .local (ofString "off"), .var .local (ofString "w4")]))
            (.assign .local (ofString "j")
              (.op .add [.var .local (ofString "j"), .const 1])))
          [(bufw.toNat, bufLen)] ["heap_ptr"] hc hsd_AR hN hch_root hch_ev hdst_ev
          (by change (bufw + offw).toNat + nodeRefBytes s chw.toNat ≤ heapEnd; rw [hdst_add_nat]; omega)
          ⟨(bufw.toNat, bufLen), List.Mem.head _,
            by change bufw.toNat ≤ (bufw + offw).toNat; rw [hdst_add_nat]; omega,
            by change (bufw + offw).toNat + nodeRefBytes s chw.toNat ≤ bufw.toNat + bufLen; rw [hdst_add_nat]; omega⟩
          (by decide)
          (by change (evaluateHOLFiniteState sd finishWriteLoopBody).1 ≠ _; rw [hb_ev']; exact hnt_b)
        dsimp only at hdc
        change (∃ _ _, _) ∨ _ at hdc
        rcases hdc with ⟨w4w, mid, hw4_eq, hmid_l, heff_mid24, _, hpres_fn, _, hdc_eq⟩ |
            ⟨hne_b, _, hnb_b, hnc_b, _⟩
        · change evaluateHOLFiniteState sd finishWriteLoopBody = _ at hdc_eq
          have hw4_eq' : w4w.toNat = nodeRefBytes s chw.toNat := hw4_eq
          have hmid_off : mid.locals.lookup (ofString "off") = some (.val (.word offw)) := by
            rw [hmid_l]; simp [sd, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlo,
              show ofString "w4" ≠ ofString "off" by decide]
          have hmid_w4 : mid.locals.lookup (ofString "w4") = some (.val (.word w4w)) := by
            rw [hmid_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hmid_j : mid.locals.lookup (ofString "j") = some (.val (.word jw)) := by
            rw [hmid_l]; simp [sd, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlj,
              show ofString "w4" ≠ ofString "j" by decide]
          have hasg_ev : evaluateHOLFiniteState mid
              (.seq
                (.assign .local (ofString "off")
                  (.op .add [.var .local (ofString "off"), .var .local (ofString "w4")]))
                (.assign .local (ofString "j")
                  (.op .add [.var .local (ofString "j"), .const 1]))) =
              (none, setVarHOLFinite (ofString "j") (.val (.word (jw + 1)))
                (setVarHOLFinite (ofString "off") (.val (.word (offw + w4w))) mid)) := by
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            have hne_oj : ofString "off" ≠ ofString "j" := by decide
            simp [evalHOLExact, evalListHOLExact, hmid_off, hmid_w4, hmid_j, hne_oj, Ne.symm hne_oj,
              wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero,
              isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
              setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              evaluateHOLFiniteState_assign]
          rw [hasg_ev] at hdc_eq
          rw [hb_ev'] at hdc_eq
          have hrb_none : rb = none := congrArg Prod.fst hdc_eq
          have hsb_eq : sb = { mid with
              locals := HolFiniteMapExact.resVarEq
                ((setVarHOLFinite (ofString "j") (.val (.word (jw + 1)))
                  (setVarHOLFinite (ofString "off") (.val (.word (offw + w4w))) mid)).locals)
                (ofString "w4", sd.locals.lookup (ofString "w4")) } :=
            congrArg Prod.snd hdc_eq
          subst hrb_none
          dsimp only at hnone ⊢
          let R24 := [(bufw.toNat, bufLen)] ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)
          have heff_s_sb : HeapByteEff s sb R24 ["heap_ptr"] := by
            rw [hsb_eq]
            exact (((HeapByteEff.refl hAR R24 ["heap_ptr"]).locals_clock sd.locals sd.clock).trans heff_mid24).locals_clock _ _
          have hkc_disj_s : ∀ o ∈ nodeExtents s Nd,
              Disj (bufferRegion s ("keccak_pad", 136)) o ∧
              Disj (bufferRegion s ("keccak_st", 200)) o := by
            intro o ho
            exact ⟨disj_comm ((hKS ("keccak_pad", 136) (by decide)).2 o ho),
              disj_comm ((hKS ("keccak_st", 200) (by decide)).2 o ho)⟩
          obtain ⟨hN_mid, hext_mid, _, hnrb_mid⟩ :=
            hpres_fn (fun e he _ o ho => by simp at he; subst he; exact hbuf_disj o ho) hkc_disj_s
          have hN_sb : NodeHeap sb Nd := by
            rw [hsb_eq]; exact hN_mid
          have hext_sb : nodeExtents sb Nd = nodeExtents s Nd := by
            rw [hsb_eq]; exact hext_mid
          have hkp_sb : globN sb "keccak_pad" = globN s "keccak_pad" := by
            unfold globN; rw [← heff_s_sb.globals (ofString "keccak_pad") (by decide)]
          have hks_sb : globN sb "keccak_st" = globN s "keccak_st" := by
            unfold globN; rw [← heff_s_sb.globals (ofString "keccak_st") (by decide)]
          have hbuf_sb_eq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
              bufferRegion sb gs = bufferRegion s gs := by
            intro gs hgs
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
            rcases hgs with rfl | rfl
            · simp [bufferRegion, hkp_sb]
            · simp [bufferRegion, hks_sb]
          have hkc_sb_eq : keccakBufIvls sb = keccakBufIvls s := by
            simp [keccakBufIvls, hbuf_sb_eq ("keccak_pad", 136) (by decide),
              hbuf_sb_eq ("keccak_st", 200) (by decide)]
          have hKS_sb : KeccakBufsSafe sb Nd :=
            keccakBufsSafe_of_grows hKS ⟨heff_s_sb.hp_le, heff_s_sb.sp_le⟩ hbuf_sb_eq hext_sb
          have heff_s_sb_reord : HeapByteEff s sb
              (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
              ["heap_ptr"] := by
            refine heff_s_sb.mono (fun i hi _ => ?_) (fun _ hg => hg)
            rcases List.mem_append.1 hi with hrl | hrest
            · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_left _ hrl), le_rfl, le_rfl⟩
            · rcases List.mem_append.1 hrest with hm24 | hkc
              · exact Or.inl ⟨i, List.mem_append_left _ hm24, le_rfl, le_rfl⟩
              · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkc), le_rfl, le_rfl⟩
          have hw_sb_eq : ∀ n ∈ Nd, ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) → off ≠ 24 →
              memW sb (n + off) = memW s (n + off) := by
            intro n hn off hoff8 hoff_lt hoff_ne24
            apply node_nonHash_memW_eq_of_hashOnly_heapByteEff hAR hN heff_s_sb_reord ?_ hn hoff8 hoff_lt hoff_ne24
            intro e he _ o ho
            rcases List.mem_append.1 he with hrl | hkc
            · simp at hrl; subst hrl; exact hbuf_disj o ho
            · exact keccakBufIvls_disj_of_safe hKS e hkc o ho
          have hsb_node_k : memW sb nodew.toNat = 3 := by
            have := hw_sb_eq nodew.toNat hnode_in 0 (by decide) (by omega) (by decide)
            simpa [hk3] using this
          have hjw1_nat : (jw + 1).toNat = jw.toNat + 1 := by
            have h1v : ((1 : BitVec 64)).toNat = 1 := rfl
            rw [BitVec.toNat_add, h1v]; exact Nat.mod_eq_of_lt (by omega)
          have hoff_add_nat : (offw + w4w).toNat = offw.toNat + w4w.toNat := by
            rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
          have hsum_sb_eq : branchRefsLenSum sb nodew.toNat (16 - (jw + 1).toNat) =
              branchRefsLenSum s nodew.toNat (16 - (jw + 1).toNat) := by
            apply branchRefsLenSum_congr (hbr_nd hk3)
            · intro i hi
              have := hw_sb_eq nodew.toNat hnode_in (32 + 8 * i) (by omega) (by omega) (by omega)
              simpa [Nat.add_assoc] using this
            · intro m hm
              rw [hsb_eq]
              exact hnrb_mid m hm
            · omega
          have hsb_ln : sb.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hln,
              show ofString "j" ≠ ofString "node" by decide,
              show ofString "off" ≠ ofString "node" by decide,
              show ofString "w4" ≠ ofString "node" by decide]
          have hsb_lf : sb.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlf,
              show ofString "j" ≠ ofString "fr" by decide,
              show ofString "off" ≠ ofString "fr" by decide,
              show ofString "w4" ≠ ofString "fr" by decide]
          have hsb_lk : sb.locals.lookup (ofString "k") = some (.val (.word kw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlk,
              show ofString "j" ≠ ofString "k" by decide,
              show ofString "off" ≠ ofString "k" by decide,
              show ofString "w4" ≠ ofString "k" by decide]
          have hsb_lp : sb.locals.lookup (ofString "payload") = some (.val (.word payw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlp,
              show ofString "j" ≠ ofString "payload" by decide,
              show ofString "off" ≠ ofString "payload" by decide,
              show ofString "w4" ≠ ofString "payload" by decide]
          have hsb_lcb : sb.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlcb,
              show ofString "j" ≠ ofString "cbuf" by decide,
              show ofString "off" ≠ ofString "cbuf" by decide,
              show ofString "w4" ≠ ofString "cbuf" by decide]
          have hsb_lcl : sb.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlcl,
              show ofString "j" ≠ ofString "clen" by decide,
              show ofString "off" ≠ ofString "clen" by decide,
              show ofString "w4" ≠ ofString "clen" by decide]
          have hsb_lhl : sb.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlhl,
              show ofString "j" ≠ ofString "hl" by decide,
              show ofString "off" ≠ ofString "hl" by decide,
              show ofString "w4" ≠ ofString "hl" by decide]
          have hsb_lb : sb.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid_l, hlb,
              show ofString "j" ≠ ofString "buf" by decide,
              show ofString "off" ≠ ofString "buf" by decide,
              show ofString "w4" ≠ ofString "buf" by decide]
          have hsb_lo : sb.locals.lookup (ofString "off") = some (.val (.word (offw + w4w))) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "j" ≠ ofString "off" by decide]
          have hsb_lj : sb.locals.lookup (ofString "j") = some (.val (.word (jw + 1))) := by
            rw [hsb_eq, resVarEq_lookup_ne _ _ _ _ (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hclk_sb : sb.clock ≤ clk := by
            change sb.clock ≤ s.clock - 1 at hclk_b; omega
          obtain ⟨offw', hoffw'_eq, heff_rest, hN_post, hext_post, hKS_post, hw_post,
            hln_p, hlf_p, hlk_p, hlp_p, hlcb_p, hlcl_p, hlhl_p, hlb_p, hlo_p⟩ :=
            ih sb Nd nodew frw kw payw cbufw clenw hlw bufw (offw + w4w) (jw + 1) bufLen
              hclk_sb heff_s_sb.arena.1.code heff_s_sb.arena hN_sb hKS_sb hnode_in hsb_node_k
              (by rw [hjw1_nat]; omega) hbuf_hi
              (by rw [hoff_add_nat, hsum_sb_eq, hw4_eq', hjw1_nat]; omega)
              (fun o ho => by rw [hext_sb] at ho; exact hbuf_disj o ho)
              hsb_ln hsb_lf hsb_lk hsb_lp hsb_lcb hsb_lcl hsb_lhl hsb_lb hsb_lo hsb_lj hnone
          rw [hkc_sb_eq] at heff_rest
          have hoff_final : offw'.toNat =
              offw.toNat + branchRefsLenSum s nodew.toNat (16 - jw.toNat) := by
            rw [hoffw'_eq, hsum_sb_eq, hoff_add_nat, hw4_eq', hjw1_nat, hsum_unfold]
            omega
          exact ⟨offw', hoff_final, heff_s_sb.trans heff_rest, hN_post,
            hext_post.trans hext_sb, hKS_post,
            fun n hn off hoff8 hoff_lt hoff_ne24 => by
              have hsz_ge := nodeSize_ge32 (memW s n)
              have hk_sb_eq : memW sb n = memW s n := by
                simpa using hw_sb_eq n hn 0 (by decide) (by omega) (by decide)
              exact (hw_post n hn off hoff8 (by rw [hk_sb_eq]; exact hoff_lt) hoff_ne24).trans
                (hw_sb_eq n hn off hoff8 hoff_lt hoff_ne24),
            hln_p, hlf_p, hlk_p, hlp_p, hlcb_p, hlcl_p, hlhl_p, hlb_p, hlo_p⟩
        · exfalso
          change (evaluateHOLFiniteState sd finishWriteLoopBody).1 ≠ none at hne_b
          change (evaluateHOLFiniteState sd finishWriteLoopBody).1 ≠ some .break at hnb_b
          change (evaluateHOLFiniteState sd finishWriteLoopBody).1 ≠ some .continue at hnc_b
          rw [hb_ev'] at hne_b hnb_b hnc_b
          cases rb with
          | none => exact hne_b rfl
          | some r' =>
            cases r' with
            | «break» => exact hnb_b rfl
            | «continue» => exact hnc_b rfl
            | _ => simp [fixClockHOLFinite] at hnone
    · simp only [hlt, ↓reduceIte]
      have hj_eq : 16 - jw.toNat = 0 := by omega
      exact ⟨offw, by rw [hj_eq]; simp [branchRefsLenSum],
        HeapByteEff.refl hAR _ ["heap_ptr"], hN, rfl, hKS,
        fun _ _ _ _ _ _ => rfl, hln, hlf, hlk, hlp, hlcb, hlcl, hlhl, hlb, hlo⟩

private def finishPayloadLen {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fr node : Nat) : Nat :=
  if memW s node = 2 then
    memW s (fr + 40) + nodeRefBytes s (memW s (node + 48))
  else if memW s node = 3 then
    memW s (fr + 40) + branchRefsLenSum s node 16 +
      rlpBytesLenPure
        (if 0 < memW s (node + 168) then memB s (memW s (node + 160)) else 0)
        (memW s (node + 168))
  else memW s (fr + 40)

private theorem finishPayloadLen_lt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (fr : Nat) (hN : NodeHeap s Nd)
    (hfr : ValidRlpFrame s Nd fr) :
    finishPayloadLen s fr (memW s (fr + 8)) < 2 ^ 42 := by
  obtain ⟨_, _, _, hn, _, _, _, hpay, hpay3, _, _⟩ := hfr
  unfold finishPayloadLen
  by_cases h2 : memW s (memW s (fr + 8)) = 2
  · rw [if_pos h2]
    have := nodeRefBytes_le33 s (memW s (memW s (fr + 8) + 48))
    omega
  · rw [if_neg h2]
    by_cases h3 : memW s (memW s (fr + 8)) = 3
    · rw [if_pos h3]
      have hzero := hpay3 h3
      have hsum := branchRefsLenSum_le s (memW s (fr + 8)) 16
      obtain ⟨_, _, _, _, _, _, _, _, _, hbranch⟩ := hN.1 _ hn
      have hlen := hbranch h3
      have hrlp := (rlpBytesLenPure_bounds
        (if 0 < memW s (memW s (fr + 8) + 168) then
          memB s (memW s (memW s (fr + 8) + 160)) else 0)
        (memW s (memW s (fr + 8) + 168))).2.2
      omega
    · rw [if_neg h3]
      omega

private theorem finishPayloadLen_pos {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (fr : Nat) (hfr : ValidRlpFrame s Nd fr) :
    1 ≤ finishPayloadLen s fr (memW s (fr + 8)) := by
  obtain ⟨_, _, _, _, hk1, hk3, _, _, _, hleaf, hext⟩ := hfr
  unfold finishPayloadLen
  by_cases h2 : memW s (memW s (fr + 8)) = 2
  · rw [if_pos h2]
    obtain ⟨_, _, _, _, _, hpay2⟩ := hext h2
    have hb := (rlpBytesLenPure_bounds (memB s (memW s (fr + 24))) (memW s (fr + 32))).1
    omega
  · rw [if_neg h2]
    by_cases h3 : memW s (memW s (fr + 8)) = 3
    · rw [if_pos h3]
      have hb := (rlpBytesLenPure_bounds
        (if 0 < memW s (memW s (fr + 8) + 168) then
          memB s (memW s (memW s (fr + 8) + 160)) else 0)
        (memW s (memW s (fr + 8) + 168))).1
      omega
    · rw [if_neg h3]
      have h1 : memW s (memW s (fr + 8)) = 1 := by omega
      obtain ⟨_, _, _, _, _, hpay1, _⟩ := hleaf h1
      have hb1 := (rlpBytesLenPure_bounds (memB s (memW s (fr + 24))) (memW s (fr + 32))).1
      have hb2 := (rlpBytesLenPure_bounds 128 (memW s (memW s (fr + 8) + 56))).1
      omega

end NodeRlpFillProof

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
