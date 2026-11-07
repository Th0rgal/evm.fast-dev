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
from `Nd`'s node records and paths. Propagated from `MptObjReadyStrong` in `mpt_root`. -/
def KeccakBufsSafe {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
    ((bufferRegion s gs).2 = 0 ∨ Allocated s (bufferRegion s gs)) ∧
      ∀ o ∈ nodeExtents s Nd, Disj o (bufferRegion s gs)

/-- Scratch gap up to caller scratch ceiling `sp0`: `[frame_mem_ptr, sp0)`. -/
def freeGapTo {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (globN s "frame_mem_ptr", sp0 - globN s "frame_mem_ptr")

/-- Minimal 1-byte value-pointer non-aliasing condition for `Nd` wrt scratch ceiling `sp0`:
any leaf (`k = 1`, `vlen = 1`) or branch (`k = 3`, `vlen = 1`) in `Nd` whose 1-byte value pointer
`vp` lies in `ordinaryDomain` does not alias `[heap_ptr, heapLimit)`, `[frame_mem_ptr, sp0)`,
`nodeCacheIvls Nd`, or `keccakBufIvls s`. At `mpt_root` entry `sp0 = globN s "scratch_ptr"`,
so `freeGapTo sp0 s = freeGap s`. -/
def NodeValuesSafe {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  ∀ n ∈ Nd,
    (memW s n = 1 → memW s (n + 56) = 1 →
      ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 48)))) →
      (∀ m ∈ Nd, ¬ InIvl (memW s (n + 48)) (m + 8, 24)) ∧
      (∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
        0 < (bufferRegion s gs).2 → ¬ InIvl (memW s (n + 48)) (bufferRegion s gs)) ∧
      ¬ InIvl (memW s (n + 48)) (freeGapTo sp0 s) ∧
      ¬ InIvl (memW s (n + 48)) (heapFree s)) ∧
    (memW s n = 3 → memW s (n + 168) = 1 →
      ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 160)))) →
      (∀ m ∈ Nd, ¬ InIvl (memW s (n + 160)) (m + 8, 24)) ∧
      (∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
        0 < (bufferRegion s gs).2 → ¬ InIvl (memW s (n + 160)) (bufferRegion s gs)) ∧
      ¬ InIvl (memW s (n + 160)) (freeGapTo sp0 s) ∧
      ¬ InIvl (memW s (n + 160)) (heapFree s))

/-- Entry-level 1-byte value-pointer invariant for `Nd`: `NodeValuesSafe` specialized to
`sp0 = globN s "scratch_ptr"` (where `freeGapTo sp0 s = freeGap s`). -/
def NodeHeapValuePtrOK {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  NodeValuesSafe (globN s "scratch_ptr") s Nd

def MptObjInWithStrong {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nm : List Nat) (m : Nat) : Prop :=
  MptObjInWith s S Nm m ∧ NodeHeapValuePtrOK s Nm

def MptObjInStrong {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  ∃ Nm, MptObjInWithStrong s S Nm (locN s "m")

def MptObjAvoidsStrong (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ MptObjInStrong s S ∧ (∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j) ∧
    AvoidsTries s S ((locN s "m", 16) :: R s) ∧
    ∃ Nm Nd, MptObjInWithStrong s S Nm (locN s "m") ∧ TriesTypedWith s S Nd ∧
      ∀ o ∈ (locN s "m", 16) :: R s ++ nodeExtents s Nm, ∀ j ∈ nodeExtents s Nd, Disj o j

def MptObjReadyStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MptObjAvoidsStrong (fun _ => []) s

/-- Strengthened `NodeRlpReady` carrying `KeccakBufsSafe` and `NodeHeapValuePtrOK` for `Nd`. -/
def NodeRlpReadyK : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "node") ∧
    KeccakBufsSafe s Nd ∧ NodeHeapValuePtrOK s Nd

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
  obtain ⟨Nd, hNd, hr, _, _⟩ := h.1.2
  exact ⟨h.1.1, Nd, hNd, hr⟩

private theorem strong_node_member {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : NodeRlpReadyStrong s) :
    ∃ Nd, NodeHeap s Nd ∧ locN s "node" ∈ Nd ∧ KeccakBufsSafe s Nd ∧ NodeHeapValuePtrOK s Nd := by
  obtain ⟨Nd, hNd, hr, hk, hv⟩ := h.1.2
  exact ⟨Nd, hNd, hr.resolve_left h.2.1, hk, hv⟩

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

private theorem nodeValuesSafe_with_locals {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {Nd : List Nat}
    (h : NodeValuesSafe sp0 s Nd) :
    NodeValuesSafe sp0 { s with locals := locals, clock := k } Nd := h

private theorem nodeValuesSafe_of_heapByteEff {F : Type}
    {sp0 : Nat} {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {extra : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd) (hsafe : KeccakBufsSafe s Nd)
    (hkp_out : ofString "keccak_pad" ∉ gw.map ofString)
    (hks_out : ofString "keccak_st" ∉ gw.map ofString)
    (heff : R16Shards.WkBlockTxEnc.HeapByteEff s post
      (nodeCacheIvls Nd ++ keccakBufIvls s ++ extra) gw)
    (hextra_disj : ∀ e ∈ extra, 0 < e.2 → ∀ o ∈ nodeExtents s Nd, Disj e o)
    (hvs : NodeValuesSafe sp0 s Nd) :
    NodeValuesSafe sp0 post Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hkc_all := keccakBufIvls_disj_of_safe hsafe
  have hbuf_eq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion post gs = bufferRegion s gs := by
    intro gs hgs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl
    · unfold bufferRegion globN
      rw [← heff.globals (ofString "keccak_pad") hkp_out]
    · unfold bufferRegion globN
      rw [← heff.globals (ofString "keccak_st") hks_out]
  have hw_noncache : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 →
      off + 8 ≤ nodeSize (memW s n) → (off = 0 ∨ 32 ≤ off) →
      memW post (n + off) = memW s (n + off) := by
    intro n hn off hoff8 hoff_lt hoff_out
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
    have hn8 : n % 8 = 0 := hw_n.1
    have hal_off : Allocated s (n + off, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    have ha_lt : n + off < 2 ^ 64 := by have := hin_n.2; dsimp [nodeIvl] at this; omega
    apply memW_eq_of_heapByteEff_disj hAs heff (by omega) hal_off ha_lt
    intro iv hiv hpos
    rcases List.mem_append.1 hiv with hiv1 | hex
    · rcases List.mem_append.1 hiv1 with hc | hkc
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
        by_cases hnm : n = m
        · subst hnm
          rcases hoff_out with rfl | h32
          · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
          · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
        · have hdj := hN.2 n hn m hm hnm
          have hsz_m := nodeSize_ge32 (memW s m)
          dsimp [Disj, nodeIvl] at hdj ⊢
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · have ho_mem : nodeIvl s n ∈ nodeExtents s Nd := by
          unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
        have hdj := hkc_all iv hkc (nodeIvl s n) ho_mem
        dsimp [Disj, nodeIvl] at hdj ⊢
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
    · have ho_mem : nodeIvl s n ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
      have hdj := hextra_disj iv hex hpos (nodeIvl s n) ho_mem
      dsimp [Disj, nodeIvl] at hdj ⊢
      rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  have hfg_eq : freeGapTo sp0 post = freeGapTo sp0 s := by
    simp [freeGapTo, heff.fp_eq]
  have hhf_sub : ∀ b, InIvl b (heapFree post) → InIvl b (heapFree s) := by
    intro b hb
    dsimp [InIvl, heapFree] at hb ⊢
    have hhp := heff.hp_le
    omega
  intro n hn
  have hsz0 := nodeSize_ge32 (memW s n)
  have hk_eq : memW post n = memW s n := hw_noncache n hn 0 (by decide) (by omega) (Or.inl rfl)
  obtain ⟨h1, h3⟩ := hvs n hn
  refine ⟨?_, ?_⟩
  · intro hk1 hv1 hdom
    have hk1_s : memW s n = 1 := hk_eq ▸ hk1
    have hsz1 : nodeSize (memW s n) = 64 := by simp [nodeSize, hk1_s]
    have h48 := hw_noncache n hn 48 (by decide) (by omega) (Or.inr (by decide))
    have h56 := hw_noncache n hn 56 (by decide) (by omega) (Or.inr (by decide))
    rw [h48] at hdom ⊢
    rw [hfg_eq]
    obtain ⟨hnc_no, hkc_no, hfg_no, hhf_no⟩ := h1 hk1_s (h56 ▸ hv1) hdom
    refine ⟨hnc_no, ?_, hfg_no, fun h => hhf_no (hhf_sub _ h)⟩
    intro gs hgs hpos
    rw [hbuf_eq gs hgs] at hpos ⊢
    exact hkc_no gs hgs hpos
  · intro hk3 hv1 hdom
    have hk3_s : memW s n = 3 := hk_eq ▸ hk3
    have hsz3 : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3_s]
    have h160 := hw_noncache n hn 160 (by decide) (by omega) (Or.inr (by decide))
    have h168 := hw_noncache n hn 168 (by decide) (by omega) (Or.inr (by decide))
    rw [h160] at hdom ⊢
    rw [hfg_eq]
    obtain ⟨hnc_no, hkc_no, hfg_no, hhf_no⟩ := h3 hk3_s (h168 ▸ hv1) hdom
    refine ⟨hnc_no, ?_, hfg_no, fun h => hhf_no (hhf_sub _ h)⟩
    intro gs hgs hpos
    rw [hbuf_eq gs hgs] at hpos ⊢
    exact hkc_no gs hgs hpos

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

private theorem eval_dec_load_memW_of_wordsOK {F : Type}
    (s : PanSemStateFiniteExact 64 F) (base : BitVec 64) (off len : Nat)
    (name : MlS) (addr : ExpHOL 64) (cont : ProgHOL 64)
    (hW : WordsOK s (base.toNat, len))
    (hoff8 : off % 8 = 0) (hoff : off + 8 ≤ len)
    (hhi : base.toNat + len ≤ 2 ^ 64)
    (haddr : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) addr =
        some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ∃ w : BitVec 64,
      w.toNat = memW s (base.toNat + off) ∧
      evaluateHOLFiniteState s (.dec name .one (.load .one addr) cont) =
        ((evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) cont).1,
         { (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) cont).2 with
           locals := HolFiniteMapExact.resVarEq
             (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) cont).2.locals
             (name, s.locals.lookup name) }) := by
  obtain ⟨w, hload, hw⟩ := eval_load_memW_of_wordsOK hW hoff8 hoff hhi haddr
  refine ⟨w, hw, ?_⟩
  rw [evaluateHOLFiniteState_dec_total]
  simp only [hload]
  have hshape : shapeEqHOL .one
      (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  simp only [hshape, ↓reduceIte]

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
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "root") ∧
    KeccakBufsSafe s Nd ∧ NodeHeapValuePtrOK s Nd

private def RootCallReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => RootReady s ∧ locN s "root" ≠ 0

private theorem root_init {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hs : MptObjReadyStrong s)
    (hv : evalAt s (.load .one (.op .add [.var .local (ofString "m"), .const 0])) = some v) :
    RootReady (setVarHOLFinite (ofString "root") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "m" 0 v hv
  obtain ⟨ha, S, hS, ⟨Nd, hm, hvp⟩, _rest⟩ := hs
  refine ⟨localsFree_arenaReady s _ _ ha, Nd, hm.2.2.2.2.1, ?_, ?_, hvp⟩
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

/-- Strengthened `mpt_root` under `MptObjReadyStrong`. -/
theorem gbody_mpt_root_strong
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hn : TerminatingFunBoundedOn NodeRlpReadyNonNull (ofString "node_hash") K.«node_hash») :
    TerminatingFunBoundedOn MptObjReadyStrong (ofString "mpt_root") K.«mpt_root» := by
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

private def leafPayloadExact {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fr node : Nat) : Prop :=
  memW s (fr + 40) =
    rlpBytesLenPure (memB s (memW s (fr + 24))) (memW s (fr + 32)) +
      rlpBytesLenPure
        (if 0 < memW s (node + 56) then memB s (memW s (node + 48)) else 0)
        (memW s (node + 56))

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
    leafPayloadExact s fr (memW s (fr + 8)) ∧
    (0 < memW s (memW s (fr + 8) + 56) →
      s.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW s (memW s (fr + 8) + 48)))))) ∧
  (memW s (memW s (fr + 8)) = 2 →
    1 ≤ memW s (fr + 32) ∧
    memW s (fr + 32) ≤ memW s (memW s (fr + 8) + 40) / 2 + 1 ∧
    Inside (memW s (fr + 24), memW s (fr + 32)) sourceBase (globN s "heap_ptr") ∧
    (∀ o ∈ nodeExtents s Nd, Disj (memW s (fr + 24), memW s (fr + 32)) o) ∧
    (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      Disj (memW s (fr + 24), memW s (fr + 32)) (bufferRegion s gs)) ∧
    memW s (fr + 40) = rlpBytesLenPure (memB s (memW s (fr + 24))) (memW s (fr + 32))) ∧
  (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)], Disj (fr, 48) (bufferRegion s gs))

private theorem memW_lt_two_pow_64 {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    memW s a < 2 ^ 64 := by
  unfold memW
  cases s.memory (BitVec.ofNat 64 a) with
  | word w => exact w.isLt

private theorem rlpBytesLenPure_congr_ne_one {fb gb n : Nat} (hne : n ≠ 1) :
    rlpBytesLenPure fb n = rlpBytesLenPure gb n := by
  unfold rlpBytesLenPure
  rw [if_neg (by omega), if_neg (by omega)]

private theorem validRlpFrame_of_heapByteEff_disj {F : Type}
    {sp0 : Nat} {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {fr : Nat}
    {Rl : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (_hN : NodeHeap s Nd)
    (hvs : NodeValuesSafe sp0 s Nd)
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
    (hvp_disj_Rl : memW s (memW s (fr + 8)) = 1 → memW s (memW s (fr + 8) + 56) = 1 →
      ∀ iv ∈ Rl, 0 < iv.2 → ¬ InIvl (memW s (memW s (fr + 8) + 48)) iv)
    (hfg_sp0 : globN s "scratch_ptr" ≤ sp0)
    (hv : ValidRlpFrame s Nd fr) :
    ValidRlpFrame post Nd fr := by
  obtain ⟨hfr8, hfr_in, hfr_W, hnd_in, hk1, hk3, hidx, hpay, hk3_pay, hk1_pay, hk2_pay, hfr_kb⟩ := hv
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
    fun h3 => by rw [hw40]; exact hk3_pay (hk_eq ▸ h3), ?_, ?_,
    fun gs hgs => by rw [hbuf_eq gs hgs]; exact hfr_kb gs hgs⟩
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
      ?_, ?_⟩
    · unfold leafPayloadExact at hpay_lo ⊢
      rw [hw40, hw24, hw32, hn48_eq, hn56_eq, hcb_b]
      by_cases hv1 : memW s (memW s (fr + 8) + 56) = 1
      · have hpos1 : 0 < memW s (memW s (fr + 8) + 56) := by omega
        have hdom_ord : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW s (memW s (fr + 8) + 48)))) := by
          rw [← hAs.1.memaddrs]; exact hdom1 hpos1
        obtain ⟨_, _, hfg_no, hhf_no⟩ := (hvs _ hnd_in).1 h1s hv1 hdom_ord
        have hvp_lt : memW s (memW s (fr + 8) + 48) < 2 ^ 64 :=
          memW_lt_two_pow_64 s (memW s (fr + 8) + 48)
        have hvp_b : memB post (memW s (memW s (fr + 8) + 48)) = memB s (memW s (memW s (fr + 8) + 48)) := by
          by_contra hne
          rcases heff.byte_frame (memW s (memW s (fr + 8) + 48)) hvp_lt hne with
            ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
          · exact hvp_disj_Rl h1s hv1 iv hiv (by omega) ⟨hb1, hb2⟩
          · apply hfg_no
            dsimp [InIvl, freeGapTo]; dsimp [freeGap] at hfg1 hfg2
            omega
          · exact hhf_no ⟨hhf1, hhf2⟩
        rw [hvp_b]; exact hpay_lo
      · rw [rlpBytesLenPure_congr_ne_one hv1]; exact hpay_lo
    · intro hpos
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
    (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (frw nodew : BitVec 64)
    (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (hN : NodeHeap s Nd) (hKS : KeccakBufsSafe s Nd)
    (hvs : NodeValuesSafe sp0 s Nd)
    (hfr_loc : s.locals.lookup (ofString "fr") = some (.val (.word frw)))
    (hnode_loc : s.locals.lookup (ofString "node") = some (.val (.word nodew)))
    (hfr_in : Inside (frw.toNat, 48) (globN s "scratch_ptr") scratchEnd)
    (hfr_sp0 : frw.toNat + 48 ≤ sp0)
    (hfr_W : WordsOK s (frw.toNat, 48))
    (hfr_kb : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      Disj (frw.toNat, 48) (bufferRegion s gs))
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
            payw.toNat =
              rlpBytesLenPure (memB s1 cbufw.toNat) clenw.toNat +
                rlpBytesLenPure
                  (if 0 < memW s (nodew.toNat + 56) then memB s1 (memW s (nodew.toNat + 48)) else 0)
                  (memW s (nodew.toNat + 56)) ∧
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
            · have hv_b_s1 : memB s1 vpw.toNat = memB sa5 vpw.toNat := by
                have hm_s1_sa5 : s1.memory = sa5.memory ∧ s1.be = sa5.be := by
                  rw [hstate_s1]; exact ⟨hmid_vl_m, heff_vl.be⟩
                unfold memB; rw [hm_s1_sa5.1, hm_s1_sa5.2]
              rw [hpay_nat, hel_eq, hcb_b_s1, hvenc_eq, ← hvl_nat, ← hvp_nat, hv_b_s1]
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
    have heff_s1_post : HeapByteEff s1 postSt [(frw.toNat + 24, 24)] ["heap_ptr"] := by
      dsimp [postSt, emptyLocalsHOLFinite]
      exact (((heff_st1.trans heff_st2).trans heff_st3).locals_clock _ _).locals_clock _ _
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
    refine ⟨rfl, heff_post, hN_post.1, hN_post.2, hKS_post, hnd_memW_eq, ?_⟩
    have hbuf_post_eq : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
        bufferRegion postSt gs = bufferRegion s gs := by
      intro gs hgs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
      rcases hgs with rfl | rfl
      · simp [bufferRegion, hkp_eq]
      · simp [bufferRegion, hks_eq]
    refine ⟨hfr_W.1, by rw [hsp_eq]; exact hfr_in, hfr_W_post,
      by rw [hw8_p]; exact hnode_in,
      by rw [hw8_p, hk_post_eq]; exact hk1,
      by rw [hw8_p, hk_post_eq]; exact hk_le3,
      by rw [hw16_p]; exact hfr16_le,
      by rw [hw40_p]; exact hpay_lt,
      fun h3 => by rw [hw40_p]; exact hk3_p (by rwa [hw8_p, hk_post_eq] at h3),
      ?_, ?_, fun gs hgs => by rw [hbuf_post_eq gs hgs]; exact hfr_kb gs hgs⟩
    · intro h1_post
      have h1s : memW s nodew.toNat = 1 := by rwa [hw8_p, hk_post_eq] at h1_post
      have hsz1 : nodeSize (memW s nodew.toNat) = 64 := by simp [nodeSize, h1s]
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
      · unfold leafPayloadExact
        rw [hw40_p, hw24_p, hw32_p, hw8_p, hn48_eq, hn56_eq, hcb_b]
        by_cases hv1 : memW s (nodew.toNat + 56) = 1
        · have hpos1 : 0 < memW s (nodew.toNat + 56) := by omega
          have hdom_ord : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW s (nodew.toNat + 48)))) := by
            rw [← hAR.1.memaddrs]; exact hdom1 hpos1
          obtain ⟨_, _, hfg_no, hhf_no⟩ := (hvs nodew.toNat hnode_in).1 h1s hv1 hdom_ord
          have hvp_lt : memW s (nodew.toNat + 48) < 2 ^ 64 :=
            memW_lt_two_pow_64 s (nodew.toNat + 48)
          have hvp_b : memB postSt (memW s (nodew.toNat + 48)) = memB s1 (memW s (nodew.toNat + 48)) := by
            by_contra hne
            rcases heff_s1_post.byte_frame (memW s (nodew.toNat + 48)) hvp_lt hne with
              ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
            · simp only [List.mem_singleton] at hiv; subst hiv
              apply hfg_no
              have hfp_le_sp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAR.2.2.2.2.1
              have hfr_lo : globN s "scratch_ptr" ≤ frw.toNat := hfr_in.1
              dsimp [InIvl, freeGapTo]; dsimp only at hb1 hb2
              omega
            · apply hfg_no
              have hfp_eq1 : globN s1 "frame_mem_ptr" = globN s "frame_mem_ptr" := heff_s1.fp_eq
              have hsp_eq1 : globN s1 "scratch_ptr" = globN s "scratch_ptr" := by
                unfold globN; rw [← heff_s1.globals (ofString "scratch_ptr") (by decide)]
              have hsp_le_sp0 : globN s "scratch_ptr" ≤ sp0 := by
                have hfr_lo : globN s "scratch_ptr" ≤ frw.toNat := hfr_in.1
                omega
              dsimp [InIvl, freeGapTo]; dsimp [freeGap] at hfg1 hfg2
              omega
            · apply hhf_no
              have hhp_le1 : globN s "heap_ptr" ≤ globN s1 "heap_ptr" := heff_s1.hp_le
              dsimp [InIvl, heapFree] at hhf1 hhf2 ⊢
              omega
          rw [hvp_b]; exact hpay1
        · rw [rlpBytesLenPure_congr_ne_one hv1]; exact hpay1
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
      refine ⟨by rw [hw32_p]; exact hcl1,
        by rw [hw32_p, hw8_p, hn40_eq]; exact hcl_hi,
        by rw [hw24_p, hw32_p, hhp_post_s1]; exact hcb_in,
        fun o ho => by rw [hN_post.2] at ho; rw [hw24_p, hw32_p]; exact hcb_disj o ho,
        fun gs hgs => by rw [hbuf_post_eq gs hgs, hw24_p, hw32_p]; exact hcb_kb gs hgs,
        by rw [hw40_p, hw24_p, hw32_p, hcb_b, hpay2]⟩

private theorem eval_call__node_rlp_begin_none {F : Type}
    (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (frExp nodeExp : ExpHOL 64)
    (frw nodew : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hN : NodeHeap s Nd)
    (hKS : KeccakBufsSafe s Nd) (hvs : NodeValuesSafe sp0 s Nd)
    (hfr_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
      some (.val (.word frw)))
    (hnode_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
      some (.val (.word nodew)))
    (hfr_in : Inside (frw.toNat, 48) (globN s "scratch_ptr") scratchEnd)
    (hfr_sp0 : frw.toNat + 48 ≤ sp0)
    (hfr_W : WordsOK s (frw.toNat, 48))
    (hfr_kb : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      Disj (frw.toNat, 48) (bufferRegion s gs))
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
          eval__node_rlp_begin_returned sp0 ent Nd frw nodew vc hc hent_AR hN hKS hvs
            hent_fr hent_node hfr_in hfr_sp0 hfr_W hfr_kb hnode_in hk1 hfr8_eq hfr16_le (by rw [hcal])
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
  obtain ⟨_, _, _, _, hk1, hk3, _, _, _, hleaf, hext, _⟩ := hfr
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
      unfold leafPayloadExact at hpay1
      have hb1 := (rlpBytesLenPure_bounds (memB s (memW s (fr + 24))) (memW s (fr + 32))).1
      omega

private def finishWriteLen {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fr node : Nat) : Nat :=
  if memW s node = 3 then
    branchRefsLenSum s node 16 +
      rlpBytesLenPure
        (if 0 < memW s (node + 168) then memB s (memW s (node + 160)) else 0)
        (memW s (node + 168))
  else
    rlpBytesLenPure (memB s (memW s (fr + 24))) (memW s (fr + 32)) +
      if memW s node = 1 then
        rlpBytesLenPure
          (if 0 < memW s (node + 56) then memB s (memW s (node + 48)) else 0)
          (memW s (node + 56))
      else nodeRefBytes s (memW s (node + 48))

private theorem rlpBytesLenPure_lt_iff (fb gb n : Nat) :
    rlpBytesLenPure fb n < rlpBytesLenPure gb n ↔
      n = 1 ∧ fb < 128 ∧ 128 ≤ gb := by
  by_cases hn : n = 1
  · subst n
    by_cases hf : fb < 128 <;> by_cases hg : gb < 128 <;>
      simp [rlpBytesLenPure, rlpHeaderLenPure, hf, hg]; try omega
  · simp [rlpBytesLenPure, hn]

private theorem rlpBytesLenPure_growth_exact (fb gb n : Nat)
    (hg : rlpBytesLenPure fb n < rlpBytesLenPure gb n) :
    n = 1 ∧ fb < 128 ∧ 128 ≤ gb ∧
      rlpBytesLenPure gb n = rlpBytesLenPure fb n + 1 := by
  obtain ⟨rfl, hf, hb⟩ := (rlpBytesLenPure_lt_iff fb gb n).mp hg
  refine ⟨rfl, hf, hb, ?_⟩
  have hgb : ¬ gb < 128 := by omega
  simp [rlpBytesLenPure, rlpHeaderLenPure, hf, hgb]

private theorem rlpBytesLenPure_le_high (fb n : Nat) :
    rlpBytesLenPure fb n ≤ rlpBytesLenPure 128 n := by
  have h := (rlpBytesLenPure_bounds fb n).2.1
  simpa only [rlpBytesLenPure, Nat.lt_irrefl, and_false, ↓reduceIte] using h

private theorem finishWriteLen_le_payload_add_one {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (fr : Nat)
    (hfr : ValidRlpFrame s Nd fr) :
    finishWriteLen s fr (memW s (fr + 8)) ≤
      finishPayloadLen s fr (memW s (fr + 8)) + 1 := by
  obtain ⟨_, _, _, _, hk1, hk3, _, _, hbranch, hleaf, hext, _⟩ := hfr
  by_cases h3 : memW s (memW s (fr + 8)) = 3
  · have h2 : memW s (memW s (fr + 8)) ≠ 2 := by omega
    simp [finishWriteLen, finishPayloadLen, h3, h2, hbranch h3]
  · by_cases h2 : memW s (memW s (fr + 8)) = 2
    · obtain ⟨_, _, _, _, _, hpay⟩ := hext h2
      have h1 : memW s (memW s (fr + 8)) ≠ 1 := by omega
      simp [finishWriteLen, finishPayloadLen, h3, h2, h1, hpay]
    · have h1 : memW s (memW s (fr + 8)) = 1 := by omega
      obtain ⟨_, _, _, _, _, hpay, _⟩ := hleaf h1
      unfold leafPayloadExact at hpay
      have hne3 : (1 : Nat) ≠ 3 := by decide
      have hne2 : (1 : Nat) ≠ 2 := by decide
      simp only [finishWriteLen, finishPayloadLen, h1, hne3, hne2, ↓reduceIte]
      omega

private theorem finishWriteLen_fits_alloc_of_slack {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (fr buf q : Nat)
    (hfr : ValidRlpFrame s Nd fr)
    (halloc : buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
      finishPayloadLen s fr (memW s (fr + 8)) < q)
    (hq : q ≤ heapLimit) :
    buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
      finishWriteLen s fr (memW s (fr + 8)) ≤ heapLimit := by
  have hwrite := finishWriteLen_le_payload_add_one s Nd fr hfr
  omega

private theorem finishWriteLen_fits_alloc_below_limit {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (fr buf q : Nat)
    (hfr : ValidRlpFrame s Nd fr)
    (halloc : buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
      finishPayloadLen s fr (memW s (fr + 8)) ≤ q)
    (hq : q < heapLimit) :
    buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
      finishWriteLen s fr (memW s (fr + 8)) ≤ heapLimit := by
  have hwrite := finishWriteLen_le_payload_add_one s Nd fr hfr
  omega

private theorem finishWriteLen_overflow_boundary {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (fr buf q : Nat)
    (hfr : ValidRlpFrame s Nd fr)
    (halloc : buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
      finishPayloadLen s fr (memW s (fr + 8)) ≤ q)
    (hq : q ≤ heapLimit)
    (hover : heapLimit <
      buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
        finishWriteLen s fr (memW s (fr + 8))) :
    q = heapLimit ∧
      buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
        finishPayloadLen s fr (memW s (fr + 8)) = heapLimit ∧
      finishWriteLen s fr (memW s (fr + 8)) =
        finishPayloadLen s fr (memW s (fr + 8)) + 1 ∧
      memW s (memW s (fr + 8)) = 1 := by
  have hwrite := finishWriteLen_le_payload_add_one s Nd fr hfr
  have hkind : memW s (memW s (fr + 8)) = 1 := by
    obtain ⟨_, _, _, _, hk1, hk3, _, _, hbranch, _, hext, _⟩ := hfr
    by_cases h3 : memW s (memW s (fr + 8)) = 3
    · have h2 : memW s (memW s (fr + 8)) ≠ 2 := by omega
      have h32 : (3 : Nat) ≠ 2 := by decide
      have hpay := hbranch h3
      have heq :
          finishWriteLen s fr (memW s (fr + 8)) =
            finishPayloadLen s fr (memW s (fr + 8)) := by
        simp [finishWriteLen, finishPayloadLen, h3, h2, h32, hpay]
      omega
    · by_cases h2 : memW s (memW s (fr + 8)) = 2
      · obtain ⟨_, _, _, _, _, hpay⟩ := hext h2
        have h1 : memW s (memW s (fr + 8)) ≠ 1 := by omega
        have h23 : (2 : Nat) ≠ 3 := by decide
        have h21 : (2 : Nat) ≠ 1 := by decide
        have heq :
            finishWriteLen s fr (memW s (fr + 8)) =
              finishPayloadLen s fr (memW s (fr + 8)) := by
          simp [finishWriteLen, finishPayloadLen, h3, h2, h1, h23, h21, hpay]
        omega
      · omega
  exact ⟨by omega, by omega, by omega, hkind⟩

private theorem allocated_disj_heapLimit_word {F : Type}
    (s : PanSemStateFiniteExact 64 F) (i : Ivl)
    (hA : ArenaOK s) (hsp : heapLimit < globN s "scratch_ptr")
    (hi : Allocated s i) : Disj (heapLimit, 8) i := by
  have hsp8 : globN s "scratch_ptr" % 8 = 0 := hA.2.2.2.2.2.2.2.1
  have hlimit8 : heapLimit % 8 = 0 := by decide
  rcases hi with hi | hi
  · exact Or.inr (Or.inr (Or.inr (hi.2.trans hA.2.1)))
  · exact Or.inr (Or.inr (Or.inl (by have := hi.1; omega)))

private theorem finishWriteLen_eq_payload {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (fr : Nat)
    (hfr : ValidRlpFrame s Nd fr) :
    finishWriteLen s fr (memW s (fr + 8)) =
      finishPayloadLen s fr (memW s (fr + 8)) := by
  obtain ⟨_, _, _, _, hk1, hk3, _, _, hbranch, hleaf, hext, _⟩ := hfr
  by_cases h3 : memW s (memW s (fr + 8)) = 3
  · have h2 : memW s (memW s (fr + 8)) ≠ 2 := by omega
    simp [finishWriteLen, finishPayloadLen, h3, h2, hbranch h3]
  · by_cases h2 : memW s (memW s (fr + 8)) = 2
    · obtain ⟨_, _, _, _, _, hpay⟩ := hext h2
      have h1 : memW s (memW s (fr + 8)) ≠ 1 := by omega
      simp [finishWriteLen, finishPayloadLen, h3, h2, h1, hpay]
    · have h1 : memW s (memW s (fr + 8)) = 1 := by omega
      obtain ⟨_, _, _, _, _, hpay, _⟩ := hleaf h1
      unfold leafPayloadExact at hpay
      simp [finishWriteLen, finishPayloadLen, h3, h2, h1, hpay]

private theorem finishWriteLen_fits_alloc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (fr buf q : Nat)
    (hfr : ValidRlpFrame s Nd fr)
    (halloc : buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
      finishPayloadLen s fr (memW s (fr + 8)) ≤ q)
    (hq : q ≤ heapLimit) :
    buf + rlpHeaderLenPure (finishPayloadLen s fr (memW s (fr + 8))) +
      finishWriteLen s fr (memW s (fr + 8)) ≤ heapLimit := by
  rw [finishWriteLen_eq_payload s Nd fr hfr]
  exact halloc.trans hq

private theorem nodeExtents_allocated {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (hN : NodeHeap s Nd) :
    ∀ o ∈ nodeExtents s Nd, o.2 ≠ 0 → Allocated s o := by
  intro o ho hpos
  obtain ⟨n, hn, ho⟩ := List.mem_flatMap.mp ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact (hN.1 n hn).2.1
  · unfold nodePath at hpos ⊢
    by_cases hk : (memW s n = 1 ∨ memW s n = 2) ∧ memW s (n + 40) ≠ 0
    · rw [if_pos hk]
      rcases (hN.1 n hn).2.2.2.2.2.2.1 hk.1 with hz | hp
      · exact False.elim (hk.2 hz)
      · exact hp.2.1
    · rw [if_neg hk] at hpos
      exact False.elim (hpos rfl)

private theorem nodeExtents_disj_heapLimit_word {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (hA : ArenaOK s) (hN : NodeHeap s Nd)
    (hsp : heapLimit < globN s "scratch_ptr") :
    ∀ o ∈ nodeExtents s Nd, Disj (heapLimit, 8) o := by
  intro o ho
  by_cases hz : o.2 = 0
  · exact Or.inr (Or.inl hz)
  · exact allocated_disj_heapLimit_word s o hA hsp
      (nodeExtents_allocated s Nd hN o ho hz)

private def finishAfterLoads : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__node_rlp_finish with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ body))) => body
  | _ => .skip

private theorem eval__node_rlp_finish_loads {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (frw nodew : BitVec 64)
    (hN : NodeHeap s Nd) (hfr : ValidRlpFrame s Nd frw.toNat)
    (hnode : memW s (frw.toNat + 8) = nodew.toNat)
    (hfr_loc : s.locals.lookup (ofString "fr") = some (.val (.word frw)))
    (hnode_loc : s.locals.lookup (ofString "node") = some (.val (.word nodew))) :
    ∃ kw payw cbufw clenw : BitVec 64,
      kw.toNat = memW s nodew.toNat ∧
      payw.toNat = memW s (frw.toNat + 40) ∧
      cbufw.toNat = memW s (frw.toNat + 24) ∧
      clenw.toNat = memW s (frw.toNat + 32) ∧
      let entry := setVarHOLFinite (ofString "clen") (.val (.word clenw))
        (setVarHOLFinite (ofString "cbuf") (.val (.word cbufw))
          (setVarHOLFinite (ofString "payload") (.val (.word payw))
            (setVarHOLFinite (ofString "k") (.val (.word kw)) s)))
      let outer := evaluateHOLFiniteState s
        (sourceFnBody Guest.Software.guestFn__node_rlp_finish)
      let inner := evaluateHOLFiniteState entry finishAfterLoads
      outer.1 = inner.1 ∧ outer.2.memory = inner.2.memory ∧
        outer.2.globals = inner.2.globals ∧ outer.2.be = inner.2.be ∧
        outer.2.memaddrs = inner.2.memaddrs ∧ outer.2.code = inner.2.code ∧
        outer.2.shMemaddrs = inner.2.shMemaddrs ∧ outer.2.baseAddr = inner.2.baseAddr ∧
        outer.2.structs = inner.2.structs := by
  have hn : nodew.toNat ∈ Nd := hnode ▸ hfr.2.2.2.1
  obtain ⟨_, _, hin, hw, _⟩ := hN.1 _ hn
  have hlimit : heapLimit < 2 ^ 64 := by decide
  have hscratch : scratchEnd < 2 ^ 64 := by decide
  have hsize := nodeSize_ge32 (memW s nodew.toNat)
  have hnode_hi : nodew.toNat + nodeSize (memW s nodew.toNat) ≤ 2 ^ 64 := by
    have := hin.2
    dsimp [nodeIvl] at this
    omega
  have hfr_hi : frw.toNat + 48 ≤ 2 ^ 64 :=
    hfr.2.1.2.trans (Nat.le_of_lt hscratch)
  obtain ⟨kw, hkw, he0⟩ := eval_dec_load_memW_of_wordsOK s nodew 0
    (nodeSize (memW s nodew.toNat)) (ofString "k")
    (.op .add [.var .local (ofString "node"), .const 0])
    (.dec (ofString "payload") .one
      (.load .one (.op .add [.var .local (ofString "fr"), .const 40]))
      (.dec (ofString "cbuf") .one
        (.load .one (.op .add [.var .local (ofString "fr"), .const 24]))
        (.dec (ofString "clen") .one
          (.load .one (.op .add [.var .local (ofString "fr"), .const 32]))
          finishAfterLoads)))
    hw (by decide) (by omega) hnode_hi
    (by simp [evalHOLExact, evalListHOLExact, hnode_loc,
      wordOpHOL, wordOp, valueIsWord, valueWord])
  let s1 := setVarHOLFinite (ofString "k") (.val (.word kw)) s
  have hfr1 : s1.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hfr_loc, show ofString "k" ≠ ofString "fr" by decide]
  obtain ⟨payw, hpay, he1⟩ := eval_dec_load_memW_of_wordsOK s1 frw 40 48
    (ofString "payload") (.op .add [.var .local (ofString "fr"), .const 40])
    (.dec (ofString "cbuf") .one
      (.load .one (.op .add [.var .local (ofString "fr"), .const 24]))
      (.dec (ofString "clen") .one
        (.load .one (.op .add [.var .local (ofString "fr"), .const 32]))
        finishAfterLoads))
    hfr.2.2.1 (by decide) (by decide) hfr_hi
    (by simp [evalHOLExact, evalListHOLExact, hfr1,
      wordOpHOL, wordOp, valueIsWord, valueWord])
  let s2 := setVarHOLFinite (ofString "payload") (.val (.word payw)) s1
  have hfr2 : s2.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hfr1, show ofString "payload" ≠ ofString "fr" by decide]
  obtain ⟨cbufw, hcb, he2⟩ := eval_dec_load_memW_of_wordsOK s2 frw 24 48
    (ofString "cbuf") (.op .add [.var .local (ofString "fr"), .const 24])
    (.dec (ofString "clen") .one
      (.load .one (.op .add [.var .local (ofString "fr"), .const 32]))
      finishAfterLoads)
    hfr.2.2.1 (by decide) (by decide) hfr_hi
    (by simp [evalHOLExact, evalListHOLExact, hfr2,
      wordOpHOL, wordOp, valueIsWord, valueWord])
  let s3 := setVarHOLFinite (ofString "cbuf") (.val (.word cbufw)) s2
  have hfr3 : s3.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      hfr2, show ofString "cbuf" ≠ ofString "fr" by decide]
  obtain ⟨clenw, hcl, he3⟩ := eval_dec_load_memW_of_wordsOK s3 frw 32 48
    (ofString "clen") (.op .add [.var .local (ofString "fr"), .const 32])
    finishAfterLoads hfr.2.2.1 (by decide) (by decide) hfr_hi
    (by simp [evalHOLExact, evalListHOLExact, hfr3,
      wordOpHOL, wordOp, valueIsWord, valueWord])
  refine ⟨kw, payw, cbufw, clenw, by simpa using hkw, hpay, hcb, hcl, ?_⟩
  dsimp only
  have hb : sourceFnBody Guest.Software.guestFn__node_rlp_finish =
    .dec (ofString "k") .one
      (.load .one (.op .add [.var .local (ofString "node"), .const 0]))
      (.dec (ofString "payload") .one
        (.load .one (.op .add [.var .local (ofString "fr"), .const 40]))
        (.dec (ofString "cbuf") .one
          (.load .one (.op .add [.var .local (ofString "fr"), .const 24]))
          (.dec (ofString "clen") .one
            (.load .one (.op .add [.var .local (ofString "fr"), .const 32]))
            finishAfterLoads))) := rfl
  rw [hb, he0]; dsimp only
  rw [he1]; dsimp only
  rw [he2]; dsimp only
  rw [he3]; dsimp only
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def finishExtLenCont : ProgHOL 64 :=
  .assign .local (ofString "payload")
    (.op .add [.var .local (ofString "payload"), .var .local (ofString "rl")])

private theorem eval_finishExtLen_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (nodew frw kw payw cbufw clenw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hN : NodeHeap s Nd)
    (hnode : nodew.toNat ∈ Nd) (hk2 : memW s nodew.toNat = 2)
    (hln : s.locals.lookup (ofString "node") = some (.val (.word nodew)))
    (hlf : s.locals.lookup (ofString "fr") = some (.val (.word frw)))
    (hlk : s.locals.lookup (ofString "k") = some (.val (.word kw)))
    (hlp : s.locals.lookup (ofString "payload") = some (.val (.word payw)))
    (hlcb : s.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)))
    (hlcl : s.locals.lookup (ofString "clen") = some (.val (.word clenw)))
    (hpay : payw.toNat < 2 ^ 41)
    (hnone : (evaluateHOLFiniteState s
      (.decCall (ofString "rl") .one (ofString "node_ref_len")
        [.load .one (.op .add [.var .local (ofString "node"), .const 48])]
        finishExtLenCont)).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.decCall (ofString "rl") .one (ofString "node_ref_len")
        [.load .one (.op .add [.var .local (ofString "node"), .const 48])]
        finishExtLenCont)).2
    ∃ payw' : BitVec 64,
      payw'.toNat = payw.toNat + nodeRefBytes s (memW s (nodew.toNat + 48)) ∧
      post.globals = s.globals ∧ post.memory = s.memory ∧ post.be = s.be ∧
      HeapByteEff s post [] ["heap_ptr"] ∧
      post.locals.lookup (ofString "node") = some (.val (.word nodew)) ∧
      post.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
      post.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
      post.locals.lookup (ofString "payload") = some (.val (.word payw')) ∧
      post.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) ∧
      post.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
  intro post; dsimp only [post]
  obtain ⟨_, _, hin, hw, hext, _, _, _, _, _⟩ := hN.1 nodew.toNat hnode
  have hlimit : heapLimit < 2 ^ 64 := by decide
  have hsz : nodeSize (memW s nodew.toNat) = 56 := by unfold nodeSize; simp [hk2]
  obtain ⟨chw, hch, hch_nat⟩ := eval_load_memW_of_wordsOK (base := nodew) (off := 48)
    hw (by decide) (by change 48 + 8 ≤ nodeSize (memW s nodew.toNat); omega)
    (by have := hin.2; dsimp [nodeIvl] at this; omega)
    (e := .op .add [.var .local (ofString "node"), .const 48])
    (by simp [evalHOLExact, evalListHOLExact, hln, wordOpHOL, wordOp, valueIsWord, valueWord])
  have hch_nat' : chw.toNat = memW s (nodew.toNat + 48) := hch_nat
  have hroot : RootIn Nd chw.toNat := hch_nat' ▸ hext hk2
  have hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "rl") .one (ofString "node_ref_len")
        [.load .one (.op .add [.var .local (ofString "node"), .const 48])]
        finishExtLenCont)).1 ≠ some .timeOut := by
    rw [hnone]; simp
  have hdc0 := eval_decCall_node_ref_len_exact s Nd "rl"
      (.load .one (.op .add [.var .local (ofString "node"), .const 48])) chw
      finishExtLenCont [] ["heap_ptr"] hc hAR hN hroot hch hnt
  dsimp only at hdc0
  change (∃ _ _, _) ∨ _ at hdc0
  rcases hdc0 with
    ⟨rlw, mid, hrl, hmid_g, hmid_m, hmid_l, heff, _, hdc⟩ |
    ⟨hne, _, _, _, _⟩
  · have hmid_pay : mid.locals.lookup (ofString "payload") = some (.val (.word payw)) := by
      rw [hmid_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlp,
        show ofString "rl" ≠ ofString "payload" by decide]
    have hmid_rl : mid.locals.lookup (ofString "rl") = some (.val (.word rlw)) := by
      rw [hmid_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hasg : evaluateHOLFiniteState mid finishExtLenCont =
        (none, setVarHOLFinite (ofString "payload") (.val (.word (payw + rlw))) mid) := by
      unfold finishExtLenCont
      rw [evaluateHOLFiniteState_assign]
      simp [evalHOLExact, evalListHOLExact, hmid_pay, hmid_rl, wordOpHOL, wordOp,
        valueIsWord, valueWord, BitVec.add_zero, isValidValueHOLFinite, lookupKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setVarHOLFinite]
    have hsum : (payw + rlw).toNat = payw.toNat + rlw.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
      have := nodeRefBytes_le33 s chw.toNat
      omega
    let post0 := { setVarHOLFinite (ofString "payload") (.val (.word (payw + rlw))) mid with
      locals := HolFiniteMapExact.resVarEq
        (setVarHOLFinite (ofString "payload") (.val (.word (payw + rlw))) mid).locals
        (ofString "rl", s.locals.lookup (ofString "rl")) }
    have hpost0 : (evaluateHOLFiniteState s
        (.decCall (ofString "rl") .one (ofString "node_ref_len")
          [.load .one (.op .add [.var .local (ofString "node"), .const 48])]
          finishExtLenCont)).2 = post0 := by
      rw [hdc, hasg]
    rw [hpost0]
    refine ⟨payw + rlw, by rw [hsum, hrl, hch_nat], hmid_g, hmid_m, heff.be,
      heff.locals_clock _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
      simp [setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hln,
        show ofString "payload" ≠ ofString "node" by decide,
        show ofString "rl" ≠ ofString "node" by decide]
    · rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
      simp [setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hlf,
        show ofString "payload" ≠ ofString "fr" by decide,
        show ofString "rl" ≠ ofString "fr" by decide]
    · rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
      simp [setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hlk,
        show ofString "payload" ≠ ofString "k" by decide,
        show ofString "rl" ≠ ofString "k" by decide]
    · rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
      simp [setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hlcb,
        show ofString "payload" ≠ ofString "cbuf" by decide,
        show ofString "rl" ≠ ofString "cbuf" by decide]
    · rw [resVarEq_lookup_ne _ _ _ _ (by decide)]
      simp [setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hlcl,
        show ofString "payload" ≠ ofString "clen" by decide,
        show ofString "rl" ≠ ofString "clen" by decide]
  · exact absurd hnone hne

private def finishBranchLenCont : ProgHOL 64 :=
  .seq
    finishLenLoop
    (.decCall (ofString "vl2") .one (ofString "rlp_value_encoded_len")
      [.load .one (.op .add [.var .local (ofString "node"), .const 160]),
       .load .one (.op .add [.var .local (ofString "node"), .const 168])]
      (.assign .local (ofString "payload")
        (.op .add [.var .local (ofString "payload"), .var .local (ofString "vl2")])))

private theorem eval_finishBranchLen_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (nodew frw kw payw cbufw clenw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s) (hN : NodeHeap s Nd)
    (hnode : nodew.toNat ∈ Nd) (hk3 : memW s nodew.toNat = 3)
    (hln : s.locals.lookup (ofString "node") = some (.val (.word nodew)))
    (hlf : s.locals.lookup (ofString "fr") = some (.val (.word frw)))
    (hlk : s.locals.lookup (ofString "k") = some (.val (.word kw)))
    (hlp : s.locals.lookup (ofString "payload") = some (.val (.word payw)))
    (hlcb : s.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)))
    (hlcl : s.locals.lookup (ofString "clen") = some (.val (.word clenw)))
    (hpay : payw.toNat = 0)
    (hnone : (evaluateHOLFiniteState s
      (.dec (ofString "i") .one (.const 0) finishBranchLenCont)).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.dec (ofString "i") .one (.const 0) finishBranchLenCont)).2
    ∃ payw' : BitVec 64,
      payw'.toNat = payw.toNat + branchRefsLenSum s nodew.toNat 16 +
        rlpBytesLenPure
          (if 0 < memW s (nodew.toNat + 168) then memB s (memW s (nodew.toNat + 160)) else 0)
          (memW s (nodew.toNat + 168)) ∧
      (0 < memW s (nodew.toNat + 168) →
        s.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW s (nodew.toNat + 160))))) ∧
      post.globals = s.globals ∧ post.memory = s.memory ∧ post.be = s.be ∧
      HeapByteEff s post [] ["heap_ptr"] ∧
      post.locals.lookup (ofString "node") = some (.val (.word nodew)) ∧
      post.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
      post.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
      post.locals.lookup (ofString "payload") = some (.val (.word payw')) ∧
      post.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) ∧
      post.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
  intro post
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0) = some (.val (.word (0 : BitVec 64))) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  let s0 := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) s
  have hdec0 : evaluateHOLFiniteState s (.dec (ofString "i") .one (.const 0) finishBranchLenCont) =
      ((evaluateHOLFiniteState s0 finishBranchLenCont).1,
       { (evaluateHOLFiniteState s0 finishBranchLenCont).2 with
         locals := HolFiniteMapExact.resVarEq
           (evaluateHOLFiniteState s0 finishBranchLenCont).2.locals
           (ofString "i", s.locals.lookup (ofString "i")) }) := by
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev0]; dsimp only; rw [if_pos hsh0]
  have hnone' : (evaluateHOLFiniteState s0 finishBranchLenCont).1 = none := by
    rw [hdec0] at hnone; exact hnone
  clear hnone
  have hpostI : post = { (evaluateHOLFiniteState s0 finishBranchLenCont).2 with
      locals := HolFiniteMapExact.resVarEq
        (evaluateHOLFiniteState s0 finishBranchLenCont).2.locals
        (ofString "i", s.locals.lookup (ofString "i")) } := by
    dsimp only [post]; rw [hdec0]
  have hs0_n : s0.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hln,
      show ofString "i" ≠ ofString "node" by decide]
  have hs0_f : s0.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlf,
      show ofString "i" ≠ ofString "fr" by decide]
  have hs0_k : s0.locals.lookup (ofString "k") = some (.val (.word kw)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk,
      show ofString "i" ≠ ofString "k" by decide]
  have hs0_p : s0.locals.lookup (ofString "payload") = some (.val (.word payw)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlp,
      show ofString "i" ≠ ofString "payload" by decide]
  have hs0_cb : s0.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlcb,
      show ofString "i" ≠ ofString "cbuf" by decide]
  have hs0_cl : s0.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlcl,
      show ofString "i" ≠ ofString "clen" by decide]
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_AR : ArenaReady s0 := ⟨guestInv_setVar _ _ _ hAR.1, hAR.2⟩
  have heff0 : HeapByteEff s s0 [] ["heap_ptr"] :=
    (HeapByteEff.refl hAR [] ["heap_ptr"]).locals_clock _ _
  have hs0_N : NodeHeap s0 Nd :=
    (nodeHeap_of_heapByteEff_disj hAR hN heff0 (by simp)).1
  have hs0_k3 : memW s0 nodew.toNat = 3 := by
    simpa [s0, setVarHOLFinite, memW] using hk3
  obtain ⟨hn1, hn2, hseq⟩ := seq_none_rel s0 finishLenLoop _ hnone'
  obtain ⟨payw1, hpay1, hg1, hm1, hb1, heff1, hn1n, hn1f, hn1k, hn1p, hn1cb, hn1cl⟩ :=
    eval_finishLenLoop_none s0.clock s0 Nd nodew frw kw payw cbufw clenw 0
      (le_refl _) (by simpa [s0, setVarHOLFinite] using hc) hs0_AR hs0_N hnode hs0_k3
      (by decide) (by rw [hpay]; decide)
      hs0_n hs0_f hs0_k hs0_p hs0_cb hs0_cl hs0_i hn1
  let s1 := (evaluateHOLFiniteState s0 finishLenLoop).2
  have hs1_AR : ArenaReady s1 := heff1.arena
  obtain ⟨_, _, hin, hw, _, hbr, _, _, _, hbranch⟩ := hs0_N.1 nodew.toNat hnode
  have hlimit : heapLimit < 2 ^ 64 := by decide
  have hsz : nodeSize (memW s0 nodew.toNat) = 176 := by unfold nodeSize; simp [hs0_k3]
  have hnode_hi : nodew.toNat + nodeSize (memW s0 nodew.toNat) ≤ 2 ^ 64 := by
    have h1 : nodew.toNat + nodeSize (memW s0 nodew.toNat) ≤ heapLimit := hin.2
    omega
  have hmem1 : ∀ off, off % 8 = 0 → off + 8 ≤ 176 →
      memW s1 (nodew.toNat + off) = memW s0 (nodew.toNat + off) := by
    intro off hoff8 hoff
    unfold memW; rw [hm1]
  have hw1 : WordsOK s1 (nodeIvl s0 nodew.toNat) :=
    P3MptSet.wordsOK_transfer hs0_AR.1 hs1_AR.1 hw
  obtain ⟨vpw, hvp, hvp_nat⟩ := eval_load_memW_of_wordsOK (s := s1) (base := nodew) (off := 160)
    hw1 (by decide) (by change 160 + 8 ≤ nodeSize (memW s0 nodew.toNat); omega) hnode_hi
    (e := .op .add [.var .local (ofString "node"), .const 160])
    (by simp [s1, evalHOLExact, evalListHOLExact, hn1n, wordOpHOL, wordOp, valueIsWord, valueWord])
  obtain ⟨vlw, hvl, hvl_nat⟩ := eval_load_memW_of_wordsOK (s := s1) (base := nodew) (off := 168)
    hw1 (by decide) (by change 168 + 8 ≤ nodeSize (memW s0 nodew.toNat); omega) hnode_hi
    (e := .op .add [.var .local (ofString "node"), .const 168])
    (by simp [s1, evalHOLExact, evalListHOLExact, hn1n, wordOpHOL, wordOp, valueIsWord, valueWord])
  have hvp_nat' : vpw.toNat = memW s0 (nodew.toNat + 160) := by rw [hvp_nat, hmem1 160 (by decide) (by decide)]
  have hvl_nat' : vlw.toNat = memW s0 (nodew.toNat + 168) := by rw [hvl_nat, hmem1 168 (by decide) (by decide)]
  have hvl60 : vlw.toNat < 2 ^ 60 := by rw [hvl_nat']; exact (hbranch hs0_k3).trans (by decide)
  have hnt2 : (evaluateHOLFiniteState s1
      (.decCall (ofString "vl2") .one (ofString "rlp_value_encoded_len")
        [.load .one (.op .add [.var .local (ofString "node"), .const 160]),
         .load .one (.op .add [.var .local (ofString "node"), .const 168])]
        (.assign .local (ofString "payload")
          (.op .add [.var .local (ofString "payload"), .var .local (ofString "vl2")])))).1 ≠
      some .timeOut := by rw [hn2]; simp
  obtain ⟨vl2w, mid, hvl2, hdom, hmid_g, hmid_m, hmid_l, heff2, _, hdc⟩ :=
    eval_decCall_rlp_value_encoded_len_exact s1 "vl2"
      (.load .one (.op .add [.var .local (ofString "node"), .const 160]))
      (.load .one (.op .add [.var .local (ofString "node"), .const 168]))
      vpw vlw _ [] ["heap_ptr"] hs1_AR.1.code hs1_AR hvp hvl hvl60 hnt2 (Or.inr hn2)
  have hmid_p : mid.locals.lookup (ofString "payload") = some (.val (.word payw1)) := by
    rw [hmid_l]; simp [s1, HolFiniteMapExact.lookup_update, FUPDATE, hn1p,
      show ofString "vl2" ≠ ofString "payload" by decide]
  have hmid_v : mid.locals.lookup (ofString "vl2") = some (.val (.word vl2w)) := by
    rw [hmid_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hasg : evaluateHOLFiniteState mid
      (.assign .local (ofString "payload")
        (.op .add [.var .local (ofString "payload"), .var .local (ofString "vl2")])) =
      (none, setVarHOLFinite (ofString "payload") (.val (.word (payw1 + vl2w))) mid) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, hmid_p, hmid_v, wordOpHOL, wordOp,
      valueIsWord, valueWord, BitVec.add_zero, isValidValueHOLFinite, lookupKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setVarHOLFinite]
  have hsum : (payw1 + vl2w).toNat = payw1.toNat + vl2w.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
    have h16 : 16 - (0 : BitVec 64).toNat = 16 := rfl
    have hsum16 := branchRefsLenSum_le s0 nodew.toNat 16
    have hpay1' : payw1.toNat ≤ 33 * 16 := by
      rw [hpay1, hpay, Nat.zero_add, h16]; exact hsum16
    have hrlp : vl2w.toNat ≤ vlw.toNat + 9 := by
      rw [hvl2]; exact (rlpBytesLenPure_bounds _ vlw.toNat).2.2
    have hvl40 : vlw.toNat < 2 ^ 40 := by rw [hvl_nat']; exact hbranch hs0_k3
    have hvl9 : vlw.toNat + 9 ≤ 2 ^ 40 + 9 := Nat.le_of_lt (Nat.add_lt_add_right hvl40 9)
    have htot : payw1.toNat + vl2w.toNat < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.add_le_add hpay1' hrlp)
        (Nat.lt_of_le_of_lt (Nat.add_le_add_left hvl9 (33 * 16)) (by decide))
    exact htot
  let post0 := { setVarHOLFinite (ofString "payload") (.val (.word (payw1 + vl2w))) mid with
    locals := HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq
        (setVarHOLFinite (ofString "payload") (.val (.word (payw1 + vl2w))) mid).locals
        (ofString "vl2", s1.locals.lookup (ofString "vl2")))
      (ofString "i", s.locals.lookup (ofString "i")) }
  have hpost0 : post = post0 := by
    rw [hpostI, finishBranchLenCont, hseq, hdc, hasg]
  rw [hpost0]
  have hg0 : s0.globals = s.globals := rfl
  have hm0 : s0.memory = s.memory := rfl
  have hb0 : s0.be = s.be := rfl
  have hmem0 : memW s0 = memW s := rfl
  have hmemB0 : memB s0 = memB s := rfl
  have hs0_addr : s0.memaddrs = s.memaddrs := rfl
  have hdom' : 0 < memW s (nodew.toNat + 168) →
      s.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW s (nodew.toNat + 160)))) := by
    intro hpos
    have hpos' : 0 < vlw.toNat := by rw [hvl_nat', hmem0]; exact hpos
    have hb_eq : BitVec.ofNat 64 (memW s (nodew.toNat + 160)) = vpw := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, ← hmem0, ← hvp_nat', Nat.mod_eq_of_lt vpw.isLt]
    rw [hb_eq, ← hs0_addr, ← heff1.memaddrs]
    exact hdom hpos'
  refine ⟨payw1 + vl2w, ?_, hdom', hmid_g.trans hg1 |>.trans hg0, hmid_m.trans hm1 |>.trans hm0,
    heff2.be.trans hb1 |>.trans hb0, heff0.trans (heff1.trans (heff2.locals_clock _ _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsum, hpay1, hvl2, hvp_nat', hvl_nat', hmem0]
    have hmemB : memB s1 vpw.toNat = memB s0 vpw.toNat := by
      unfold memB; rw [hm1, hb1]
    have hmemB' : memB s1 (memW s (nodew.toNat + 160)) = memB s (memW s (nodew.toNat + 160)) := by
      rw [← hmem0, ← hvp_nat', hmemB, hmemB0]
    have h16 : 16 - (0 : BitVec 64).toNat = 16 := rfl
    have hbr0 : branchRefsLenSum s0 nodew.toNat 16 = branchRefsLenSum s nodew.toNat 16 := rfl
    rw [hmemB', h16, hbr0]
  · rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
    simp [s1, setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hn1n,
      show ofString "payload" ≠ ofString "node" by decide,
      show ofString "vl2" ≠ ofString "node" by decide]
  · rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
    simp [s1, setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hn1f,
      show ofString "payload" ≠ ofString "fr" by decide,
      show ofString "vl2" ≠ ofString "fr" by decide]
  · rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
    simp [s1, setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hn1k,
      show ofString "payload" ≠ ofString "k" by decide,
      show ofString "vl2" ≠ ofString "k" by decide]
  · rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
    simp [s1, setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hn1cb,
      show ofString "payload" ≠ ofString "cbuf" by decide,
      show ofString "vl2" ≠ ofString "cbuf" by decide]
  · rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
    simp [s1, setVarHOLFinite, hmid_l, HolFiniteMapExact.lookup_update, FUPDATE, hn1cl,
      show ofString "payload" ≠ ofString "clen" by decide,
      show ofString "vl2" ≠ ofString "clen" by decide]

/-! ## Main `_node_rlp_fill` loop: scan machinery (adapted from the R10 shard). -/

private def fillScanCond : ExpHOL 64 :=
  .op .and [.cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.const 16)),
    .cmp .notEqual (.const 0) (.cmp .equal (.var .local (ofString "found")) (.const 0))]

private def fillScanBody : ProgHOL 64 :=
  .seq (.assign .local (ofString "child")
    (.load .one (.op .add [.var .local (ofString "nd"), .const 32,
      .panop .mul [.var .local (ofString "i"), .const 8]])))
    (.seq (.assign .local (ofString "i")
      (.op .add [.var .local (ofString "i"), .const 1]))
      (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
        [.var .local (ofString "child")]))

private def FillScanReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ locN s "i" ≤ 16

private theorem fillSeq_none {F : Type} (s : PanSemStateFiniteExact 64 F) (p q : ProgHOL 64)
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

private theorem fillScan_advance {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (w : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hn : (evaluateHOLFiniteState s fillScanBody).1 = none) :
    (evaluateHOLFiniteState s fillScanBody).2.locals.lookup (ofString "i") =
      some (.val (.word (w + 1))) := by
  unfold fillScanBody at hn ⊢
  obtain ⟨hn1, hn2, heq⟩ := fillSeq_none _ _ _ hn
  rw [heq]
  obtain ⟨hn3, hn4, heq2⟩ := fillSeq_none _ _ _ hn2
  rw [heq2]
  rw [evaluate_avoidsLocal_flowing (ofString "i") _ (by decide) _ (Or.inl hn4)]
  have hkeep := evaluate_avoidsLocal_flowing (ofString "i") _ (by decide) s (Or.inl hn1)
  have hcount : CountedBody (ofString "i") 1
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) 0 :=
    CountedBody.incr
  exact (hcount.run _ ((evaluateHOLFiniteState_metadata s _).1.trans hc) w
    (hkeep.trans hi) (Nat.zero_le _)).2.2.2.2 hn3 |>.1

private theorem fillScan_active {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : FillScanReady s)
    (ha : LoopActive fillScanCond s) :
    ∃ w : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word w)) ∧ w.toNat < 16 := by
  obtain ⟨word, he, hw⟩ := ha
  rw [evalHOLFinite_eq_toExact] at he
  rcases hi : s.locals.lookup (ofString "i") with _ | vi
  · simp [fillScanCond, evalHOLExact, evalListHOLExact, hi] at he
  · rcases vi with ⟨⟨i⟩⟩ | fs | ⟨n, fs⟩
    · have hle : i.toNat ≤ 16 := by simpa [FillScanReady, locN, hi] using hP.2
      refine ⟨i, rfl, ?_⟩
      by_contra hn
      have hi16 : i = 16 := BitVec.eq_of_toNat_eq (by simpa using (show i.toNat = 16 by omega))
      subst hi16
      rcases hf : s.locals.lookup (ofString "found") with _ | vf
      · simp [fillScanCond, evalHOLExact, evalListHOLExact, hi, hf] at he
      · rcases vf with ⟨⟨f⟩⟩ | fs | ⟨n, fs⟩
        · simp [fillScanCond, evalHOLExact, evalListHOLExact, hi, hf,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
            Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, valueIsWord, valueWord,
            wordOpHOL, wordOp] at he
          exact hw he.symm
        · simp [fillScanCond, evalHOLExact, evalListHOLExact, hi, hf,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
            Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, valueIsWord, valueWord,
            wordOpHOL, wordOp] at he
        · simp [fillScanCond, evalHOLExact, evalListHOLExact, hi, hf,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
            Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, valueIsWord, valueWord,
            wordOpHOL, wordOp] at he
    · simp [fillScanCond, evalHOLExact, evalListHOLExact, hi] at he
    · simp [fillScanCond, evalHOLExact, evalListHOLExact, hi] at he

private theorem fillScan_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hP : FillScanReady s) (ha : LoopActive fillScanCond s)
    (hnone : (evaluateHOLFiniteState (decClockHOLFinite s) fillScanBody).1 = none) :
    FillScanReady (evaluateHOLFiniteState (decClockHOLFinite s) fillScanBody).2 ∧
      16 - locN (evaluateHOLFiniteState (decClockHOLFinite s) fillScanBody).2 "i" <
        16 - locN s "i" := by
  obtain ⟨i, hi, hil⟩ := fillScan_active s hP ha
  have hnew := fillScan_advance (decClockHOLFinite s) hc i hi hnone
  have hadd : (i + 1).toNat = i.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2^64; omega)
  have hnloc : locN (evaluateHOLFiniteState (decClockHOLFinite s) fillScanBody).2 "i" =
      i.toNat + 1 := by simp only [locN, hnew, hadd]
  have hiloc : locN s "i" = i.toNat := by simp only [locN, hi]
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_congr (s := s) rfl rfl rfl rfl hP.1), ?_⟩, ?_⟩
  · rw [hnloc]; omega
  · rw [hnloc, hiloc]; omega

private theorem fillScan_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn FillScanReady (.while fillScanCond fillScanBody)
      ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) := by
  apply TerminatingProgBoundedOn.while_rank (fun s => 16 - locN s "i")
  · intro F s hP
    exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hP.1, hP.2⟩
  · refine weakenGuard (P := FillScanReady) (Q := GuestInv) ?_ (fun s h => h.1)
    unfold fillScanBody
    refine TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
        (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
          (TerminatingProgBoundedOn.call_guestInv hn _ _))) (by omega)
  · intro F s hc hP ha
    exact Nat.sub_le _ _
  · intro F s hc hP ha hf
    have hnc := evaluate_noTopContinue fillScanBody (by rfl) (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) fillScanBody).1 = none :=
      hf.elim id (fun h => False.elim (hnc h))
    exact fillScan_step s hc hP ha hnone

/-- The saved child index of the current scratch frame is in range. -/
private def FillScanEntry : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ memW s (locN s "top" + 16) ≤ 16

private theorem fillScanEntry_locals : LocalsOnly ["top"] FillScanEntry := by
  intro F s ls k hl hs
  have ht := locN_congr s ls k "top" (hl "top" (by simp))
  refine ⟨guestInv_with_locals_clock s ls k hs.1, ?_⟩
  change memW s (locN { s with locals := ls, clock := k } "top" + 16) ≤ 16
  rw [ht]
  exact hs.2

private def fillScanProgram : ProgHOL 64 :=
  .dec (ofString "i") .one (.load .one (.op .add [.var .local (ofString "top"), .const 16]))
    (.seq (.while fillScanCond fillScanBody)
      (.store (.op .add [.var .local (ofString "top"), .const 16]) (.var .local (ofString "i"))))

private theorem fillScan_program_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn FillScanEntry fillScanProgram
      ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) := by
  unfold fillScanProgram
  refine TerminatingProgBoundedOn.mono_bound (dec_guard _ _ _ ?_
    (TerminatingProgBoundedOn.seq_guestInv_after (fillScan_bound hn) (fun s h => h.1)
      (straight _ rfl))) (by omega)
  intro F s v hs hv
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "top" 16 v hv
  refine ⟨guestInv_setVar _ _ _ hs.1, ?_⟩
  rw [locN_setVar_same, hw]
  exact hs.2

/-- Extract the two nested loops from the installed body without changing its AST. -/
private def fillBody : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__node_rlp_fill with
  | .decCall _ _ _ _ (.decCall _ _ _ _
      (.seq _ (.seq _ (.seq _ (.seq _ (.dec _ _ _ (.seq (.while _ b) _))))))) => b
  | _ => .skip

private def fillSearch : ProgHOL 64 :=
  match fillBody with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq p _)))) => p
  | _ => .skip

private def fillTail : ProgHOL 64 :=
  match fillBody with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ p)))) => p
  | _ => .skip

private theorem fillSearch_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn FillScanEntry fillSearch
      (max (max (K.«_node_needs_rlp» + 1) 0)
        (max ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) 0)) := by
  change TerminatingProgBoundedOn FillScanEntry
    (.ite _ (.ite _ (.seq _ (.seq _ (.call _ _ _))) .skip)
      (.ite _ fillScanProgram .skip)) _
  apply TerminatingProgBoundedOn.ite_on
  · apply TerminatingProgBoundedOn.ite_on
    · refine weakenGuard (P := FillScanEntry) (Q := GuestInv) ?_ (fun s h => h.1)
      exact TerminatingProgBoundedOn.mono_bound
        (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
          (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
            (TerminatingProgBoundedOn.call_guestInv hn _ _))) (by omega)
    · exact weakenGuard (straight _ rfl) (fun s h => h.1)
  · exact TerminatingProgBoundedOn.ite_on (fillScan_program_bound hn)
      (weakenGuard (straight _ rfl) (fun s h => h.1))

private theorem fillTail_bound
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish») :
    TerminatingProgBoundedOn GuestInv fillTail
      (max ((K.«scratch_alloc» + 1) + (K.«_node_rlp_begin» + 1)) (K.«_node_rlp_finish» + 1)) := by
  change TerminatingProgBoundedOn GuestInv (.ite _ (.decCall _ _ _ _
    (.seq _ (.seq _ (.seq _ (.seq (.call _ _ _) (.assign _ _ _))))))
    (.seq (.call _ _ _) (.assign _ _ _))) _
  apply TerminatingProgBoundedOn.ite_on
  · refine TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
        (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
          (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
            (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.call_guestInv hb _ _) (straight _ rfl)))))) (by omega)
  · exact TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv hf _ _) (straight _ rfl)) (by omega)

private def fillBodyCost : Nat :=
  max (max (K.«_node_needs_rlp» + 1) 0)
    (max ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) 0) +
  max ((K.«scratch_alloc» + 1) + (K.«_node_rlp_begin» + 1)) (K.«_node_rlp_finish» + 1)

private theorem fillBody_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp»)
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish») :
    TerminatingProgBoundedOn FillScanEntry fillBody fillBodyCost := by
  change TerminatingProgBoundedOn FillScanEntry (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
    (.dec _ _ _ (.seq fillSearch fillTail))))) _
  exact TerminatingProgBoundedOn.dec_onLocals fillScanEntry_locals _ (by decide) _ _
    (TerminatingProgBoundedOn.dec_onLocals fillScanEntry_locals _ (by decide) _ _
      (TerminatingProgBoundedOn.dec_onLocals fillScanEntry_locals _ (by decide) _ _
        (TerminatingProgBoundedOn.dec_onLocals fillScanEntry_locals _ (by decide) _ _
          (TerminatingProgBoundedOn.seq_guestInv_after (fillSearch_bound hn) (fun s h => h.1)
            (fillTail_bound ha hb hf)))))

/-- Remaining allocator capacity; either a scratch push or a nonempty encoding lowers it. -/
private def fillMeasure : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat :=
  fun s => heapLimit - globN s "heap_ptr" + (globN s "scratch_ptr" - scratchStart)

private theorem fillMeasure_le {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : ArenaReady s) : fillMeasure s ≤ 2 ^ 62 := by
  have hsp := hs.2.2.2.2.2.1
  dsimp only [fillMeasure, heapLimit, scratchStart, scratchEnd] at *
  omega

private theorem fillMeasure_decreases {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (ht : ArenaReady t) (hg : AllocatorGrows s t)
    (hstrict : globN s "heap_ptr" < globN t "heap_ptr" ∨
      globN t "scratch_ptr" < globN s "scratch_ptr") :
    fillMeasure t < fillMeasure s := by
  have hhp := ht.2.2.1
  have hsl : scratchStart ≤ globN t "scratch_ptr" := ht.2.2.2.1.trans ht.2.2.2.2.1
  rcases hg with ⟨hh, hsp⟩
  unfold fillMeasure
  omega

/-- Frame chain: the current frame, its parent, and so on, are all valid, and parent
pointers sit at or above `fr + 48` up to `sp0` (new frames are pushed at lower scratch addresses). -/
private inductive ChainOK {F : Type} (sp0 : Nat) (Nd : List Nat) :
    PanSemStateFiniteExact 64 F → Nat → Prop
  | chainNil : ∀ s : PanSemStateFiniteExact 64 F, ChainOK sp0 Nd s 0
  | chainDone : ∀ (s : PanSemStateFiniteExact 64 F) (fr : Nat), ValidRlpFrame s Nd fr →
      fr + 48 ≤ sp0 → memW s (fr + 0) = 0 → ChainOK sp0 Nd s fr
  | chainStep : ∀ (s : PanSemStateFiniteExact 64 F) (fr p : Nat), ValidRlpFrame s Nd fr →
      memW s (fr + 0) = p → fr + 48 ≤ p → ChainOK sp0 Nd s p → ChainOK sp0 Nd s fr

private theorem chainOK_with_locals_clock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (sp0 : Nat) (Nd : List Nat) {fr : Nat}
    (h : ChainOK sp0 Nd s fr) :
    ChainOK sp0 Nd { s with locals := ls, clock := k } fr := by
  induction h with
  | chainNil =>
    exact ChainOK.chainNil ({ s with locals := ls, clock := k } : PanSemStateFiniteExact 64 F)
  | chainDone fr' hv hsp0 hl =>
    exact ChainOK.chainDone ({ s with locals := ls, clock := k } : PanSemStateFiniteExact 64 F) fr'
      hv hsp0 hl
  | chainStep fr' p hv hl hle _ ih =>
    exact ChainOK.chainStep ({ s with locals := ls, clock := k } : PanSemStateFiniteExact 64 F) fr'
      p hv hl hle ih

/-- The main-loop invariant. -/
private def FillLoopInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ sp0 Nd, globN s "scratch_ptr" ≤ sp0 ∧ sp0 ≤ scratchEnd ∧
    NodeHeap s Nd ∧ KeccakBufsSafe s Nd ∧ NodeValuesSafe sp0 s Nd ∧
    (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      0 < (bufferRegion s gs).2 →
      (bufferRegion s gs).1 + (bufferRegion s gs).2 ≤ globN s "heap_ptr" ∨
        sp0 ≤ (bufferRegion s gs).1) ∧
    ChainOK sp0 Nd s (locN s "top")

private theorem fillLoopInv_locals : LocalsOnly ["top"] FillLoopInv := by
  intro F s ls k hl hs
  obtain ⟨ha, sp0, Nd, hsp, hsp_hi, hN, hK, hvs, hkc_sp0, hch⟩ := hs
  refine ⟨⟨guestInv_with_locals_clock s ls k ha.1, ha.2⟩,
    sp0, Nd, hsp, hsp_hi, hN, hK, hvs, hkc_sp0, ?_⟩
  have ht : locN { s with locals := ls, clock := k } "top" = locN s "top" :=
    locN_congr s ls k "top" (hl "top" (by simp))
  rw [show locN { s with locals := ls, clock := k } "top" = locN s "top" from ht]
  exact chainOK_with_locals_clock s ls k sp0 Nd hch

/-! ## `_node_rlp_finish` callee pieces: `rlp_list_header_len`, `alloc`, `rlp_encode_list_header`. -/

private theorem eval_decCall_rlp_list_header_len_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (nExp : ExpHOL 64)
    (n0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hnone : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [nExp] cont)).1 = none) :
    ∃ (hl : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      hl.toNat = rlpHeaderLenPure n0.toNat ∧
      1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      mid.globals = s.globals ∧ mid.memory = s.memory ∧ mid.be = s.be ∧
      mid.memaddrs = s.memaddrs ∧
      mid.locals = s.locals.update (ofString lname, .val (.word hl)) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnone ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [nExp] =
      some [.val (.word n0)] := by simp [evalListHOLFinite, evalListHOLExact, hn]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_list_header_len")
    (ofString "payload_len") (sourceFnBody Guest.Software.guestFn_rlp_list_header_len) n0
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_list_header_len)
  simp only [ha, hlk] at hnone ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnone
  · simp only [hcz, ↓reduceIte] at hnone ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "payload_len", ValueHOL.val (.word n0)) with hcmap
    set ent := callEntryStateHOLFinite s cmap with hent
    have hent_pl : ent.locals.lookup (ofString "payload_len") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hwb : sourceFnBody Guest.Software.guestFn_rlp_list_header_len =
        .call none (ofString "rlp_header_len") [.var .local (ofString "payload_len")] := rfl
    rw [hwb, evaluateHOLFiniteState_call] at hnone ⊢
    have ha1 : evalListHOLFinite ent
        (h := fun a => Classical.propDecidable (ent.memaddrs a))
        [.var .local (ofString "payload_len")] = some [.val (.word n0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_pl]
    have hlk1 := pan_one_word_lookup ent.code.lookup (ofString "rlp_header_len")
      (ofString "n") (sourceFnBody Guest.Software.guestFn_rlp_header_len) n0
      (by rw [show ent.code = s.code from rfl, hcode]; exact WkBlockTxEnc.lookup_rlp_header_len)
    simp only [ha1, hlk1] at hnone ⊢
    by_cases hcz1 : ent.clock = 0
    · simp [hcz1] at hnone
    · simp only [hcz1, ↓reduceIte] at hnone ⊢
      set cmap1 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word n0)) with hcmap1
      set ent1 := callEntryStateHOLFinite ent cmap1 with hent1
      have hent1_n : ent1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [ent1, cmap1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hcode1 : ent1.code = originalRuntimeCode := by rw [hent1, hent]; exact hcode
      rcases hcal : evaluateHOLFiniteState ent1
        (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rc, sc⟩
      simp only [hcal] at hnone ⊢
      have hnt1 : rc ≠ some .timeOut := by
        rintro rfl; simp at hnone
      cases rc with
      | none => simp at hnone
      | some r =>
        cases r with
        | returned v =>
          obtain ⟨hrv, hloc⟩ := eval_rlp_header_len_body_exact ent1 n0 hcode1 hent1_n
            (by rw [hcal]; exact hnt1)
          rw [hcal] at hrv hloc
          dsimp only at hrv hloc
          injection hrv with hrv1
          injection hrv1 with hv_eq; subst hv_eq
          have hsh : shapeEqHOL (shapeOfHOLExact
            (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat))) : ValueHOL 64)) .one =
            true := by simp [shapeOfHOLExact, shapeEqHOL]
          simp only [hsh, ↓reduceIte] at hnone ⊢
          let hl := BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat)
          let mid := setVarHOLFinite (ofString lname) (.val (.word hl))
            { sc with locals := s.locals }
          have hG_sc : GuestInv sc := by
            have hg := (M13.evaluateHOLFiniteState_guestInv_be ent1
              (sourceFnBody Guest.Software.guestFn_rlp_header_len)
              (guestInv_callEntry ent cmap1 (guestInv_callEntry s cmap hAR.1))).1
            rw [hcal] at hg; exact hg
          have hG_mid : GuestInv mid :=
            guestInv_setVar _ _ _ (guestInv_with_locals_clock sc s.locals sc.clock hG_sc)
          have hmid_g : mid.globals = s.globals := by
            simp only [mid, setVarHOLFinite]
            show sc.globals = s.globals
            have h1 : sc.globals = ent1.globals := by rw [hloc]
            have h2 : ent1.globals = ent.globals := rfl
            have h3 : ent.globals = s.globals := rfl
            rw [h1, h2, h3]
          have hmid_m : mid.memory = s.memory := by
            simp only [mid, setVarHOLFinite]
            show sc.memory = s.memory
            have h1 : sc.memory = ent1.memory := by rw [hloc]
            have h2 : ent1.memory = ent.memory := rfl
            have h3 : ent.memory = s.memory := rfl
            rw [h1, h2, h3]
          have hmid_b : mid.be = s.be := by
            simp only [mid, setVarHOLFinite]
            show sc.be = s.be
            have h1 : sc.be = ent1.be := by rw [hloc]
            have h2 : ent1.be = ent.be := rfl
            have h3 : ent.be = s.be := rfl
            rw [h1, h2, h3]
          have hmid_ma : mid.memaddrs = s.memaddrs := by
            simp only [mid, setVarHOLFinite]
            show sc.memaddrs = s.memaddrs
            have h1 : sc.memaddrs = ent1.memaddrs := by rw [hloc]
            have h2 : ent1.memaddrs = ent.memaddrs := rfl
            have h3 : ent.memaddrs = s.memaddrs := rfl
            rw [h1, h2, h3]
          have hbv : hl.toNat = rlpHeaderLenPure n0.toNat := by
            rw [BitVec.toNat_ofNat]
            have hbds := rlpHeaderLenPure_bounds n0.toNat
            exact Nat.mod_eq_of_lt (by omega)
          refine ⟨hl, mid, hbv, by rw [hbv]; have := rlpHeaderLenPure_bounds n0.toNat; omega,
            by rw [hbv]; have := rlpHeaderLenPure_bounds n0.toNat; omega,
            hmid_g, hmid_m, hmid_b, hmid_ma, rfl, ?_, ?_, rfl⟩
          · refine ⟨⟨hG_mid, arenaOK_congr_globals hmid_g hAR.2⟩, hmid_ma,
              by unfold globN; rw [hmid_g],
              by unfold globN; rw [hmid_g],
              by unfold globN; rw [hmid_g],
              hmid_b, fun k _ => by rw [hmid_g],
              fun a h => by rw [hmid_m] at h; exact absurd rfl h,
              fun a h => by rw [hmid_m] at h; exact absurd rfl h,
              fun b _ h => by unfold memB at h; rw [hmid_m, hmid_b] at h; exact absurd rfl h⟩
          · intro hcon
            have h2 : (evaluateHOLFiniteState mid cont).1 = none := hnone
            rw [h2] at hcon; simp at hcon
        | _ => simp at hnone

private theorem eval_decCall_alloc_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (nExp : ExpHOL 64)
    (n : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n)))
    (hnone : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1 = none) :
    ∃ (bufw q : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      bufw.toNat = globN s "heap_ptr" ∧
      bufw.toNat % 8 = 0 ∧
      q.toNat = (globN s "heap_ptr" + n.toNat + 7) / 8 * 8 ∧
      globN s "heap_ptr" + n.toNat ≤ q.toNat ∧
      q.toNat ≤ heapLimit ∧
      globN mid "heap_ptr" = q.toNat ∧
      mid.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      mid.memory = s.memory ∧ mid.be = s.be ∧
      mid.locals = s.locals.update (ofString lname, .val (.word bufw)) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  obtain ⟨hp, hhp, hhp_nat⟩ := global_heap_ptr_word s hAR.2
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnone ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [nExp] =
      some [.val (.word n)] := by simp [evalListHOLFinite, evalListHOLExact, hn]
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
        simp only [hsh, ↓reduceIte] at hnone ⊢
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
        have hmid_mem : mid.memory = s.memory := by
          change sa.memory = s.memory; exact hm_sa
        have hmid_be : mid.be = s.be := by
          change sa.be = s.be
          rw [hgb.2]; rfl
        have hmid_ma : mid.memaddrs = s.memaddrs := by
          change sa.memaddrs = s.memaddrs
          rw [hgb.1.memaddrs, hAR.1.memaddrs]
        refine ⟨hp, q, mid, hhp_nat, ?_, by rw [← hhp_nat]; exact hq_nat,
          by rw [← hhp_nat]; exact hpq, hqc, hmid_hp, hg_sa, hmid_mem, hmid_be,
          rfl, ?_, ?_, rfl⟩
        · rw [hhp_nat]; exact hAR.2.2.2.2.2.2.1
        · refine ⟨hAR_mid, hmid_ma, ?_, hmid_fp, ?_, hmid_be, ?_,
            fun a h => False.elim (h (by rw [hmid_mem] at h; exact absurd rfl h)),
            fun a h => False.elim (h (by rw [hmid_mem] at h; exact absurd rfl h)),
            fun b _ h => False.elim (h (by
              unfold memB
              rw [hmid_mem, hmid_be]))⟩
          · rw [← hhp_nat, hmid_hp]; omega
          · rw [hmid_sp]
          · intro k hk
            have hne : k ≠ ofString "heap_ptr" := fun heq =>
              hk (List.mem_map.2 ⟨"heap_ptr", hgw, heq.symm⟩)
            change s.globals.lookup k = sa.globals.lookup k
            rw [hg_sa]; simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
        · intro hcon
          have h2 : (evaluateHOLFiniteState mid cont).1 = none := hnone
          rw [h2] at hcon; simp at hcon
      | _ => simp at hnone

private theorem eval_call_none_rlp_encode_list_header {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp nExp : ExpHOL 64)
    (dst0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure n0.toNat ≤ ivl.1 + ivl.2)
    (hnone : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_encode_list_header") [dstExp, nExp])).1 = none) :
    ∃ post : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "rlp_encode_list_header") [dstExp, nExp])) =
        (none, post) ∧
      post.locals = s.locals ∧ post.globals = s.globals ∧
      post.be = s.be ∧ post.memaddrs = s.memaddrs ∧
      M11.ByteRegionEffect s post Rl := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, nExp] = some [.val (.word dst0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hn]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_list_header")
    (ofString "dst") (ofString "payload_len")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_list_header) dst0 n0
    (by decide)
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_encode_list_header)
  simp only [ha, hlk] at hnone ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnone
  · simp only [hcz, ↓reduceIte] at hnone ⊢
    set cmap2 := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "payload_len", ValueHOL.val (.word n0)) with hcmap2
    set ent2 := callEntryStateHOLFinite s cmap2 with hent2
    have hent2_dst : ent2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "payload_len" ≠ ofString "dst" by decide]
    have hent2_pl : ent2.locals.lookup (ofString "payload_len") = some (.val (.word n0)) := by
      simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hwb : sourceFnBody Guest.Software.guestFn_rlp_encode_list_header =
        .call none (ofString "rlp_write_header")
          [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] := rfl
    rw [hwb, evaluateHOLFiniteState_call] at hnone ⊢
    have ha3 : evalListHOLFinite ent2
        (h := fun a => Classical.propDecidable (ent2.memaddrs a))
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] =
        some [.val (.word dst0), .val (.word 192), .val (.word n0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent2_dst, hent2_pl]
    have hlk3 := pan_three_word_lookup ent2.code.lookup (ofString "rlp_write_header")
      (ofString "dst") (ofString "base") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 192 n0
      (by decide) (by decide) (by decide)
      (by rw [show ent2.code = s.code from rfl, hcode]; exact M11.lookup_rlp_write_header)
    simp only [ha3, hlk3] at hnone ⊢
    by_cases hcz2 : ent2.clock = 0
    · simp [hcz2] at hnone
    · simp only [hcz2, ↓reduceIte] at hnone ⊢
      set cmap3 := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "base", ValueHOL.val (.word 192))).update
        (ofString "n", ValueHOL.val (.word n0)) with hcmap3
      set ent3 := callEntryStateHOLFinite ent2 cmap3 with hent3
      have hent3_dst : ent3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [ent3, cmap3, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "base" ≠ ofString "dst" by decide,
          show ofString "n" ≠ ofString "dst" by decide]
      have hent3_base : ent3.locals.lookup (ofString "base") = some (.val (.word 192)) := by
        simp [ent3, cmap3, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "base" by decide]
      have hent3_n : ent3.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [ent3, cmap3, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hcode3 : ent3.code = originalRuntimeCode := by rw [hent3, hent2]; exact hcode
      have hma3 : ent3.memaddrs = ordinaryDomain := by
        rw [show ent3.memaddrs = s.memaddrs from rfl]; exact hAR.1.memaddrs
      rcases hcal3 : evaluateHOLFiniteState ent3
        (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rc3, sc3⟩
      simp only [hcal3] at hnone ⊢
      have hnt3 : rc3 ≠ some .timeOut := by
        rintro rfl; simp at hnone
      cases rc3 with
      | none => simp at hnone
      | some r =>
        cases r with
        | returned rv =>
          have hres := eval_rlp_write_header_body_exact ent3 dst0 192 n0 Rl hcode3 hma3
            hent3_dst hent3_base hent3_n hin_ivl (by rw [hcal3]; exact hnt3)
          rw [hcal3] at hres; dsimp only at hres
          obtain ⟨hrv, -, -⟩ := hres.1 rv rfl
          rw [hrv] at hnone ⊢
          have hsh : shapeEqHOL (shapeOfHOLExact
            (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat))) : ValueHOL 64)) .one =
            true := by simp [shapeOfHOLExact, shapeEqHOL]
          simp only [hsh, ↓reduceIte] at hnone ⊢
          have heff2 : M11.ByteRegionEffect ent3 sc3 Rl := (hres.1 rv rfl).2.2
          refine ⟨{ sc3 with locals := s.locals }, by rfl, rfl,
            heff2.globals.trans rfl, heff2.be.trans rfl, heff2.memaddrs.trans rfl, ?_⟩
          exact ((M11.ByteRegionEffect.refl s Rl).with_locals_clock ent2.locals ent2.clock).trans
            ((M11.ByteRegionEffect.refl ent2 Rl).with_locals_clock ent3.locals ent3.clock) |>.trans
            heff2 |>.with_locals_clock _ _
        | _ => simp at hnone

/-! ## Generalized (`hcase`) versions of the `_node_rlp_finish` decCall pieces. -/

private theorem eval_decCall_rlp_list_header_len_exact' {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (nExp : ExpHOL 64)
    (n0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hcase : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [nExp] cont)).1 = none ∨
      ∃ rv : ValueHOL 64, (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [nExp] cont)).1 =
        some (.returned rv)) :
    ∃ (hl : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      hl.toNat = rlpHeaderLenPure n0.toNat ∧
      1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      mid.globals = s.globals ∧ mid.memory = s.memory ∧ mid.be = s.be ∧
      mid.memaddrs = s.memaddrs ∧
      mid.locals = s.locals.update (ofString lname, .val (.word hl)) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hcase ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [nExp] =
      some [.val (.word n0)] := by simp [evalListHOLFinite, evalListHOLExact, hn]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_list_header_len")
    (ofString "payload_len") (sourceFnBody Guest.Software.guestFn_rlp_list_header_len) n0
    (by rw [hcode]; exact WkBlockTxEnc.lookup_rlp_list_header_len)
  simp only [ha, hlk] at hcase ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hcase
  · simp only [hcz, ↓reduceIte] at hcase ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "payload_len", ValueHOL.val (.word n0)) with hcmap
    set ent := callEntryStateHOLFinite s cmap with hent
    have hent_pl : ent.locals.lookup (ofString "payload_len") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hwb : sourceFnBody Guest.Software.guestFn_rlp_list_header_len =
        .call none (ofString "rlp_header_len") [.var .local (ofString "payload_len")] := rfl
    rw [hwb, evaluateHOLFiniteState_call] at hcase ⊢
    have ha1 : evalListHOLFinite ent
        (h := fun a => Classical.propDecidable (ent.memaddrs a))
        [.var .local (ofString "payload_len")] = some [.val (.word n0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_pl]
    have hlk1 := pan_one_word_lookup ent.code.lookup (ofString "rlp_header_len")
      (ofString "n") (sourceFnBody Guest.Software.guestFn_rlp_header_len) n0
      (by rw [show ent.code = s.code from rfl, hcode]; exact WkBlockTxEnc.lookup_rlp_header_len)
    simp only [ha1, hlk1] at hcase ⊢
    by_cases hcz1 : ent.clock = 0
    · simp [hcz1] at hcase
    · simp only [hcz1, ↓reduceIte] at hcase ⊢
      set cmap1 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word n0)) with hcmap1
      set ent1 := callEntryStateHOLFinite ent cmap1 with hent1
      have hent1_n : ent1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [ent1, cmap1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hcode1 : ent1.code = originalRuntimeCode := by rw [hent1, hent]; exact hcode
      rcases hcal : evaluateHOLFiniteState ent1
        (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rc, sc⟩
      simp only [hcal] at hcase ⊢
      have hnt1 : rc ≠ some .timeOut := by
        rintro rfl; simp at hcase
      cases rc with
      | none => simp at hcase
      | some r =>
        cases r with
        | returned v =>
          obtain ⟨hrv, hloc⟩ := eval_rlp_header_len_body_exact ent1 n0 hcode1 hent1_n
            (by rw [hcal]; exact hnt1)
          rw [hcal] at hrv hloc
          dsimp only at hrv hloc
          injection hrv with hrv1
          injection hrv1 with hv_eq; subst hv_eq
          have hsh : shapeEqHOL (shapeOfHOLExact
            (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat))) : ValueHOL 64)) .one =
            true := by simp [shapeOfHOLExact, shapeEqHOL]
          simp only [hsh, ↓reduceIte] at hcase ⊢
          let hl := BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat)
          let mid := setVarHOLFinite (ofString lname) (.val (.word hl))
            { sc with locals := s.locals }
          have hG_sc : GuestInv sc := by
            have hg := (M13.evaluateHOLFiniteState_guestInv_be ent1
              (sourceFnBody Guest.Software.guestFn_rlp_header_len)
              (guestInv_callEntry ent cmap1 (guestInv_callEntry s cmap hAR.1))).1
            rw [hcal] at hg; exact hg
          have hG_mid : GuestInv mid :=
            guestInv_setVar _ _ _ (guestInv_with_locals_clock sc s.locals sc.clock hG_sc)
          have hmid_g : mid.globals = s.globals := by
            simp only [mid, setVarHOLFinite]
            show sc.globals = s.globals
            have h1 : sc.globals = ent1.globals := by rw [hloc]
            have h2 : ent1.globals = ent.globals := rfl
            have h3 : ent.globals = s.globals := rfl
            rw [h1, h2, h3]
          have hmid_m : mid.memory = s.memory := by
            simp only [mid, setVarHOLFinite]
            show sc.memory = s.memory
            have h1 : sc.memory = ent1.memory := by rw [hloc]
            have h2 : ent1.memory = ent.memory := rfl
            have h3 : ent.memory = s.memory := rfl
            rw [h1, h2, h3]
          have hmid_b : mid.be = s.be := by
            simp only [mid, setVarHOLFinite]
            show sc.be = s.be
            have h1 : sc.be = ent1.be := by rw [hloc]
            have h2 : ent1.be = ent.be := rfl
            have h3 : ent.be = s.be := rfl
            rw [h1, h2, h3]
          have hmid_ma : mid.memaddrs = s.memaddrs := by
            simp only [mid, setVarHOLFinite]
            show sc.memaddrs = s.memaddrs
            have h1 : sc.memaddrs = ent1.memaddrs := by rw [hloc]
            have h2 : ent1.memaddrs = ent.memaddrs := rfl
            have h3 : ent.memaddrs = s.memaddrs := rfl
            rw [h1, h2, h3]
          have hbv : hl.toNat = rlpHeaderLenPure n0.toNat := by
            rw [BitVec.toNat_ofNat]
            have hbds := rlpHeaderLenPure_bounds n0.toNat
            exact Nat.mod_eq_of_lt (by omega)
          refine ⟨hl, mid, hbv, by rw [hbv]; have := rlpHeaderLenPure_bounds n0.toNat; omega,
            by rw [hbv]; have := rlpHeaderLenPure_bounds n0.toNat; omega,
            hmid_g, hmid_m, hmid_b, hmid_ma, rfl, ?_, ?_, rfl⟩
          · refine ⟨⟨hG_mid, arenaOK_congr_globals hmid_g hAR.2⟩, hmid_ma,
              by unfold globN; rw [hmid_g],
              by unfold globN; rw [hmid_g],
              by unfold globN; rw [hmid_g],
              hmid_b, fun k _ => by rw [hmid_g],
              fun a h => by rw [hmid_m] at h; exact absurd rfl h,
              fun a h => by rw [hmid_m] at h; exact absurd rfl h,
              fun b _ h => by unfold memB at h; rw [hmid_m, hmid_b] at h; exact absurd rfl h⟩
          · intro hcon
            have h2 : (evaluateHOLFiniteState mid cont).1 = none ∨
              ∃ rv : ValueHOL 64, (evaluateHOLFiniteState mid cont).1 =
                some (.returned rv) := hcase
            rcases h2 with h2 | ⟨rv, h2⟩
            · rw [h2] at hcon; simp at hcon
            · rw [h2] at hcon; simp at hcon
        | _ => simp at hcase

private theorem eval_decCall_alloc_exact' {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (nExp : ExpHOL 64)
    (n : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n)))
    (hcase : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1 = none ∨
      ∃ rv : ValueHOL 64, (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1 =
        some (.returned rv)) :
    ∃ (bufw q : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      bufw.toNat = globN s "heap_ptr" ∧
      bufw.toNat % 8 = 0 ∧
      q.toNat = (globN s "heap_ptr" + n.toNat + 7) / 8 * 8 ∧
      globN s "heap_ptr" + n.toNat ≤ q.toNat ∧
      q.toNat ≤ heapLimit ∧
      globN mid "heap_ptr" = q.toNat ∧
      mid.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      mid.memory = s.memory ∧ mid.be = s.be ∧
      mid.locals = s.locals.update (ofString lname, .val (.word bufw)) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  obtain ⟨hp, hhp, hhp_nat⟩ := global_heap_ptr_word s hAR.2
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hcase ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [nExp] =
      some [.val (.word n)] := by simp [evalListHOLFinite, evalListHOLExact, hn]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) n (by rw [hcode]; exact WkBlockTxEnc.lookup_alloc)
  simp only [ha, hlk] at hcase ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hcase
  · simp only [hcz, ↓reduceIte] at hcase ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word n))
    set ent := callEntryStateHOLFinite s cmap
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
    simp only [hal] at hcase ⊢
    cases ra with
    | none => simp at hcase
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
        simp only [hsh, ↓reduceIte] at hcase ⊢
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
        have hmid_mem : mid.memory = s.memory := by
          change sa.memory = s.memory; exact hm_sa
        have hmid_be : mid.be = s.be := by
          change sa.be = s.be
          rw [hgb.2]; rfl
        have hmid_ma : mid.memaddrs = s.memaddrs := by
          change sa.memaddrs = s.memaddrs
          rw [hgb.1.memaddrs, hAR.1.memaddrs]
        refine ⟨hp, q, mid, hhp_nat, ?_, by rw [← hhp_nat]; exact hq_nat,
          by rw [← hhp_nat]; exact hpq, hqc, hmid_hp, hg_sa, hmid_mem, hmid_be,
          rfl, ?_, ?_, rfl⟩
        · rw [hhp_nat]; exact hAR.2.2.2.2.2.2.1
        · refine ⟨hAR_mid, hmid_ma, ?_, hmid_fp, ?_, hmid_be, ?_,
            fun a h => False.elim (h (by rw [hmid_mem] at h; exact absurd rfl h)),
            fun a h => False.elim (h (by rw [hmid_mem] at h; exact absurd rfl h)),
            fun b _ h => False.elim (h (by
              unfold memB
              rw [hmid_mem, hmid_be]))⟩
          · rw [← hhp_nat, hmid_hp]; omega
          · rw [hmid_sp]
          · intro k hk
            have hne : k ≠ ofString "heap_ptr" := fun heq =>
              hk (List.mem_map.2 ⟨"heap_ptr", hgw, heq.symm⟩)
            change s.globals.lookup k = sa.globals.lookup k
            rw [hg_sa]; simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
        · intro hcon
          have h2 : (evaluateHOLFiniteState mid cont).1 = none ∨
            ∃ rv : ValueHOL 64, (evaluateHOLFiniteState mid cont).1 =
              some (.returned rv) := hcase
          rcases h2 with h2 | ⟨rv, h2⟩
          · rw [h2] at hcon; simp at hcon
          · rw [h2] at hcon; simp at hcon
      | _ => simp at hcase
/-! ## `_node_rlp_finish` body composition (round-4 session): the post-load tail
`hl → buf → bare header call → off → write phases → stores → return 0` as explicit
`ProgHOL` definitions, with an `rfl` transcription check against the AST-derived
`finishAfterLoads`. -/

private def finPhaseA : ProgHOL 64 :=
  .decCall (ofString "w") .one (ofString "rlp_encode_bytes")
    [.op .add [.var .local (ofString "buf"), .var .local (ofString "off")],
     .var .local (ofString "cbuf"), .var .local (ofString "clen")]
    (.seq
      (.assign .local (ofString "off")
        (.op .add [.var .local (ofString "off"), .var .local (ofString "w")]))
      (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
        (.decCall (ofString "w2") .one (ofString "rlp_encode_bytes")
          [.op .add [.var .local (ofString "buf"), .var .local (ofString "off")],
           .load .one (.op .add [.var .local (ofString "node"), .const 48]),
           .load .one (.op .add [.var .local (ofString "node"), .const 56])]
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w2")])))
        (.decCall (ofString "w3") .one (ofString "node_write_ref")
          [.load .one (.op .add [.var .local (ofString "node"), .const 48]),
           .op .add [.var .local (ofString "buf"), .var .local (ofString "off")]]
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w3")])))))

private def finPhaseB : ProgHOL 64 :=
  .dec (ofString "j") .one (.const 0)
    (.seq finishWriteLoop
      (.decCall (ofString "w5") .one (ofString "rlp_encode_bytes")
        [.op .add [.var .local (ofString "buf"), .var .local (ofString "off")],
         .load .one (.op .add [.var .local (ofString "node"), .const 160]),
         .load .one (.op .add [.var .local (ofString "node"), .const 168])]
        (.assign .local (ofString "off")
          (.op .add [.var .local (ofString "off"), .var .local (ofString "w5")]))))

private def finWrite : ProgHOL 64 :=
  .seq
    (.ite (.cmp .notEqual (.var .local (ofString "k")) (.const 3)) finPhaseA finPhaseB)
    (.seq
      (.store (.op .add [.var .local (ofString "node"), .const 8])
        (.var .local (ofString "buf")))
      (.seq
        (.store (.op .add [.var .local (ofString "node"), .const 16])
          (.var .local (ofString "off")))
        (.return (.const 0))))

/-- The write dispatch proper: the two branches of `finWrite` before the two outgoing-pointer
stores (which `finRest_tail_close` handles through `hret2`). -/
private def finDispatch : ProgHOL 64 :=
  .ite (.cmp .notEqual (.var .local (ofString "k")) (.const 3)) finPhaseA finPhaseB

private def finCallCont : ProgHOL 64 :=
  .dec (ofString "off") .one (.var .local (ofString "hl")) finWrite

private def finAllocCont : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "rlp_encode_list_header")
      [.var .local (ofString "buf"), .var .local (ofString "payload")])
    finCallCont

private def finHlCont : ProgHOL 64 :=
  .decCall (ofString "buf") .one (ofString "alloc")
    [.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]]
    finAllocCont

private def finRest : ProgHOL 64 :=
  .decCall (ofString "hl") .one (ofString "rlp_list_header_len")
    [.var .local (ofString "payload")] finHlCont

private def finLoadsRest : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal (.var .local (ofString "k")) (.const 2))
      (.decCall (ofString "rl") .one (ofString "node_ref_len")
        [.load .one (.op .add [.var .local (ofString "node"), .const 48])]
        finishExtLenCont)
      .skip)
    (.seq
      (.ite (.cmp .equal (.var .local (ofString "k")) (.const 3))
        (.dec (ofString "i") .one (.const 0) finishBranchLenCont)
        .skip)
      finRest)

private theorem finishAfterLoads_eq_finLoadsRest : finishAfterLoads = finLoadsRest := rfl

/-! ### Return-value kills for the tail's kill-free threading -/

private theorem assign_ne_returned {F : Type} (st : PanSemStateFiniteExact 64 F)
    (kind : VarKind) (x : MlS) (e : ExpHOL 64) (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState st (.assign kind x e)).1 = some (.returned rv)) :
    False := by
  rw [evaluateHOLFiniteState_assign] at hret
  split at hret <;> first | (split at hret <;> simp at hret) | simp at hret

private theorem twoAssigns_ne_returned {F : Type} (st : PanSemStateFiniteExact 64 F)
    (kind1 kind2 : VarKind) (x1 x2 : MlS) (e1 e2 : ExpHOL 64) (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState st
      (.seq (.assign kind1 x1 e1) (.assign kind2 x2 e2))).1 = some (.returned rv)) :
    False := by
  rw [evaluateHOLFiniteState_seq_line780] at hret
  generalize hA : evaluateHOLFiniteState st (.assign kind1 x1 e1) = ev1 at hret
  have hA1 : ev1.1 = none ∨ ev1.1 = some .error := by
    rw [← hA, evaluateHOLFiniteState_assign]
    split <;> first | (split <;> simp) | simp
  rcases hA1 with h | h
  · dsimp only at hret
    rw [h] at hret
    exact assign_ne_returned ev1.2 kind2 x2 e2 rv hret
  · simp [h] at hret

private theorem decCall_cont_ne_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (shape : ShapeHOL) (fname : String)
    (args : List (ExpHOL 64)) (cont : ProgHOL 64) (rv : ValueHOL 64)
    (hvals : ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rsh : ShapeHOL),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup (ofString fname) vals = some (body, callee, rsh))
    (hcont : ∀ st : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState st cont).1 ≠ some (.returned rv))
    (hret : (evaluateHOLFiniteState s
      (.decCall (ofString lname) shape (ofString fname) args cont)).1 = some (.returned rv)) :
    False := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  obtain ⟨vals, body, callee, rsh, ha, hlk⟩ := hvals
  simp only [ha, hlk] at hret
  by_cases hcz : s.clock = 0
  · simp [hcz] at hret
  · simp only [hcz, ↓reduceIte] at hret
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, sb⟩
    simp only [hb] at hret
    cases rb with
    | none => simp at hret
    | some o =>
        cases o with
        | error => simp at hret
        | timeOut => simp at hret
        | «break» => simp at hret
        | «continue» => simp at hret
        | returned val =>
            dsimp only at hret
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact val) shape &&
                shapeEqHOL (shapeOfHOLExact val) rsh) = true
            · rw [if_pos hsh] at hret
              dsimp only at hret
              exact hcont (setVarHOLFinite (ofString lname) val
                { sb with locals := s.locals }) hret
            · rw [if_neg hsh] at hret; simp at hret
        | exception e v => simp at hret
        | finalFfi ev => simp at hret

private theorem bareCall_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dstExp nExp : ExpHOL 64) (rv : ValueHOL 64)
    (hvals : ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rsh : ShapeHOL),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [dstExp, nExp] = some vals ∧
      lookupCodeHOLFinite s.code.lookup (ofString "rlp_encode_list_header") vals =
        some (body, callee, rsh))
    (hret : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_encode_list_header") [dstExp, nExp])).1
      = some (.returned rv)) : False := by
  rw [evaluateHOLFiniteState_call] at hret
  obtain ⟨vals, body, callee, rsh, ha, hlk⟩ := hvals
  simp only [ha, hlk] at hret
  by_cases hcz : s.clock = 0
  · simp [hcz] at hret
  · simp only [hcz, ↓reduceIte] at hret
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, sb⟩
    simp only [hb] at hret
    cases rb with
    | none => simp at hret
    | some o =>
        cases o with
        | error => simp at hret
        | timeOut => simp at hret
        | «break» => simp at hret
        | «continue» => simp at hret
        | returned val =>
            dsimp only at hret
            by_cases hsh : shapeEqHOL (shapeOfHOLExact val) rsh = true
            · rw [if_pos hsh] at hret; simp at hret
            · rw [if_neg hsh] at hret; simp at hret
        | exception e v => simp at hret
        | finalFfi ev => simp at hret


/-! ### The write loop never returns -/

private theorem finishWriteLoop_ne_returned {F : Type} :
    ∀ (clk : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (nodew frw kw payw cbufw clenw hlw bufw offw jw : BitVec 64)
      (bufLen : Nat) (rv : ValueHOL 64),
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
      (evaluateHOLFiniteState s finishWriteLoop).1 = some (.returned rv) →
      False := by
  intro clk
  induction clk with
  | zero =>
    intro s Nd nodew frw kw payw cbufw clenw hlw bufw offw jw bufLen rv
      hclk _ hAR _ _ _ _ hj16 _ _ _ _ _ _ _ _ _ _ _ _ hlj hret
    rw [finishWriteLoop, evaluateHOLFiniteState_while_fixClockRewrite] at hret
    have hcnd : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "j")) (.const 16)) =
        some (.val (.word (if jw.toNat < 16 then 1 else 0))) := by
      have h16 : (16#64).toNat = 16 := rfl
      simp [evalHOLFinite, evalHOLExact, hlj, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small jw 16#64 (by omega) (by decide), h16]
    rw [hcnd] at hret; dsimp only at hret
    by_cases hlt : jw.toNat < 16
    · have hk0 : s.clock = 0 := by omega
      simp [hlt, hk0] at hret
    · simp only [hlt, ↓reduceIte] at hret
      simp at hret
  | succ clk ih =>
    intro s Nd nodew frw kw payw cbufw clenw hlw bufw offw jw bufLen rv
      hclk hc hAR hN hKS hnode_in hk3 hj16 hbuf_hi hoff_fit hbuf_disj
      hln hlf hlk hlp hlcb hlcl hlhl hlb hlo hlj hret
    rw [finishWriteLoop, evaluateHOLFiniteState_while_fixClockRewrite, ← finishWriteLoop] at hret
    have hcnd : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.var .local (ofString "j")) (.const 16)) =
        some (.val (.word (if jw.toNat < 16 then 1 else 0))) := by
      have h16 : (16#64).toNat = 16 := rfl
      simp [evalHOLFinite, evalHOLExact, hlj, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small jw 16#64 (by omega) (by decide), h16]
    rw [hcnd] at hret; dsimp only at hret
    by_cases hlt : jw.toNat < 16
    · have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos hlt, if_pos h10] at hret
      by_cases hcz : s.clock = 0
      · simp [hcz] at hret
      · rw [if_neg hcz] at hret
        let sd := decClockHOLFinite s
        have hsd_AR : ArenaReady sd := localsFree_arenaReady s s.locals (s.clock - 1) hAR
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
        have hhl_he : heapLimit ≤ heapEnd := by rw [heapEnd_val]; decide
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
        simp only [hb_ev] at hret
        rw [hb_ev'] at hclk_b
        have hnt_b : rb ≠ some .timeOut := by
          rintro h; rw [h] at hret; simp at hret
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
            ⟨hne_b, hneret, hnbrk, hncont, _⟩
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
          dsimp only at hret
          let R24 := [(bufw.toNat, bufLen)] ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s)
          have heff_s_sb : HeapByteEff s sb R24 ["heap_ptr"] := by
            rw [hsb_eq]
            exact (((HeapByteEff.refl hAR R24 ["heap_ptr"]).locals_clock sd.locals sd.clock).trans heff_mid24).locals_clock _ _
          obtain ⟨hN_mid, hext_mid, _, hnrb_mid⟩ :=
            hpres_fn (fun e he _ o ho => by simp at he; subst he; exact hbuf_disj o ho)
              (fun o ho =>
                ⟨disj_comm ((hKS ("keccak_pad", 136) (by decide)).2 o ho),
                  disj_comm ((hKS ("keccak_st", 200) (by decide)).2 o ho)⟩)
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
          exact ih sb Nd nodew frw kw payw cbufw clenw hlw bufw (offw + w4w) (jw + 1) bufLen rv
            hclk_sb heff_s_sb.arena.1.code heff_s_sb.arena hN_sb hKS_sb hnode_in hsb_node_k
            (by rw [hjw1_nat]; omega) hbuf_hi
            (by rw [hoff_add_nat, hsum_sb_eq, hw4_eq', hjw1_nat]; omega)
            (fun o ho => by rw [hext_sb] at ho; exact hbuf_disj o ho)
            hsb_ln hsb_lf hsb_lk hsb_lp hsb_lcb hsb_lcl hsb_lhl hsb_lb hsb_lo hsb_lj hret
        · cases rb with
          | none =>
            change (evaluateHOLFiniteState sd finishWriteLoopBody).1 ≠ none at hne_b
            rw [hb_ev'] at hne_b
            exact hne_b rfl
          | some o =>
            cases o with
            | error => simp at hret
            | timeOut => simp at hret
            | «break» =>
              change (evaluateHOLFiniteState sd finishWriteLoopBody).1 ≠ some .break at hnbrk
              rw [hb_ev'] at hnbrk
              exact hnbrk rfl
            | «continue» =>
              change (evaluateHOLFiniteState sd finishWriteLoopBody).1 ≠ some .continue at hncont
              rw [hb_ev'] at hncont
              exact hncont rfl
            | returned val =>
              change (∀ v : ValueHOL 64,
                (evaluateHOLFiniteState sd finishWriteLoopBody).1 ≠ some (.returned v)) at hneret
              rw [hb_ev'] at hneret
              exact absurd rfl (hneret val)
            | exception e x => simp at hret
            | finalFfi ev => simp at hret
    · simp only [hlt, ↓reduceIte] at hret
      simp at hret


/-! ## Cycle 2b: `_node_rlp_finish` rest-tail (`finRest`) evaluation -/

/-! ### Shared closing block for the `finRest` branches

Given the state `sM` just before the two final stores (with the byte-effect
covering the node hash slots plus the freshly allocated rlp buffer plus the
keccak scratch buffers), this thread the two stores and the `return 0` into the
full `finRest` post-state and produces every component of the `finRest`
conclusion bundle. -/

private theorem finRest_tail_close {F : Type}
    (st : PanSemStateFiniteExact 64 F) (Nd : List Nat) (nodew bufw payv : BitVec 64)
    (hlBv : BitVec 64)
    (hhl1 : 1 ≤ hlBv.toNat)
    (htot40 : hlBv.toNat + payv.toNat < 2 ^ 40)
    (hAR : ArenaReady st) (hN : NodeHeap st Nd) (hKS : KeccakBufsSafe st Nd)
    (hnode_in : nodew.toNat ∈ Nd)
    (hbufw0 : bufw.toNat = globN st "heap_ptr")
    (hbuf_disj : ∀ o ∈ nodeExtents st Nd,
      Disj (globN st "heap_ptr", hlBv.toNat + payv.toNat) o)
    (sM : PanSemStateFiniteExact 64 F)
    (heffB : R16Shards.WkBlockTxEnc.HeapByteEff st sM
      (Nd.map (fun n => (n + 24, 8)) ++
        ([(globN st "heap_ptr", hlBv.toNat + payv.toNat)] ++ keccakBufIvls sM))
      ["heap_ptr"])
    (hW_M : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 → off + 8 ≤ nodeSize (memW st n) →
      off ≠ 24 → memW sM (n + off) = memW st (n + off))
    (hM_ln : sM.locals.lookup (ofString "node") = some (.val (.word nodew)))
    (hM_lb : sM.locals.lookup (ofString "buf") = some (.val (.word bufw)))
    (hoffF : ∃ offF : BitVec 64, sM.locals.lookup (ofString "off") = some (.val (.word offF)) ∧
      offF.toNat = hlBv.toNat + payv.toNat)
    (hM_hp : globN st "heap_ptr" < globN sM "heap_ptr")
    (hret2 : (evaluateHOLFiniteState sM
      (.seq (.store (.op .add [.var .local (ofString "node"), .const 8])
          (.var .local (ofString "buf")))
        (.seq (.store (.op .add [.var .local (ofString "node"), .const 16])
            (.var .local (ofString "off")))
          (.return (.const 0))))).1 = some (.returned (.val (.word 0))))
    (post : PanSemStateFiniteExact 64 F)
    (Lv : HolFiniteMapExact MlS (ValueHOL 64))
    (hpost : post = {(evaluateHOLFiniteState sM
      (.seq (.store (.op .add [.var .local (ofString "node"), .const 8])
          (.var .local (ofString "buf")))
        (.seq (.store (.op .add [.var .local (ofString "node"), .const 16])
            (.var .local (ofString "off")))
          (.return (.const 0))))).2 with locals := Lv}) :
    ∃ offF : BitVec 64,
      offF.toNat = hlBv.toNat + payv.toNat ∧
      R16Shards.WkBlockTxEnc.HeapByteEff st post
        ((globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
          (nodeCacheIvls Nd ++ keccakBufIvls st)) ["heap_ptr"] ∧
      globN st "heap_ptr" < globN post "heap_ptr" ∧
      NodeHeap post Nd ∧
      nodeExtents post Nd = nodeExtents st Nd ∧
      KeccakBufsSafe post Nd ∧
      memW post (nodew.toNat + 8) = globN st "heap_ptr" ∧
      memW post (nodew.toNat + 16) = offF.toNat ∧
      (∀ n ∈ Nd, n ≠ nodew.toNat → memW post (n + 8) = memW st (n + 8) ∧
        memW post (n + 16) = memW st (n + 16)) ∧
      (∀ n ∈ Nd, memW post n = memW st n ∧
        (1 ≤ memW st n → memW post (n + 40) = memW st (n + 40)) ∧
        (memW st n = 1 → memW post (n + 48) = memW st (n + 48) ∧
          memW post (n + 56) = memW st (n + 56))) := by
  obtain ⟨offF, hM_loff, hoffF_nat⟩ := hoffF
  obtain ⟨hk_le3, halloc_nd, hin_nd, hw_nd, _, _, _, _, _, _⟩ := hN.1 nodew.toNat hnode_in
  have hns32 := nodeSize_ge32 (memW st nodew.toNat)
  have hlim_he : heapLimit ≤ heapEnd := by
    rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhp_lim : globN st "heap_ptr" ≤ heapLimit := hAR.2.2.1
  have hQpos : 0 < hlBv.toNat + payv.toNat := by omega
  have hnode_hi : nodew.toNat + nodeSize (memW st nodew.toNat) ≤ heapLimit := by
    have h2 := hin_nd.2
    simp only [Inside, nodeIvl] at h2
    omega
  have hkeq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion sM gs = bufferRegion st gs := by
    intro gs hgs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl
    · unfold bufferRegion globN
      rw [← heffB.globals (ofString "keccak_pad") (by decide)]
    · unfold bufferRegion globN
      rw [← heffB.globals (ofString "keccak_st") (by decide)]
  have hnv64 : nodew.toNat < 2 ^ 64 := nodew.isLt
  -- no node record overlaps the two stored words
  have haway : ∀ n ∈ Nd, ∀ off : Nat, off ≠ 8 → off ≠ 16 → off < nodeSize (memW st n) →
      n + off ≠ nodew.toNat + 8 ∧ n + off ≠ nodew.toNat + 16 := by
    intro n hn off hoff8 hoff16 hoff_sz
    by_cases hne : n = nodew.toNat
    · subst hne; omega
    · have hdisj := hN.2 n hn nodew.toNat hnode_in hne
      have h1 := nodeSize_ge32 (memW st n)
      have h2 := hns32
      dsimp [nodeIvl] at hdisj
      rcases hdisj with h0 | h0 | h0 | h0 <;> omega
  -- concrete evals of the store operands
  have hdst1 : @evalHOLExact 64 F _ sM.toExact
      (fun a => Classical.propDecidable (sM.memaddrs a))
      (.op .add [.var .local (ofString "node"), .const 8]) =
      some (.val (.word (nodew + BitVec.ofNat 64 8))) := by
    simp [evalHOLExact, evalListHOLExact, hM_ln, wordOpHOL, wordOp, valueIsWord, valueWord,
      BitVec.add_zero]
  have hval1 : @evalHOLExact 64 F _ sM.toExact
      (fun a => Classical.propDecidable (sM.memaddrs a))
      (.var .local (ofString "buf")) = some (.val (.word bufw)) := by
    simp [evalHOLExact, hM_lb]
  -- WordsOK for the 24-byte node header prefix at sM
  have hW_M_nd : WordsOK sM (nodew.toNat, nodeSize (memW st nodew.toNat)) :=
    P3MptSet.wordsOK_transfer hAR.1 heffB.arena.1 hw_nd
  have hW1 : WordsOK sM (nodew.toNat, 24) := by
    refine ⟨hW_M_nd.1, show 24 % 8 = 0 by decide, ?_⟩
    intro k hk
    refine hW_M_nd.2.2 k ?_
    have := hns32
    omega
  have hhi1 : nodew.toNat + 24 ≤ heapEnd := by omega
  have hin1 : ∃ i ∈ ((globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
      (nodeCacheIvls Nd ++ keccakBufIvls st)),
      i.1 ≤ nodew.toNat + 8 ∧ nodew.toNat + 8 + 8 ≤ i.1 + i.2 :=
    ⟨(nodew.toNat + 8, 24), by
      simp only [List.mem_cons, nodeCacheIvls, List.mem_append, List.mem_map]
      exact Or.inr (Or.inl ⟨nodew.toNat, hnode_in, rfl⟩), by omega, by omega⟩
  have hin2 : ∃ i ∈ ((globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
      (nodeCacheIvls Nd ++ keccakBufIvls st)),
      i.1 ≤ nodew.toNat + 16 ∧ nodew.toNat + 16 + 8 ≤ i.1 + i.2 :=
    ⟨(nodew.toNat + 8, 24), by
      simp only [List.mem_cons, nodeCacheIvls, List.mem_append, List.mem_map]
      exact Or.inr (Or.inl ⟨nodew.toNat, hnode_in, rfl⟩), by omega, by omega⟩
  -- thread the tail evaluation through both stores and the return
  rw [evaluateHOLFiniteState_seq_line780] at hret2 hpost
  have hst1 := eval_store_memW_at (s := sM) (base := nodew) (w := bufw) (off := 8) (len := 24)
    (Rl := (globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
      (nodeCacheIvls Nd ++ keccakBufIvls st)) (gw := ["heap_ptr"])
    heffB.arena hW1 (by decide) (by decide) hhi1 hin1 hdst1 hval1
  dsimp only at hst1
  obtain ⟨hst1_n, hst1_l, hst1_g, hst1_w8, hst1_mem, hst1_eff⟩ := hst1
  rcases hev1 : evaluateHOLFiniteState sM
    (.store (.op .add [.var .local (ofString "node"), .const 8])
      (.var .local (ofString "buf"))) with ⟨o1, sS1⟩
  rw [hev1] at hret2 hpost hst1_n hst1_l hst1_g hst1_w8 hst1_mem hst1_eff
  dsimp only at hret2 hpost hst1_n hst1_l hst1_g hst1_w8 hst1_mem hst1_eff
  subst hst1_n
  simp only at hret2 hpost
  rw [evaluateHOLFiniteState_seq_line780] at hret2 hpost
  have hAR_S1 : ArenaReady sS1 := hst1_eff.arena
  have hW2 : WordsOK sS1 (nodew.toNat, 24) :=
    P3MptSet.wordsOK_transfer heffB.arena.1 hAR_S1.1 hW1
  have hS1_ln : sS1.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
    rw [hst1_l]; exact hM_ln
  have hS1_loff : sS1.locals.lookup (ofString "off") = some (.val (.word offF)) := by
    rw [hst1_l]; exact hM_loff
  have hdst2' : @evalHOLExact 64 F _ sS1.toExact
      (fun a => Classical.propDecidable (sS1.memaddrs a))
      (.op .add [.var .local (ofString "node"), .const 16]) =
      some (.val (.word (nodew + BitVec.ofNat 64 16))) := by
    simp [evalHOLExact, evalListHOLExact, hS1_ln, wordOpHOL, wordOp, valueIsWord, valueWord,
      BitVec.add_zero]
  have hval2' : @evalHOLExact 64 F _ sS1.toExact
      (fun a => Classical.propDecidable (sS1.memaddrs a))
      (.var .local (ofString "off")) = some (.val (.word offF)) := by
    simp [evalHOLExact, hS1_loff]
  have hst2 := eval_store_memW_at (s := sS1) (base := nodew) (w := offF) (off := 16)
    (len := 24) (Rl := (globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
      (nodeCacheIvls Nd ++ keccakBufIvls st)) (gw := ["heap_ptr"])
    hAR_S1 hW2 (by decide) (by decide) hhi1 hin2 hdst2' hval2'
  dsimp only at hst2
  obtain ⟨hst2_n, hst2_l, hst2_g, hst2_w16, hst2_mem, hst2_eff⟩ := hst2
  rcases hev2 : evaluateHOLFiniteState sS1
    (.store (.op .add [.var .local (ofString "node"), .const 16])
      (.var .local (ofString "off"))) with ⟨o2, sS2⟩
  rw [hev2] at hret2 hpost hst2_n hst2_l hst2_g hst2_w16 hst2_mem hst2_eff
  dsimp only at hret2 hpost hst2_n hst2_l hst2_g hst2_w16 hst2_mem hst2_eff
  subst hst2_n
  simp only at hret2 hpost
  rw [evaluateHOLFiniteState_return] at hret2 hpost
  have hret0 : @evalHOLExact 64 F _ sS2.toExact
      (fun a => Classical.propDecidable (sS2.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  rw [hret0] at hret2 hpost
  dsimp only at hret2 hpost
  have hsz0 : sizeOfShapeWithContextHOL sS2.structs
      (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [if_pos hsz0] at hret2 hpost
  dsimp only at hret2 hpost
  have hlim264 : heapLimit < 2 ^ 64 := by decide
  have hkeep3 : ∀ X : Nat, X < 2 ^ 64 → X ≠ nodew.toNat + 8 → X ≠ nodew.toNat + 16 →
      memW post X = memW sM X := by
    intro X hX h8 h16
    rw [hpost]
    change memW sS2 X = memW sM X
    exact memW_eq_of_cell_eq ((hst2_mem X hX h16).trans (hst1_mem X hX h8))
  have heff_stores : R16Shards.WkBlockTxEnc.HeapByteEff sM sS2
      ((globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
        (nodeCacheIvls Nd ++ keccakBufIvls st)) ["heap_ptr"] :=
    hst1_eff.trans hst2_eff
  have heff_mono : R16Shards.WkBlockTxEnc.HeapByteEff st sM
      ((globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
        (nodeCacheIvls Nd ++ keccakBufIvls st)) ["heap_ptr"] := by
    refine heffB.mono (fun i hi _ => ?_) (fun _ hg => hg)
    rcases List.mem_append.1 hi with hm24 | hrest
    · obtain ⟨n, hnN, rfl⟩ := List.mem_map.1 hm24
      refine Or.inl ⟨(n + 8, 24), ?_, by dsimp; omega, by dsimp; omega⟩
      exact List.Mem.tail _ (List.mem_append_left _ (List.mem_map.2 ⟨n, hnN, rfl⟩))
    · rcases List.mem_append.1 hrest with hbuf_mem | hkc_mem
      · simp only [List.mem_singleton] at hbuf_mem
        subst hbuf_mem
        exact Or.inl ⟨(globN st "heap_ptr", hlBv.toNat + payv.toNat), List.Mem.head _,
          le_rfl, le_rfl⟩
      · simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hkc_mem
        rcases hkc_mem with rfl | rfl
        · rw [hkeq ("keccak_pad", 136) (by decide)]
          exact Or.inl ⟨bufferRegion st ("keccak_pad", 136),
            List.Mem.tail _ (List.mem_append_right _ (List.Mem.head _)), le_rfl, le_rfl⟩
        · rw [hkeq ("keccak_st", 200) (by decide)]
          exact Or.inl ⟨bufferRegion st ("keccak_st", 200),
            List.Mem.tail _ (List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _))),
            le_rfl, le_rfl⟩
  have heff_final : R16Shards.WkBlockTxEnc.HeapByteEff st post
      ((globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
        (nodeCacheIvls Nd ++ keccakBufIvls st)) ["heap_ptr"] := by
    rw [hpost]
    exact (heff_mono.trans heff_stores).locals_clock Lv _
  have heff_cache_post : R16Shards.WkBlockTxEnc.HeapByteEff st post
      (nodeCacheIvls Nd ++
        ((globN st "heap_ptr", hlBv.toNat + payv.toNat) :: keccakBufIvls st)) ["heap_ptr"] := by
    refine heff_final.mono (fun i hi _ => ?_) (fun _ hg => hg)
    rcases List.mem_cons.1 hi with rfl | hrest
    · exact Or.inl ⟨(globN st "heap_ptr", hlBv.toNat + payv.toNat),
        List.mem_append_right _ (List.Mem.head _), le_rfl, le_rfl⟩
    · rcases List.mem_append.1 hrest with hc | hkc
      · exact Or.inl ⟨i, List.mem_append_left _ hc, le_rfl, le_rfl⟩
      · exact Or.inl ⟨i, List.mem_append_right _ (List.Mem.tail _ hkc), le_rfl, le_rfl⟩
  have h8_post : memW post (nodew.toNat + 8) = globN st "heap_ptr" := by
    have h8keep : memW sS2 (nodew.toNat + 8) = memW sS1 (nodew.toNat + 8) :=
      memW_eq_of_cell_eq (hst2_mem _ (by omega) (by omega))
    rw [hpost]; change memW sS2 (nodew.toNat + 8) = globN st "heap_ptr"
    rw [h8keep, hst1_w8, hbufw0]
  have h16_post : memW post (nodew.toNat + 16) = offF.toNat := by
    rw [hpost]; exact hst2_w16
  have hother_cache : ∀ n ∈ Nd, n ≠ nodew.toNat → memW post (n + 8) = memW st (n + 8) ∧
      memW post (n + 16) = memW st (n + 16) := by
    intro n hn hne_nd
    have hin' := (hN.1 n hn).2.2.1.2
    dsimp [nodeIvl] at hin'
    have hnsn := nodeSize_ge32 (memW st n)
    have hdisj_n := hN.2 n hn nodew.toNat hnode_in hne_nd
    dsimp [nodeIvl] at hdisj_n
    have h8_ne : n + 8 ≠ nodew.toNat + 8 ∧ n + 8 ≠ nodew.toNat + 16 := by
      rcases hdisj_n with h0 | h0 | h0 | h0 <;> omega
    have h16_ne : n + 16 ≠ nodew.toNat + 8 ∧ n + 16 ≠ nodew.toNat + 16 := by
      rcases hdisj_n with h0 | h0 | h0 | h0 <;> omega
    refine ⟨?_, ?_⟩
    · rw [hkeep3 (n + 8) (by omega) h8_ne.1 h8_ne.2,
        hW_M n hn 8 (by decide) (by omega) (by decide)]
    · rw [hkeep3 (n + 16) (by omega) h16_ne.1 h16_ne.2,
        hW_M n hn 16 (by decide) (by omega) (by decide)]
  obtain ⟨hN_post, hext_post⟩ :
      NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents st Nd := by
    refine nodeHeap_of_heapByteEff_cache hAR hN heff_cache_post ?_ ?_
    · intro e he o ho
      rcases List.mem_cons.1 he with rfl | hkc
      · exact hbuf_disj o ho
      · exact keccakBufIvls_disj_of_safe hKS e hkc o ho
    · intro n hn
      by_cases hne_nd : n = nodew.toNat
      · subst hne_nd
        rw [h16_post, hoffF_nat]
        exact htot40
      · rw [(hother_cache n hn hne_nd).2]
        exact (hN.1 n hn).2.2.2.2.2.2.2.1
  have hword_nd : ∀ n ∈ Nd, memW post n = memW st n ∧
      (1 ≤ memW st n → memW post (n + 40) = memW st (n + 40)) ∧
      (memW st n = 1 → memW post (n + 48) = memW st (n + 48) ∧
        memW post (n + 56) = memW st (n + 56)) := by
    intro n hn
    have hin' := (hN.1 n hn).2.2.1.2
    dsimp [nodeIvl] at hin'
    have hnsn := nodeSize_ge32 (memW st n)
    refine ⟨?_, ?_, ?_⟩
    · have haw0 := haway n hn 0 (by decide) (by decide) (by omega)
      have h1 := hW_M n hn 0 (by decide) (by omega) (by decide)
      simpa using (hkeep3 (n + 0) (by omega) haw0.1 haw0.2).trans h1
    · intro h1k
      have hns40 : 48 ≤ nodeSize (memW st n) := by
        unfold nodeSize
        split_ifs <;> omega
      have haw40 := haway n hn 40 (by decide) (by decide) (by omega)
      have h1 := hW_M n hn 40 (by decide) hns40 (by decide)
      exact (hkeep3 (n + 40) (by omega) haw40.1 haw40.2).trans h1
    · intro h1k
      have hns48 : 56 ≤ nodeSize (memW st n) := by rw [h1k]; decide
      have hns56 : 64 ≤ nodeSize (memW st n) := by rw [h1k]; decide
      have haw48 := haway n hn 48 (by decide) (by decide) (by omega)
      have haw56 := haway n hn 56 (by decide) (by decide) (by omega)
      have h1' := hW_M n hn 48 (by decide) hns48 (by decide)
      have h2' := hW_M n hn 56 (by decide) hns56 (by decide)
      exact ⟨(hkeep3 (n + 48) (by omega) haw48.1 haw48.2).trans h1',
        (hkeep3 (n + 56) (by omega) haw56.1 haw56.2).trans h2'⟩
  refine ⟨offF, hoffF_nat, heff_final, ?_, hN_post, hext_post, ?_, h8_post, h16_post,
    hother_cache, hword_nd⟩
  · have h1 : globN st "heap_ptr" < globN sM "heap_ptr" := hM_hp
    have h2 : globN sM "heap_ptr" ≤ globN sS2 "heap_ptr" := heff_stores.hp_le
    have h3 : globN sS2 "heap_ptr" = globN post "heap_ptr" := by
      rw [hpost]; rfl
    omega
  · have hbuf_eq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
        bufferRegion post gs = bufferRegion st gs := by
      intro gs hgs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
      rcases hgs with rfl | rfl
      · unfold bufferRegion globN
        rw [← heff_final.globals (ofString "keccak_pad") (by decide)]
      · unfold bufferRegion globN
        rw [← heff_final.globals (ofString "keccak_st") (by decide)]
    exact keccakBufsSafe_of_grows hKS ⟨heff_final.hp_le, heff_final.sp_le⟩ hbuf_eq
      hext_post

/-! ### R15 cycle 3: the `_node_rlp_finish` write-phase dispatch

`finWrite`'s first half (`finPhaseA` for kinds 1/2, `finPhaseB` for kind 3) appends the payload
bytes after the 9-byte list header and returns the final `off`. This section proves the
dispatch `finWrite` in full (both phases plus the two final stores and the `return 0`), under
the frame hypotheses available at that point of `_node_rlp_finish`. -/

private theorem rlpBytesLenPure_if_zero_lt {fb n : Nat} :
    rlpBytesLenPure (if 0 < n then fb else 0) n = rlpBytesLenPure fb n := by
  by_cases h0 : n = 0
  · subst h0
    simp [rlpBytesLenPure, rlpHeaderLenPure]
  · have hlt : 0 < n := Nat.pos_of_ne_zero h0
    simp [rlpBytesLenPure, rlpHeaderLenPure, hlt]

private theorem eval_finWrite_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (nodew frw kw pw cbufw clenw hlw bufw offw : BitVec 64) (bufLen : Nat)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (hN : NodeHeap s Nd) (hKS : KeccakBufsSafe s Nd)
    (hnode_in : nodew.toNat ∈ Nd)
    (hk123 : 1 ≤ memW s nodew.toNat ∧ memW s nodew.toNat ≤ 3)
    (hkw_nat : kw.toNat = memW s nodew.toNat)
    (hln : s.locals.lookup (ofString "node") = some (.val (.word nodew)))
    (hlf : s.locals.lookup (ofString "fr") = some (.val (.word frw)))
    (hlk : s.locals.lookup (ofString "k") = some (.val (.word kw)))
    (hlp : s.locals.lookup (ofString "payload") = some (.val (.word pw)))
    (hlcb : s.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)))
    (hlcl : s.locals.lookup (ofString "clen") = some (.val (.word clenw)))
    (hlb : s.locals.lookup (ofString "buf") = some (.val (.word bufw)))
    (hlo : s.locals.lookup (ofString "off") = some (.val (.word offw)))
    (hhl : s.locals.lookup (ofString "hl") = some (.val (.word hlw)))
    (hbuf_lim : bufw.toNat + bufLen ≤ heapLimit)
    (hbuf_disj : ∀ o ∈ nodeExtents s Nd, Disj (bufw.toNat, bufLen) o)
    (hfit1 : memW s nodew.toNat = 1 →
      offw.toNat + rlpBytesLenPure (memB s cbufw.toNat) clenw.toNat +
        rlpBytesLenPure (if 0 < memW s (nodew.toNat + 56) then memB s (memW s (nodew.toNat + 48)) else 0)
          (memW s (nodew.toNat + 56)) ≤ bufLen)
    (hfit2 : memW s nodew.toNat = 2 →
      offw.toNat + rlpBytesLenPure (memB s cbufw.toNat) clenw.toNat +
        nodeRefBytes s (memW s (nodew.toNat + 48)) ≤ bufLen)
    (hfit3 : memW s nodew.toNat = 3 →
      offw.toNat + branchRefsLenSum s nodew.toNat 16 +
        rlpBytesLenPure (if 0 < memW s (nodew.toNat + 168) then memB s (memW s (nodew.toNat + 160)) else 0)
          (memW s (nodew.toNat + 168)) ≤ bufLen)
    (hclen60 : (memW s nodew.toNat = 1 ∨ memW s nodew.toNat = 2) → clenw.toNat < 2 ^ 60)
    (hval1_no : memW s nodew.toNat = 1 → memW s (nodew.toNat + 56) = 1 →
      ¬ InIvl (memW s (nodew.toNat + 48)) (bufw.toNat, bufLen) ∧
      (∀ iv ∈ keccakBufIvls s, ¬ InIvl (memW s (nodew.toNat + 48)) iv) ∧
      ¬ InIvl (memW s (nodew.toNat + 48)) (freeGap s) ∧
      ¬ InIvl (memW s (nodew.toNat + 48)) (heapFree s))
    (hval3_no : memW s nodew.toNat = 3 → memW s (nodew.toNat + 168) = 1 →
      ¬ InIvl (memW s (nodew.toNat + 160)) (bufw.toNat, bufLen) ∧
      (∀ n ∈ Nd, ¬ InIvl (memW s (nodew.toNat + 160)) (n + 24, 8)) ∧
      (∀ iv ∈ keccakBufIvls s, ¬ InIvl (memW s (nodew.toNat + 160)) iv) ∧
      ¬ InIvl (memW s (nodew.toNat + 160)) (freeGap s) ∧
      ¬ InIvl (memW s (nodew.toNat + 160)) (heapFree s))
    (hnone : (evaluateHOLFiniteState s finDispatch).1 = none) :
    let post := (evaluateHOLFiniteState s finDispatch).2
    ∃ offF : BitVec 64,
      offF.toNat = offw.toNat +
        (if memW s nodew.toNat = 1 then
          rlpBytesLenPure (memB s cbufw.toNat) clenw.toNat +
            rlpBytesLenPure (if 0 < memW s (nodew.toNat + 56) then memB s (memW s (nodew.toNat + 48)) else 0)
              (memW s (nodew.toNat + 56))
        else if memW s nodew.toNat = 2 then
          rlpBytesLenPure (memB s cbufw.toNat) clenw.toNat + nodeRefBytes s (memW s (nodew.toNat + 48))
        else branchRefsLenSum s nodew.toNat 16 +
          rlpBytesLenPure (if 0 < memW s (nodew.toNat + 168) then memB s (memW s (nodew.toNat + 160)) else 0)
            (memW s (nodew.toNat + 168))) ∧
      offF.toNat < 2 ^ 40 ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s post
        (Nd.map (fun n => (n + 24, 8)) ++ [(bufw.toNat, bufLen)] ++ keccakBufIvls s) ["heap_ptr"] ∧
      globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd ∧ KeccakBufsSafe post Nd ∧
      (∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) → off ≠ 24 →
        memW post (n + off) = memW s (n + off)) ∧
      post.locals.lookup (ofString "node") = some (.val (.word nodew)) ∧
      post.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
      post.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
      post.locals.lookup (ofString "payload") = some (.val (.word pw)) ∧
      post.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) ∧
      post.locals.lookup (ofString "clen") = some (.val (.word clenw)) ∧
      post.locals.lookup (ofString "buf") = some (.val (.word bufw)) ∧
      post.locals.lookup (ofString "off") = some (.val (.word offF)) ∧
      post.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
  intro post
  dsimp only [post]
  rw [finDispatch] at hnone
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hlim_he : heapLimit ≤ heapEnd := by
    rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hbuf_lt : bufLen < 2 ^ 64 := by omega
  obtain ⟨hk_le3, hal_n, hin_n, hw_n, hroot_ext, hroot_br, hkey_n, hlt16, hval40, hv168⟩ :=
    hN.1 nodew.toNat hnode_in
  have hnode_hi : nodew.toNat + nodeSize (memW s nodew.toNat) ≤ heapLimit := by
    have h2 := hin_n.2
    simp only [Inside, nodeIvl] at h2
    omega
  -- condition of the dispatch
  have hcnd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.var .local (ofString "k")) (.const 3)) =
      some (.val (.word (if kw = (3 : BitVec 64) then (0 : BitVec 64) else (1 : BitVec 64)))) := by
    simp [evalHOLExact, hlk, Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluateHOLFiniteState_ite, hcnd] at hnone
  dsimp only at hnone
  have hsel : (if ((if kw = (3 : BitVec 64) then (0 : BitVec 64) else (1 : BitVec 64)) : BitVec 64) = 0
      then s.evaluateHOLFiniteState finPhaseB else s.evaluateHOLFiniteState finPhaseA)
      = (if kw = (3 : BitVec 64) then s.evaluateHOLFiniteState finPhaseB
        else s.evaluateHOLFiniteState finPhaseA) := by
    by_cases h3 : kw = (3 : BitVec 64) <;> simp [h3]
  rw [hsel] at hnone
  split at hnone
  · -- kind 3: the branch-length loop plus the value tail
    rename_i hkw3
    have hkmem3 : memW s nodew.toNat = 3 := by
      have h3 : kw.toNat = 3 := by rw [hkw3]; decide
      omega
    rw [finPhaseB] at hnone
    have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.const 0) = some (.val (.word (0 : BitVec 64))) := rfl
    have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    let sj0 := setVarHOLFinite (ofString "j") (.val (.word (0 : BitVec 64))) s
    let tailB : ProgHOL 64 :=
      .decCall (ofString "w5") .one (ofString "rlp_encode_bytes")
        [.op .add [.var .local (ofString "buf"), .var .local (ofString "off")],
         .load .one (.op .add [.var .local (ofString "node"), .const 160]),
         .load .one (.op .add [.var .local (ofString "node"), .const 168])]
        (.assign .local (ofString "off")
          (.op .add [.var .local (ofString "off"), .var .local (ofString "w5")]))
    have hdec0 : evaluateHOLFiniteState s
        (.dec (ofString "j") .one (.const 0) (.seq finishWriteLoop tailB)) =
        ((evaluateHOLFiniteState sj0 (.seq finishWriteLoop tailB)).1,
         { (evaluateHOLFiniteState sj0 (.seq finishWriteLoop tailB)).2 with
           locals := HolFiniteMapExact.resVarEq
             (evaluateHOLFiniteState sj0 (.seq finishWriteLoop tailB)).2.locals
             (ofString "j", s.locals.lookup (ofString "j")) }) := by
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rw [hev0]; dsimp only; rw [if_pos hsh0]
    have hnone_j0 : (evaluateHOLFiniteState sj0 (.seq finishWriteLoop tailB)).1 = none := by
      rw [hdec0] at hnone; exact hnone
    obtain ⟨hn_loop, hn_tail, hseq_loop⟩ := seq_none_rel sj0 finishWriteLoop tailB hnone_j0
    have hsj0_AR : ArenaReady sj0 := ⟨guestInv_setVar _ _ _ hAR.1, hAR.2⟩
    have heff_j0 : R16Shards.WkBlockTxEnc.HeapByteEff s sj0 [] ["heap_ptr"] :=
      (R16Shards.WkBlockTxEnc.HeapByteEff.refl hAR [] ["heap_ptr"]).locals_clock _ _
    have hsj0_N : NodeHeap sj0 Nd :=
      (nodeHeap_of_heapByteEff_disj hAR hN heff_j0 (by simp)).1
    have hsj0_ext : nodeExtents sj0 Nd = nodeExtents s Nd := rfl
    have hsj0_KS : KeccakBufsSafe sj0 Nd := hKS
    have hsj0_k3 : memW sj0 nodew.toNat = 3 := hkmem3
    have hsj0_br : branchRefsLenSum sj0 nodew.toNat 16 = branchRefsLenSum s nodew.toNat 16 := rfl
    have hfit3_s := hfit3 hkmem3
    have hsj0_ln : sj0.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hln,
        show ofString "j" ≠ ofString "node" by decide]
    have hsj0_lf : sj0.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlf,
        show ofString "j" ≠ ofString "fr" by decide]
    have hsj0_lk : sj0.locals.lookup (ofString "k") = some (.val (.word kw)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk,
        show ofString "j" ≠ ofString "k" by decide]
    have hsj0_lp : sj0.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlp,
        show ofString "j" ≠ ofString "payload" by decide]
    have hsj0_lcb : sj0.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlcb,
        show ofString "j" ≠ ofString "cbuf" by decide]
    have hsj0_lcl : sj0.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlcl,
        show ofString "j" ≠ ofString "clen" by decide]
    have hsj0_lhl : sj0.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hhl,
        show ofString "j" ≠ ofString "hl" by decide]
    have hsj0_lb : sj0.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlb,
        show ofString "j" ≠ ofString "buf" by decide]
    have hsj0_lo : sj0.locals.lookup (ofString "off") = some (.val (.word offw)) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlo,
        show ofString "j" ≠ ofString "off" by decide]
    have hsj0_lj : sj0.locals.lookup (ofString "j") = some (.val (.word (0 : BitVec 64))) := by
      simp [sj0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    obtain ⟨offL, hoffL_nat, heff_L0, hNL, hextL, hKSL, hmemW_L0,
        hL_ln, hL_lf, hL_lk, hL_lp, hL_lcb, hL_lcl, hL_lhl, hL_lb, hL_lo⟩ :=
      eval_finishWriteLoop_none sj0.clock sj0 Nd nodew frw kw pw cbufw clenw hlw bufw offw 0 bufLen
        (le_refl _) hc hsj0_AR hsj0_N hsj0_KS hnode_in hsj0_k3 (by decide) hbuf_lim
        (by change offw.toNat + branchRefsLenSum sj0 nodew.toNat 16 ≤ bufLen; rw [hsj0_br]; omega)
        (by rw [hsj0_ext]; exact hbuf_disj)
        hsj0_ln hsj0_lf hsj0_lk hsj0_lp hsj0_lcb hsj0_lcl hsj0_lhl hsj0_lb hsj0_lo hsj0_lj hn_loop
    set sL := (evaluateHOLFiniteState sj0 finishWriteLoop).2 with hsL_eq
    have hoffL_s : offL.toNat = offw.toNat + branchRefsLenSum s nodew.toNat 16 := by
      change offL.toNat = offw.toNat + branchRefsLenSum sj0 nodew.toNat 16 at hoffL_nat
      rw [hsj0_br] at hoffL_nat
      exact hoffL_nat
    have heff_sL : R16Shards.WkBlockTxEnc.HeapByteEff s sL
        ([(bufw.toNat, bufLen)] ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s))
        ["heap_ptr"] := by
      have h0 : R16Shards.WkBlockTxEnc.HeapByteEff s sj0
          ([(bufw.toNat, bufLen)] ++ (Nd.map (fun n => (n + 24, 8)) ++ keccakBufIvls s))
          ["heap_ptr"] :=
        heff_j0.mono (fun i hi => by simp at hi) (by simp)
      exact h0.trans heff_L0
    have hAR_L : ArenaReady sL := heff_sL.arena
    have hc_L : sL.code = originalRuntimeCode := hAR_L.1.code
    have hnsz176 : nodeSize (memW s nodew.toNat) = 176 := by rw [hkmem3]; rfl
    have hmemW_L : ∀ n ∈ Nd, ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) → off ≠ 24 →
        memW sL (n + off) = memW s (n + off) := hmemW_L0
    have hkL3 : memW sL nodew.toNat = 3 := by
      have h0 := hmemW_L nodew.toNat hnode_in 0 (by decide) (by rw [hnsz176]; decide) (by decide)
      simpa [hkmem3] using h0
    have hwL : WordsOK sL (nodew.toNat, nodeSize (memW s nodew.toNat)) := by
      have hwL0 := (hNL.1 nodew.toNat hnode_in).2.2.2.1
      dsimp [nodeIvl] at hwL0
      rw [hkL3, ← hkmem3] at hwL0
      exact hwL0
    have haddr160 : @evalHOLExact 64 F _ sL.toExact (fun a => Classical.propDecidable (sL.memaddrs a))
        (.op .add [.var .local (ofString "node"), .const 160]) =
        some (.val (.word (nodew + BitVec.ofNat 64 160))) := by
      simp [evalHOLExact, evalListHOLExact, hL_ln, wordOpHOL, wordOp, valueIsWord, valueWord]
    obtain ⟨v160, hld160, hv160n⟩ := eval_load_memW_of_wordsOK (s := sL) (base := nodew)
      (off := 160) (len := nodeSize (memW s nodew.toNat)) hwL (by decide)
      (by rw [hnsz176]; decide) (by omega) haddr160
    have hv160s : v160.toNat = memW s (nodew.toNat + 160) := by
      rw [hv160n, hmemW_L nodew.toNat hnode_in 160 (by decide) (by rw [hnsz176]; decide) (by decide)]
    have haddr168 : @evalHOLExact 64 F _ sL.toExact (fun a => Classical.propDecidable (sL.memaddrs a))
        (.op .add [.var .local (ofString "node"), .const 168]) =
        some (.val (.word (nodew + BitVec.ofNat 64 168))) := by
      simp [evalHOLExact, evalListHOLExact, hL_ln, wordOpHOL, wordOp, valueIsWord, valueWord]
    obtain ⟨v168, hld168, hv168n⟩ := eval_load_memW_of_wordsOK (s := sL) (base := nodew)
      (off := 168) (len := nodeSize (memW s nodew.toNat)) hwL (by decide)
      (by rw [hnsz176]) (by omega) haddr168
    have hv168s : v168.toNat = memW s (nodew.toNat + 168) := by
      rw [hv168n, hmemW_L nodew.toNat hnode_in 168 (by decide) (by rw [hnsz176]) (by decide)]
    have hn60_3 : v168.toNat < 2 ^ 60 := by
      rw [hv168s]
      have := hv168 hkmem3
      omega
    have hdstE5 : @evalHOLExact 64 F _ sL.toExact (fun a => Classical.propDecidable (sL.memaddrs a))
        (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")]) =
        some (.val (.word (bufw + offL))) := by
      simp [evalHOLExact, evalListHOLExact, hL_lb, hL_lo, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hdst5 : (bufw + offL).toNat = bufw.toNat + offL.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hlen5L : rlpBytesLenPure (if 0 < v168.toNat then memB sL v160.toNat else 0) v168.toNat =
        rlpBytesLenPure
          (if 0 < memW s (nodew.toNat + 168) then memB s (memW s (nodew.toNat + 160)) else 0)
          (memW s (nodew.toNat + 168)) := by
      rw [hv160s, hv168s]
      by_cases hv1 : memW s (nodew.toNat + 168) = 1
      · obtain ⟨hno_buf, hno_nd24, hno_kec, hno_fg, hno_hf⟩ := hval3_no hkmem3 hv1
        have hlt_v160 : memW s (nodew.toNat + 160) < 2 ^ 64 :=
          memW_lt_two_pow_64 s (nodew.toNat + 160)
        have hmemB_v160 : memB sL (memW s (nodew.toNat + 160)) = memB s (memW s (nodew.toNat + 160)) := by
          by_contra hne
          rcases heff_sL.byte_frame (memW s (nodew.toNat + 160)) hlt_v160 hne with
            ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
          · rcases List.mem_append.1 hiv with hiv | hiv
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv; subst hiv
              exact hno_buf ⟨hb1, hb2⟩
            · rcases List.mem_append.1 hiv with hiv | hiv
              · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hiv
                exact hno_nd24 m hm ⟨hb1, hb2⟩
              · exact hno_kec iv hiv ⟨hb1, hb2⟩
          · exact hno_fg ⟨hfg1, hfg2⟩
          · exact hno_hf ⟨hhf1, hhf2⟩
        rw [hmemB_v160]
      · exact rlpBytesLenPure_congr_ne_one hv1
    obtain ⟨w5v, sB5, hw5, hdst_lt5, hsB5_gl, hsB5_lc, heff_w5, hcont_nt5, hdc5⟩ :=
      eval_decCall_rlp_encode_bytes_len_exact sL "w5"
        (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")])
        (.load .one (.op .add [.var .local (ofString "node"), .const 160]))
        (.load .one (.op .add [.var .local (ofString "node"), .const 168]))
        (bufw + offL) v160 v168
        (.assign .local (ofString "off")
          (.op .add [.var .local (ofString "off"), .var .local (ofString "w5")]))
        ([(bufw.toNat, bufLen)] ++ keccakBufIvls sL) ["heap_ptr"] hc_L hAR_L
        hdstE5 hld160 hld168 hn60_3
        ⟨(bufw.toNat, bufLen), by simp,
          by simp only [hdst5]; omega,
          by rw [hdst5, hlen5L, hoffL_s]; omega⟩
        (by rw [hn_tail]; decide) (Or.inr hn_tail)
    have hw5S : w5v.toNat =
        rlpBytesLenPure
          (if 0 < memW s (nodew.toNat + 168) then memB s (memW s (nodew.toNat + 160)) else 0)
          (memW s (nodew.toNat + 168)) := by
      rw [hw5, hlen5L]
    have hB5_off : sB5.locals.lookup (ofString "off") = some (.val (.word offL)) := by
      rw [hsB5_lc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hL_lo,
        show (ofString "w5") ≠ (ofString "off") by decide]
    have hB5_w5 : sB5.locals.lookup (ofString "w5") = some (.val (.word w5v)) := by
      rw [hsB5_lc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have heoffB5 : @evalHOLExact 64 F _ sB5.toExact
        (fun a => Classical.propDecidable (sB5.memaddrs a))
        (.op .add [.var .local (ofString "off"), .var .local (ofString "w5")]) =
        some (.val (.word (offL + w5v))) := by
      simp [evalHOLExact, evalListHOLExact, hB5_off, hB5_w5, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hval_off5 : isValidValueHOLFinite sB5 .local (ofString "off")
        (.val (.word (offL + w5v))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hB5_off, shapeOfHOLExact, shapeEqHOL]
    have hass5 : (evaluateHOLFiniteState sB5
        (.assign .local (ofString "off")
          (.op .add [.var .local (ofString "off"), .var .local (ofString "w5")]))) =
      (none, setVarHOLFinite (ofString "off") (.val (.word (offL + w5v))) sB5) := by
      rw [evaluateHOLFiniteState_assign, heoffB5]
      dsimp only
      rw [if_pos hval_off5]
      rfl
    let post3 :=
      { ({ setVarHOLFinite (ofString "off") (.val (.word (offL + w5v))) sB5 with
          locals := HolFiniteMapExact.resVarEq
            (setVarHOLFinite (ofString "off") (.val (.word (offL + w5v))) sB5).locals
            (ofString "w5", sL.locals.lookup (ofString "w5")) }) with
        locals := HolFiniteMapExact.resVarEq
          ({ setVarHOLFinite (ofString "off") (.val (.word (offL + w5v))) sB5 with
             locals := HolFiniteMapExact.resVarEq
               (setVarHOLFinite (ofString "off") (.val (.word (offL + w5v))) sB5).locals
               (ofString "w5", sL.locals.lookup (ofString "w5")) }).locals
          (ofString "j", s.locals.lookup (ofString "j")) }
    have hpost3 : (evaluateHOLFiniteState s finDispatch).2 = post3 := by
      rw [finDispatch, evaluateHOLFiniteState_ite, hcnd]
      dsimp only
      rw [hsel, if_pos hkw3, finPhaseB, hdec0]
      dsimp only
      rw [hseq_loop]
      change { (evaluateHOLFiniteState sL
          (.decCall (ofString "w5") .one (ofString "rlp_encode_bytes")
            [.op .add [.var .local (ofString "buf"), .var .local (ofString "off")],
             .load .one (.op .add [.var .local (ofString "node"), .const 160]),
             .load .one (.op .add [.var .local (ofString "node"), .const 168])]
            (.assign .local (ofString "off")
              (.op .add [.var .local (ofString "off"), .var .local (ofString "w5")])))).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState sL
            (.decCall (ofString "w5") .one (ofString "rlp_encode_bytes")
              [.op .add [.var .local (ofString "buf"), .var .local (ofString "off")],
               .load .one (.op .add [.var .local (ofString "node"), .const 160]),
               .load .one (.op .add [.var .local (ofString "node"), .const 168])]
              (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "w5")])))).2.locals
          (ofString "j", s.locals.lookup (ofString "j")) } = post3
      rw [hdc5]
      dsimp only
      rw [hass5]
    have hkp_sL : globN sL "keccak_pad" = globN s "keccak_pad" := by
      unfold globN
      rw [← heff_sL.globals (ofString "keccak_pad") (by decide)]
    have hks_sL : globN sL "keccak_st" = globN s "keccak_st" := by
      unfold globN
      rw [← heff_sL.globals (ofString "keccak_st") (by decide)]
    have hkec_sL : keccakBufIvls sL = keccakBufIvls s := by
      simp only [keccakBufIvls, bufferRegion, hkp_sL, hks_sL]
    have heff_sL_R : R16Shards.WkBlockTxEnc.HeapByteEff s sL
        (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
        ["heap_ptr"] := by
      refine heff_sL.mono (fun i hi _ => ?_) (fun _ hg => hg)
      rcases List.mem_append.1 hi with hbuf_i | hrest
      · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_left _ hbuf_i), le_rfl, le_rfl⟩
      · rcases List.mem_append.1 hrest with hnd24 | hkec_i
        · exact Or.inl ⟨i, List.mem_append_left _ hnd24, le_rfl, le_rfl⟩
        · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkec_i), le_rfl, le_rfl⟩
    have heff_w5_R : R16Shards.WkBlockTxEnc.HeapByteEff sL sB5
        (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
        ["heap_ptr"] := by
      refine heff_w5.mono (fun i hi _ => ?_) (fun _ hg => hg)
      rcases List.mem_append.1 hi with hbuf_i | hkec_i
      · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_left _ hbuf_i), le_rfl, le_rfl⟩
      · rw [hkec_sL] at hkec_i
        exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkec_i), le_rfl, le_rfl⟩
    have heff_goal3 : R16Shards.WkBlockTxEnc.HeapByteEff s post3
        (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
        ["heap_ptr"] :=
      ((heff_sL_R.trans heff_w5_R).locals_clock _ _).locals_clock _ _
    have heff_big3 : R16Shards.WkBlockTxEnc.HeapByteEff s post3
        (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
        ["heap_ptr", "keccak_pad", "keccak_st"] :=
      heff_goal3.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (by simp)
    have heff_cache3 : R16Shards.WkBlockTxEnc.HeapByteEff s post3
        (nodeCacheIvls Nd ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
        ["heap_ptr", "keccak_pad", "keccak_st"] := by
      refine heff_big3.mono (fun i hi _ => ?_) (fun _ hg => hg)
      rcases List.mem_append.1 hi with hm24 | hrest
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
        exact Or.inl ⟨(m + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩),
          by dsimp; omega, by dsimp; omega⟩
      · exact Or.inl ⟨i, List.mem_append_right _ hrest, le_rfl, le_rfl⟩
    have hextra_disj3 : ∀ e ∈ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s),
        ∀ o ∈ nodeExtents s Nd, Disj e o := by
      intro e he o ho
      rcases List.mem_append.1 he with he | he
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl
        exact hbuf_disj o ho
      · exact keccakBufIvls_disj_of_safe hKS e he o ho
    have hal_any3 : ∀ n ∈ Nd, ∀ off : Nat, off + 8 ≤ nodeSize (memW s n) →
        Allocated s (n + off, 8) := by
      intro n hn off hlt
      obtain ⟨_, hal_n', _, _, _, _, _, _, _, _⟩ := hN.1 n hn
      unfold Allocated Inside at hal_n' ⊢
      simp only [nodeIvl] at hal_n'
      dsimp only at hal_n' ⊢
      rcases hal_n' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    have hext_mem3 : ∀ n ∈ Nd, (n, nodeSize (memW s n)) ∈ nodeExtents s Nd := by
      intro n hn
      simp only [nodeExtents]
      exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
    have disj_sub3 : ∀ i i' j j' : Ivl, i.1 ≤ i'.1 → i'.1 + i'.2 ≤ i.1 + i.2 →
        j.1 ≤ j'.1 → j'.1 + j'.2 ≤ j.1 + j.2 → Disj i j → Disj i' j' := by
      intro i i' j j' hi1 hi2 hj1 hj2 h
      dsimp [Disj] at h ⊢
      rcases h with h0 | h0 | h1 | h2
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (by omega)))
    have hdisj_full3 : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 → off ≠ 24 →
        off + 8 ≤ nodeSize (memW s n) →
        ∀ iv ∈ (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s)),
          0 < iv.2 → Disj (n + off, 8) iv := by
      intro n hn off h8 h24 hlt iv hiv _
      have hsz := nodeSize_ge32 (memW s n)
      rcases List.mem_append.1 hiv with hiv | hiv
      · obtain ⟨n', hn', rfl⟩ := List.mem_map.1 hiv
        by_cases hnn : n' = n
        · subst hnn
          dsimp only [Disj]
          rcases Nat.lt_or_ge off 24 with h | h
          · exact Or.inr (Or.inr (Or.inl (by omega)))
          · exact Or.inr (Or.inr (Or.inr (by omega)))
        · have hsz' := nodeSize_ge32 (memW s n')
          exact disj_sub3 (n, nodeSize (memW s n)) (n + off, 8)
            (n', nodeSize (memW s n')) (n' + 24, 8) (by omega) (by omega) (by omega) (by omega)
            (hN.2 n hn n' hn' (Ne.symm hnn))
      · rcases List.mem_append.1 hiv with hiv | hiv
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
          rcases hiv with rfl
          exact disj_sub3 (n, nodeSize (memW s n)) (n + off, 8)
            (bufw.toNat, bufLen) (bufw.toNat, bufLen) (by omega) (by omega) (by omega) (by omega)
            (disj_comm (hbuf_disj _ (hext_mem3 n hn)))
        · exact disj_sub3 (n, nodeSize (memW s n)) (n + off, 8) iv iv
            (by omega) (by omega) (by omega) (by omega)
            (disj_comm (keccakBufIvls_disj_of_safe hKS iv hiv _ (hext_mem3 n hn)))
    have hrlp_post3 : ∀ n ∈ Nd, memW post3 (n + 16) < 2 ^ 40 := by
      intro n hn
      have h8n : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
      have hsz := nodeSize_ge32 (memW s n)
      have hlt64 : n + 16 < 2 ^ 64 := by
        have h2 := (hN.1 n hn).2.2.1.2
        simp only [Inside, nodeIvl] at h2
        omega
      have hmem16 : memW post3 (n + 16) = memW s (n + 16) :=
        memW_eq_of_heapByteEff_disj hAR heff_goal3 (by omega) (hal_any3 n hn 16 (by omega))
          hlt64 (hdisj_full3 n hn 16 (by omega) (by decide) (by omega))
      rw [hmem16]
      exact (hN.1 n hn).2.2.2.2.2.2.2.1
    obtain ⟨hNH_post3, hext_post3⟩ :=
      nodeHeap_of_heapByteEff_cache hAR hN heff_cache3 hextra_disj3 hrlp_post3
    have hag_post3 : AllocatorGrows s post3 := ⟨heff_big3.hp_le, heff_big3.sp_le⟩
    have hkp_eq3 : globN post3 "keccak_pad" = globN s "keccak_pad" := by
      unfold globN
      rw [← heff_goal3.globals (ofString "keccak_pad") (by decide)]
    have hks_eq3 : globN post3 "keccak_st" = globN s "keccak_st" := by
      unfold globN
      rw [← heff_goal3.globals (ofString "keccak_st") (by decide)]
    have hKS_post3 : KeccakBufsSafe post3 Nd :=
      keccakBufsSafe_of_grows hKS hag_post3
        (fun gs hgs => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
          rcases hgs with rfl | rfl
          · simp [bufferRegion, hkp_eq3]
          · simp [bufferRegion, hks_eq3])
        hext_post3
    have hpost3_loc : ∀ nm : String, (ofString nm) ≠ (ofString "j") →
        (ofString nm) ≠ (ofString "w5") →
        (ofString "off") ≠ (ofString nm) → (ofString "w5") ≠ (ofString nm) →
        post3.locals.lookup (ofString nm) = sL.locals.lookup (ofString nm) := by
      intro nm h1 h2 h3 h4
      dsimp only [post3]
      rw [resVarEq_lookup_ne _ _ _ _ h1, resVarEq_lookup_ne _ _ _ _ h2]
      simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [if_neg (by intro hcon; exact h3 (beq_iff_eq.mp hcon))]
      rw [hsB5_lc]
      simp only [HolFiniteMapExact.lookup_update, FUPDATE]
      rw [if_neg (by intro hcon; exact h4 (beq_iff_eq.mp hcon))]
    refine ⟨offL + w5v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hkmem3, if_neg (show ¬((3 : Nat) = 1) by decide),
        if_neg (show ¬((3 : Nat) = 2) by decide)]
      rw [BitVec.toNat_add, hoffL_s, hw5S, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [BitVec.toNat_add, hoffL_s, hw5S]
      have hbl := hbuf_lim
      rw [heapLimit_val] at hbl
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [hpost3, List.append_assoc]; exact heff_goal3
    · rw [hpost3]; exact heff_goal3.hp_le
    · rw [hpost3]; exact hNH_post3
    · rw [hpost3]; exact hext_post3
    · rw [hpost3]; exact hKS_post3
    · intro n hn off h8 hlt h24
      have h8n : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
      have hlt64 : n + off < 2 ^ 64 := by
        have h2 := (hN.1 n hn).2.2.1.2
        simp only [Inside, nodeIvl] at h2
        omega
      rw [hpost3]
      exact memW_eq_of_heapByteEff_disj hAR heff_goal3 (by omega) (hal_any3 n hn off hlt)
        hlt64 (hdisj_full3 n hn off h8 h24 hlt)
    · rw [hpost3]; exact (hpost3_loc "node" (by decide) (by decide) (by decide) (by decide)).trans hL_ln
    · rw [hpost3]; exact (hpost3_loc "fr" (by decide) (by decide) (by decide) (by decide)).trans hL_lf
    · rw [hpost3]; exact (hpost3_loc "k" (by decide) (by decide) (by decide) (by decide)).trans hL_lk
    · rw [hpost3]; exact (hpost3_loc "payload" (by decide) (by decide) (by decide) (by decide)).trans hL_lp
    · rw [hpost3]; exact (hpost3_loc "cbuf" (by decide) (by decide) (by decide) (by decide)).trans hL_lcb
    · rw [hpost3]; exact (hpost3_loc "clen" (by decide) (by decide) (by decide) (by decide)).trans hL_lcl
    · rw [hpost3]; exact (hpost3_loc "buf" (by decide) (by decide) (by decide) (by decide)).trans hL_lb
    · rw [hpost3]
      dsimp only [post3]
      rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
      simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [if_pos (by decide)]
    · rw [hpost3]; exact (hpost3_loc "hl" (by decide) (by decide) (by decide) (by decide)).trans hL_lhl
  · -- kinds 1/2: the two-write phase
    rename_i hkw3
    rw [finPhaseA] at hnone
    have hkw_ne3 : kw.toNat ≠ 3 := by
      intro h3
      exact hkw3 (by apply BitVec.eq_of_toNat_eq; rw [h3]; simp)
    have hk12 : memW s nodew.toNat = 1 ∨ memW s nodew.toNat = 2 := by omega
    have hdstE : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")]) =
        some (.val (.word (bufw + offw))) := by
      simp [evalHOLExact, evalListHOLExact, hlb, hlo, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hsrcE : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "cbuf")) = some (.val (.word cbufw)) := by
      simp [evalHOLExact, evalListHOLExact, hlcb, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hnE : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.var .local (ofString "clen")) = some (.val (.word clenw)) := by
      simp [evalHOLExact, evalListHOLExact, hlcl, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hdst0 : (bufw + offw).toNat = bufw.toNat + offw.toNat := by
      rw [BitVec.toNat_add]
      have h1 := bufw.isLt
      have h2 := offw.isLt
      omega
    have hfit12 : offw.toNat + rlpBytesLenPure (memB s cbufw.toNat) clenw.toNat ≤ bufLen := by
      rcases hk12 with h1 | h1
      · have := hfit1 h1; omega
      · have := hfit2 h1; omega
    obtain ⟨wl, mid, hwl, hdst_lt, hmid_gl, hmid_lc, heff_w, hcont_nt, hdc⟩ :=
      eval_decCall_rlp_encode_bytes_len_exact s "w"
        (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")])
        (.var .local (ofString "cbuf")) (.var .local (ofString "clen"))
        (bufw + offw) cbufw clenw
        (.seq
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w")]))
          (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
            (.decCall (ofString "w2") .one (ofString "rlp_encode_bytes")
              [.op .add [.var .local (ofString "buf"), .var .local (ofString "off")],
               .load .one (.op .add [.var .local (ofString "node"), .const 48]),
               .load .one (.op .add [.var .local (ofString "node"), .const 56])]
              (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "w2")])))
            (.decCall (ofString "w3") .one (ofString "node_write_ref")
              [.load .one (.op .add [.var .local (ofString "node"), .const 48]),
               .op .add [.var .local (ofString "buf"), .var .local (ofString "off")]]
              (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "w3")])))))
        ([(bufw.toNat, bufLen)] ++ keccakBufIvls s) ["heap_ptr"] hc hAR hdstE hsrcE hnE (hclen60 hk12)
        ⟨(bufw.toNat, bufLen), by simp, by simp only [hdst0]; omega,
          by rw [hdst0, rlpBytesLenPure_if_zero_lt]; omega⟩
        (by rw [hnone]; decide) (Or.inr hnone)
    rw [hdc] at hnone
    dsimp only at hnone
    rw [rlpBytesLenPure_if_zero_lt] at hwl
    have hAR_mid : ArenaReady mid := heff_w.arena
    have hext_mem : (nodew.toNat, nodeSize (memW s nodew.toNat)) ∈ nodeExtents s Nd := by
      simp only [nodeExtents]
      exact List.mem_flatMap.2 ⟨nodew.toNat, hnode_in, by simp [nodeIvl]⟩
    have hal_off : ∀ off : Nat, off + 8 ≤ nodeSize (memW s nodew.toNat) →
        Allocated s (nodew.toNat + off, 8) := by
      intro off hlt
      unfold Allocated Inside at hal_n ⊢
      simp only [nodeIvl] at hal_n
      dsimp only at hal_n ⊢
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    have hnode_buf_disj : ∀ off : Nat, off + 8 ≤ nodeSize (memW s nodew.toNat) →
        Disj (nodew.toNat + off, 8) (bufw.toNat, bufLen) := by
      intro off hlt
      have hbd := hbuf_disj _ hext_mem
      simp only [Disj] at hbd ⊢
      rcases hbd with h0 | h0 | h1 | h2
      · exact Or.inr (Or.inl h0)
      · exfalso
        have hsz := nodeSize_ge32 (memW s nodew.toNat)
        omega
      · exact Or.inr (Or.inr (Or.inr (by omega)))
      · exact Or.inr (Or.inr (by omega))
    have hnode_kec_disj : ∀ off : Nat, off + 8 ≤ nodeSize (memW s nodew.toNat) →
        ∀ iv ∈ keccakBufIvls s, Disj (nodew.toNat + off, 8) iv := by
      intro off hlt iv hiv
      have h1 := keccakBufIvls_disj_of_safe hKS iv hiv _ hext_mem
      simp only [Disj] at h1 ⊢
      rcases h1 with h0 | h0 | h1 | h2
      · exact Or.inr (Or.inl h0)
      · exfalso
        have hsz := nodeSize_ge32 (memW s nodew.toNat)
        omega
      · exact Or.inr (Or.inr (Or.inr (by omega)))
      · exact Or.inr (Or.inr (by omega))
    have hnode_stable : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ nodeSize (memW s nodew.toNat) →
        memW mid (nodew.toNat + off) = memW s (nodew.toNat + off) := by
      intro off h8 hlt
      have hn8 : nodew.toNat % 8 = 0 := hw_n.1
      refine memW_eq_of_heapByteEff_disj hAR heff_w (by omega) (hal_off off hlt) (by omega) ?_
      intro iv hiv hpos
      rcases List.mem_append.1 hiv with hiv | hiv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
        rcases hiv with rfl
        exact hnode_buf_disj off hlt
      · exact hnode_kec_disj off hlt iv hiv
    -- the sequenced assign off := off + w
    have hmid_off : mid.locals.lookup (ofString "off") = some (.val (.word offw)) := by
      rw [hmid_lc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hlo,
        show (ofString "w") ≠ (ofString "off") by decide]
    have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word wl)) := by
      rw [hmid_lc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have heoff : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
        (.op .add [.var .local (ofString "off"), .var .local (ofString "w")]) =
        some (.val (.word (offw + wl))) := by
      simp [evalHOLExact, evalListHOLExact, hmid_off, hmid_w, wordOpHOL, wordOp, valueIsWord,
        valueWord]
    have hvoff : isValidValueHOLFinite mid .local (ofString "off") (.val (.word (offw + wl))) =
        true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hmid_off, shapeOfHOLExact, shapeEqHOL]
    have hass : evaluateHOLFiniteState mid
        (.assign .local (ofString "off")
          (.op .add [.var .local (ofString "off"), .var .local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "off") (.val (.word (offw + wl))) mid) := by
      rw [evaluateHOLFiniteState_assign, heoff]
      dsimp only
      rw [if_pos hvoff]
      rfl
    obtain ⟨_, hite_none, hseq_eq⟩ := seq_none_rel mid
      (.assign .local (ofString "off")
        (.op .add [.var .local (ofString "off"), .var .local (ofString "w")]))
      (.ite (.cmp .equal (.var .local (ofString "k")) (.const 1))
        (.decCall (ofString "w2") .one (ofString "rlp_encode_bytes")
          [.op .add [.var .local (ofString "buf"), .var .local (ofString "off")],
           .load .one (.op .add [.var .local (ofString "node"), .const 48]),
           .load .one (.op .add [.var .local (ofString "node"), .const 56])]
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w2")])))
        (.decCall (ofString "w3") .one (ofString "node_write_ref")
          [.load .one (.op .add [.var .local (ofString "node"), .const 48]),
           .op .add [.var .local (ofString "buf"), .var .local (ofString "off")]]
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w3")]))))
      hnone
    rw [hass] at hite_none hseq_eq
    -- dispatch on k = 1
    rw [evaluateHOLFiniteState_ite] at hite_none
    have hlk_sA : (setVarHOLFinite (ofString "off") (.val (.word (offw + wl))) mid).locals.lookup
        (ofString "k") = some (.val (.word kw)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk, hmid_lc,
        show (ofString "off") ≠ (ofString "k") by decide,
        show (ofString "w") ≠ (ofString "k") by decide]
    have hcnd1 : @evalHOLExact 64 F _
        (setVarHOLFinite (ofString "off") (.val (.word (offw + wl))) mid).toExact
        (fun a => Classical.propDecidable
          ((setVarHOLFinite (ofString "off") (.val (.word (offw + wl))) mid).memaddrs a))
        (.cmp .equal (.var .local (ofString "k")) (.const 1)) =
        some (.val (.word (if kw = (1 : BitVec 64) then (1 : BitVec 64) else (0 : BitVec 64)))) := by
      simp [evalHOLExact, hlk_sA, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcnd1] at hite_none
    dsimp only at hite_none
    -- shared setup: the state after the outer encode call's sequenced assign
    set sA := setVarHOLFinite (ofString "off") (.val (.word (offw + wl))) mid with hsA_eq
    have hA_memaddr : sA.memaddrs = s.memaddrs := by
      simp only [hsA_eq, setVarHOLFinite]
      exact heff_w.memaddrs
    have hA_memory : ∀ a, sA.memory a = mid.memory a := by
      intro a
      simp [hsA_eq, setVarHOLFinite]
    have hA_loc : ∀ nm : String, (ofString "off") ≠ (ofString nm) → (ofString "w") ≠ (ofString nm) →
        sA.locals.lookup (ofString nm) = s.locals.lookup (ofString nm) := by
      intro nm h1 h2
      simp only [hsA_eq, setVarHOLFinite, hmid_lc, HolFiniteMapExact.lookup_update, FUPDATE]
      simp [h1, h2]
    have hA_node : sA.locals.lookup (ofString "node") = some (.val (.word nodew)) :=
      (hA_loc "node" (by decide) (by decide)).trans hln
    have hA_fr : sA.locals.lookup (ofString "fr") = some (.val (.word frw)) :=
      (hA_loc "fr" (by decide) (by decide)).trans hlf
    have hA_k : sA.locals.lookup (ofString "k") = some (.val (.word kw)) :=
      (hA_loc "k" (by decide) (by decide)).trans hlk
    have hA_pay : sA.locals.lookup (ofString "payload") = some (.val (.word pw)) :=
      (hA_loc "payload" (by decide) (by decide)).trans hlp
    have hA_cb : sA.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) :=
      (hA_loc "cbuf" (by decide) (by decide)).trans hlcb
    have hA_cl : sA.locals.lookup (ofString "clen") = some (.val (.word clenw)) :=
      (hA_loc "clen" (by decide) (by decide)).trans hlcl
    have hA_buf : sA.locals.lookup (ofString "buf") = some (.val (.word bufw)) :=
      (hA_loc "buf" (by decide) (by decide)).trans hlb
    have hA_hl : sA.locals.lookup (ofString "hl") = some (.val (.word hlw)) :=
      (hA_loc "hl" (by decide) (by decide)).trans hhl
    have hA_off : sA.locals.lookup (ofString "off") = some (.val (.word (offw + wl))) := by
      simp [hsA_eq, setVarHOLFinite, hmid_lc, hlo, HolFiniteMapExact.lookup_update, FUPDATE,
        show (ofString "w") ≠ (ofString "off") by decide]
    have hmem_node : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ nodeSize (memW s nodew.toNat) →
        sA.memory (BitVec.ofNat 64 (nodew.toNat + off)) =
          s.memory (BitVec.ofNat 64 (nodew.toNat + off)) := by
      intro off h8 hlt
      rw [hA_memory]
      by_contra hne
      have ha_nat : (BitVec.ofNat 64 (nodew.toNat + off)).toNat = nodew.toNat + off := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hlim; omega)]
      rcases heff_w.cell_frame _ hne with
        ⟨iv, hiv, hpos, hc1, hc2⟩ | ⟨hpos_fg, hfg1, hfg2⟩ | ⟨hpos_hf, hhf1, hhf2⟩
      · rw [ha_nat] at hc1 hc2
        rcases List.mem_append.1 hiv with hiv | hiv
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
          rcases hiv with rfl
          have hdj := hnode_buf_disj off hlt
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
        · have hdj := hnode_kec_disj off hlt iv hiv
          rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · rw [ha_nat] at hfg1 hfg2
        have hdj := P3MptSet.disj_allocated_freeGap hAR.2 (hal_off off hlt)
        dsimp [freeGap] at hdj hpos_fg hfg1 hfg2
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · rw [ha_nat] at hhf1 hhf2
        have hdj := P3MptSet.disj_allocated_heapFree hAR.2 (hal_off off hlt)
        dsimp [heapFree] at hdj hpos_hf hhf1 hhf2
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
    have hnsz56 : 56 ≤ nodeSize (memW s nodew.toNat) := by
      by_cases hm : memW s nodew.toNat = 1
      · rw [hm]; decide
      · by_cases hm2 : memW s nodew.toNat = 2
        · rw [hm2]; decide
        · have h3 : memW s nodew.toNat = 3 := by
            have := hk_le3
            have := hk123.1
            omega
          rw [h3]; decide
    have hwA : WordsOK sA (nodew.toNat, nodeSize (memW s nodew.toNat)) := by
      dsimp [WordsOK]
      refine ⟨hw_n.1, nodeSize_mod8 _, ?_⟩
      intro k hk
      obtain ⟨ws, hdom, hmem⟩ := hw_n.2.2 k hk
      refine ⟨ws, ?_, ?_⟩
      · rw [hA_memaddr]
        exact hdom
      · exact (hmem_node (8 * k) (by omega)
          (by have := nodeSize_mod8 (memW s nodew.toNat); omega)).trans hmem
    have haddr48 : @evalHOLExact 64 F _ sA.toExact (fun a => Classical.propDecidable (sA.memaddrs a))
        (.op .add [.var .local (ofString "node"), .const 48]) =
      some (.val (.word (nodew + BitVec.ofNat 64 48))) := by
      simp [evalHOLExact, evalListHOLExact, hA_node, wordOpHOL, wordOp, valueIsWord, valueWord]
    obtain ⟨v48, hld48, hv48n⟩ := eval_load_memW_of_wordsOK (base := nodew)
      (off := 48) (len := nodeSize (memW s nodew.toNat)) hwA (by omega) (by omega)
      (by have := hlim; have := hnode_hi; omega) haddr48
    have hmem_sA : memW sA (nodew.toNat + 48) = memW s (nodew.toNat + 48) := by
      have h1 : memW sA (nodew.toNat + 48) = memW mid (nodew.toNat + 48) := by
        simp only [memW, hA_memory]
      rw [h1, hnode_stable 48 (by omega) (by omega)]
    have hv48s : v48.toNat = memW s (nodew.toNat + 48) := by rw [hv48n, hmem_sA]
    by_cases hkw1 : kw = (1 : BitVec 64)
    · -- k = 1: the leaf value tail
      rw [if_pos hkw1] at hite_none
      rw [if_neg (by decide)] at hite_none
      have hkt1' : kw.toNat = 1 := by simp [hkw1]
      have hkmem : memW s nodew.toNat = 1 := by have := hkw_nat; omega
      have hnsz64 : nodeSize (memW s nodew.toNat) = 64 := by rw [hkmem]; decide
      have hA_code : sA.code = originalRuntimeCode := by
        rw [hsA_eq]
        simp only [setVarHOLFinite]
        exact hAR_mid.1.code
      have hAR_sA : ArenaReady sA := localsFree_arenaReady mid _ _ heff_w.arena
      have haddr56 : @evalHOLExact 64 F _ sA.toExact (fun a => Classical.propDecidable (sA.memaddrs a))
          (.op .add [.var .local (ofString "node"), .const 56]) =
        some (.val (.word (nodew + BitVec.ofNat 64 56))) := by
        simp [evalHOLExact, evalListHOLExact, hA_node, wordOpHOL, wordOp, valueIsWord, valueWord]
      obtain ⟨v60, hld60, hv60n⟩ := eval_load_memW_of_wordsOK (base := nodew)
        (off := 56) (len := nodeSize (memW s nodew.toNat)) hwA (by omega)
        (by have := hnsz64; omega)
        (by have := hlim; have := hnode_hi; omega) haddr56
      have hmem_sA56 : memW sA (nodew.toNat + 56) = memW s (nodew.toNat + 56) := by
        have h1 : memW sA (nodew.toNat + 56) = memW mid (nodew.toNat + 56) := by
          simp only [memW, hA_memory]
        rw [h1, hnode_stable 56 (by omega) (by have := hnsz64; omega)]
      have hv60s : v60.toNat = memW s (nodew.toNat + 56) := by rw [hv60n, hmem_sA56]
      have hn60 : v60.toNat < 2 ^ 60 := by
        rw [hv60s]
        have h1 := hval40 hkmem
        omega
      have hnooff : offw.toNat + wl.toNat < 2 ^ 64 := by
        have h1 := offw.isLt
        have h2 := wl.isLt
        omega
      have hdst0 : (bufw + (offw + wl)).toNat = bufw.toNat + (offw.toNat + wl.toNat) := by
        rw [BitVec.toNat_add, BitVec.toNat_add]
        have h1 := bufw.isLt
        have h2 := offw.isLt
        have h3 := wl.isLt
        omega
      have hlen2A : rlpBytesLenPure (if 0 < v60.toNat then memB sA v48.toNat else 0) v60.toNat =
          rlpBytesLenPure
            (if 0 < memW s (nodew.toNat + 56) then memB s (memW s (nodew.toNat + 48)) else 0)
            (memW s (nodew.toNat + 56)) := by
        rw [hv48s, hv60s]
        by_cases hv1 : memW s (nodew.toNat + 56) = 1
        · obtain ⟨hno_buf, hno_kec, hno_fg, hno_hf⟩ := hval1_no hkmem hv1
          have heff_sA0 : R16Shards.WkBlockTxEnc.HeapByteEff s sA
              ([(bufw.toNat, bufLen)] ++ keccakBufIvls s) ["heap_ptr"] :=
            heff_w.locals_clock _ _
          have hlt_v48 : memW s (nodew.toNat + 48) < 2 ^ 64 :=
            memW_lt_two_pow_64 s (nodew.toNat + 48)
          have hmemB_v48 : memB sA (memW s (nodew.toNat + 48)) = memB s (memW s (nodew.toNat + 48)) := by
            by_contra hne
            rcases heff_sA0.byte_frame (memW s (nodew.toNat + 48)) hlt_v48 hne with
              ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
            · rcases List.mem_append.1 hiv with hiv | hiv
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv; subst hiv
                exact hno_buf ⟨hb1, hb2⟩
              · exact hno_kec iv hiv ⟨hb1, hb2⟩
            · exact hno_fg ⟨hfg1, hfg2⟩
            · exact hno_hf ⟨hhf1, hhf2⟩
          rw [hmemB_v48]
        · exact rlpBytesLenPure_congr_ne_one hv1
      have hfit1'S : offw.toNat + wl.toNat +
          rlpBytesLenPure
            (if 0 < memW s (nodew.toNat + 56) then memB s (memW s (nodew.toNat + 48)) else 0)
            (memW s (nodew.toNat + 56)) ≤ bufLen := by
        have h2 := hfit1 hkmem
        have := hwl
        omega
      have hsrcE2 : @evalHOLExact 64 F _ sA.toExact (fun a => Classical.propDecidable (sA.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "node"), .const 48])) =
        some (.val (.word v48)) := hld48
      have hnE2 : @evalHOLExact 64 F _ sA.toExact (fun a => Classical.propDecidable (sA.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "node"), .const 56])) =
        some (.val (.word v60)) := hld60
      have hdstE2 : @evalHOLExact 64 F _ sA.toExact (fun a => Classical.propDecidable (sA.memaddrs a))
          (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")]) =
        some (.val (.word (bufw + (offw + wl)))) := by
        simp [evalHOLExact, evalListHOLExact, hA_buf, hA_off, wordOpHOL, wordOp, valueIsWord,
          valueWord]
      rcases eval_decCall_rlp_encode_bytes_len_exact sA "w2"
          (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")])
          (.load .one (.op .add [.var .local (ofString "node"), .const 48]))
          (.load .one (.op .add [.var .local (ofString "node"), .const 56]))
          (bufw + (offw + wl)) v48 v60
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w2")]))
          ([(bufw.toNat, bufLen)] ++ keccakBufIvls sA) ["heap_ptr"] hA_code hAR_sA
          hdstE2 hsrcE2 hnE2 hn60
          ⟨(bufw.toNat, bufLen), by simp,
            by simp only [hdst0]; omega,
            by rw [hdst0, hlen2A]; omega⟩
          (by rw [hite_none]; decide) (Or.inr hite_none) with
        ⟨len2, sB2, hlen2, hdst_lt2, hsB2_gl, hsB2_lc, heff_w2, hcont_nt2, hdc2⟩
      have hlen2S : len2.toNat =
          rlpBytesLenPure
            (if 0 < memW s (nodew.toNat + 56) then memB s (memW s (nodew.toNat + 48)) else 0)
            (memW s (nodew.toNat + 56)) := by
        rw [hlen2]; exact hlen2A
      have hB_off : sB2.locals.lookup (ofString "off") = some (.val (.word (offw + wl))) := by
        rw [hsB2_lc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, hA_off,
          show (ofString "w") ≠ (ofString "off") by decide,
          show (ofString "w2") ≠ (ofString "off") by decide]
      have hB_w2 : sB2.locals.lookup (ofString "w2") = some (.val (.word len2)) := by
        rw [hsB2_lc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have heoffB2 : @evalHOLExact 64 F _ sB2.toExact
          (fun a => Classical.propDecidable (sB2.memaddrs a))
          (.op .add [.var .local (ofString "off"), .var .local (ofString "w2")]) =
          some (.val (.word ((offw + wl) + len2))) := by
        simp [evalHOLExact, evalListHOLExact, hB_off, hB_w2, wordOpHOL, wordOp, valueIsWord,
          valueWord]
      have hval_off2 : isValidValueHOLFinite sB2 .local (ofString "off")
          (.val (.word ((offw + wl) + len2))) = true := by
        simp [isValidValueHOLFinite, lookupKvarHOLFinite, hB_off, shapeOfHOLExact, shapeEqHOL]
      have hass2 : (evaluateHOLFiniteState sB2
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w2")]))) =
        (none, setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2) := by
        rw [evaluateHOLFiniteState_assign, heoffB2]
        dsimp only
        rw [if_pos hval_off2]
        rfl
      -- the final post state (two resVarEq layers over the assign's store)
      have hpost1 : (evaluateHOLFiniteState s finDispatch).2 =
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } := by
        rw [finDispatch, evaluateHOLFiniteState_ite, hcnd]
        dsimp only
        rw [hsel, if_neg hkw3, finPhaseA, hdc]
        dsimp only
        rw [hseq_eq]
        dsimp only
        rw [evaluateHOLFiniteState_ite, hcnd1]
        dsimp only
        rw [if_pos hkw1, if_neg (by decide)]
        rw [hdc2]
        dsimp only
        rw [hass2]
      -- the effect chain
      have hshuf1 : ∀ i ∈ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s),
          i ∈ (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s)) := by
        intro i hi
        rcases List.mem_append.1 hi with hi | hi
        · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl hi)))
        · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr hi)))
      have heff_sA : R16Shards.WkBlockTxEnc.HeapByteEff s sA
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        (heff_w.locals_clock _ _).mono
          (fun i hi _ => Or.inl ⟨i, hshuf1 i hi, le_rfl, le_rfl⟩) (by simp)
      have hA_glob : sA.globals = mid.globals := by
        rw [hsA_eq]; simp only [setVarHOLFinite]
      have hkp_sA : globN sA "keccak_pad" = globN s "keccak_pad" := by
        unfold globN
        rw [hA_glob, ← hmid_gl]
      have hks_sA : globN sA "keccak_st" = globN s "keccak_st" := by
        unfold globN
        rw [hA_glob, ← hmid_gl]
      have heff_w2R : R16Shards.WkBlockTxEnc.HeapByteEff sA sB2
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] := by
        refine heff_w2.mono (fun i hi _ => ?_) (fun _ hg => hg)
        rcases List.mem_append.1 hi with hrl | hkc
        · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_left _ hrl), le_rfl, le_rfl⟩
        · have hkec_sA : keccakBufIvls sA = keccakBufIvls s := by
            simp only [keccakBufIvls, bufferRegion, hkp_sA, hks_sA]
          rw [hkec_sA] at hkc
          exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkc), le_rfl, le_rfl⟩
      have heff_sB2 : R16Shards.WkBlockTxEnc.HeapByteEff s sB2
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        heff_sA.trans heff_w2R
      have heff_sC1 : R16Shards.WkBlockTxEnc.HeapByteEff s
          (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2)
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        heff_sB2.locals_clock _ _
      have heff_post : R16Shards.WkBlockTxEnc.HeapByteEff s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) }
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        heff_sC1.locals_clock _ _
      have heff_goal : R16Shards.WkBlockTxEnc.HeapByteEff s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) }
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        heff_post
      have heff_big : R16Shards.WkBlockTxEnc.HeapByteEff s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) }
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr", "keccak_pad", "keccak_st"] :=
        heff_goal.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (by simp)
      have heff_cache : R16Shards.WkBlockTxEnc.HeapByteEff s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) }
          (nodeCacheIvls Nd ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr", "keccak_pad", "keccak_st"] := by
        refine heff_big.mono (fun i hi _ => ?_) (fun _ hg => hg)
        rcases List.mem_append.1 hi with hm24 | hrest
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
          exact Or.inl ⟨(m + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩),
            by dsimp; omega, by dsimp; omega⟩
        · exact Or.inl ⟨i, List.mem_append_right _ hrest, le_rfl, le_rfl⟩
      -- NodeHeap/extents via the cache lemma
      have hextra_disj : ∀ e ∈ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s),
          ∀ o ∈ nodeExtents s Nd, Disj e o := by
        intro e he o ho
        rcases List.mem_append.1 he with he | he
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl
          exact hbuf_disj o ho
        · exact keccakBufIvls_disj_of_safe hKS e he o ho
      have hal_any : ∀ n ∈ Nd, ∀ off : Nat, off + 8 ≤ nodeSize (memW s n) →
          Allocated s (n + off, 8) := by
        intro n hn off hlt
        obtain ⟨_, hal_n', _, _, _, _, _, _, _, _⟩ := hN.1 n hn
        unfold Allocated Inside at hal_n' ⊢
        simp only [nodeIvl] at hal_n'
        dsimp only at hal_n' ⊢
        rcases hal_n' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      have hext_mem' : ∀ n ∈ Nd, (n, nodeSize (memW s n)) ∈ nodeExtents s Nd := by
        intro n hn
        simp only [nodeExtents]
        exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
      have disj_sub : ∀ i i' j j' : Ivl, i.1 ≤ i'.1 → i'.1 + i'.2 ≤ i.1 + i.2 →
          j.1 ≤ j'.1 → j'.1 + j'.2 ≤ j.1 + j.2 → Disj i j → Disj i' j' := by
        intro i i' j j' hi1 hi2 hj1 hj2 h
        dsimp [Disj] at h ⊢
        rcases h with h0 | h0 | h1 | h2
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr (by omega)))
      have hdisj_full : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 → off ≠ 24 →
          off + 8 ≤ nodeSize (memW s n) →
          ∀ iv ∈ (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s)), 0 < iv.2 → Disj (n + off, 8) iv := by
        intro n hn off h8 h24 hlt iv hiv hpos
        have hsz := nodeSize_ge32 (memW s n)
        rcases List.mem_append.1 hiv with hiv | hiv
        · obtain ⟨n', hn', rfl⟩ := List.mem_map.1 hiv
          by_cases hnn : n' = n
          · subst hnn
            dsimp only [Disj]
            rcases Nat.lt_or_ge off 24 with h | h
            · exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inr (Or.inr (Or.inr (by omega)))
          · have hsz' := nodeSize_ge32 (memW s n')
            exact disj_sub (n, nodeSize (memW s n)) (n + off, 8)
              (n', nodeSize (memW s n')) (n' + 24, 8) (by omega) (by omega) (by omega) (by omega)
              (hN.2 n hn n' hn' (Ne.symm hnn))
        · rcases List.mem_append.1 hiv with hiv | hiv
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
            rcases hiv with rfl
            exact disj_sub (n, nodeSize (memW s n)) (n + off, 8)
              (bufw.toNat, bufLen) (bufw.toNat, bufLen) (by omega) (by omega) (by omega) (by omega)
              (disj_comm (hbuf_disj _ (hext_mem' n hn)))
          · exact disj_sub (n, nodeSize (memW s n)) (n + off, 8) iv iv (by omega) (by omega) (by omega) (by omega)
              (disj_comm (keccakBufIvls_disj_of_safe hKS iv hiv _ (hext_mem' n hn)))
      have hrlp_post : ∀ n ∈ Nd, memW
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } (n + 16) < 2 ^ 40 := by
        intro n hn
        have h8n : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
        have hsz := nodeSize_ge32 (memW s n)
        have hlt : n + 16 < 2 ^ 64 := by
          have h2 := (hN.1 n hn).2.2.1.2
          simp only [Inside, nodeIvl] at h2
          have := hlim
          omega
        have hmem16 : memW
            { ({setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                locals := HolFiniteMapExact.resVarEq
                  (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                  (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } (n + 16) =
            memW s (n + 16) :=
          memW_eq_of_heapByteEff_disj hAR heff_goal (by omega) (hal_any n hn 16 (by omega))
            (by omega) (hdisj_full n hn 16 (by omega) (by decide) (by omega))
        rw [hmem16]
        exact (hN.1 n hn).2.2.2.2.2.2.2.1
      obtain ⟨hNH_post, hext_post⟩ :=
        nodeHeap_of_heapByteEff_cache hAR hN heff_cache hextra_disj hrlp_post
      have hag_post : AllocatorGrows s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } := ⟨heff_big.hp_le, heff_big.sp_le⟩
      have hkp_eq : globN
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } "keccak_pad" =
          globN s "keccak_pad" := by
        unfold globN
        rw [← heff_goal.globals (ofString "keccak_pad") (by decide)]
      have hks_eq : globN
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } "keccak_st" =
          globN s "keccak_st" := by
        unfold globN
        rw [← heff_goal.globals (ofString "keccak_st") (by decide)]
      have hKS_post : KeccakBufsSafe
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                (ofString "w2", sA.locals.lookup (ofString "w2")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2 with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + len2))) sB2).locals
                   (ofString "w2", sA.locals.lookup (ofString "w2")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } Nd :=
        keccakBufsSafe_of_grows hKS hag_post
          (fun gs hgs => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
            rcases hgs with rfl | rfl
            · simp [bufferRegion, hkp_eq]
            · simp [bufferRegion, hks_eq])
        hext_post
      have hpost_loc : ∀ nm : String, (ofString nm) ≠ (ofString "w") →
          (ofString nm) ≠ (ofString "w2") →
          (ofString "off") ≠ (ofString nm) → (ofString "w2") ≠ (ofString nm) →
          (evaluateHOLFiniteState s finDispatch).2.locals.lookup (ofString nm) =
            s.locals.lookup (ofString nm) := by
        intro nm h1 h2 h3 h4
        rw [hpost1]
        dsimp only
        rw [resVarEq_lookup_ne _ _ _ _ h1, resVarEq_lookup_ne _ _ _ _ h2]
        simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by intro hcon; exact h3 (beq_iff_eq.mp hcon))]
        rw [hsB2_lc]
        simp only [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by intro hcon; exact h4 (beq_iff_eq.mp hcon))]
        exact hA_loc nm h3 (Ne.symm h1)
      refine ⟨(offw + wl) + len2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hkmem, if_pos (show ((1 : Nat) = 1) by decide)]
        rw [BitVec.toNat_add, BitVec.toNat_add, hwl, hlen2S]
        omega
      · rw [BitVec.toNat_add, BitVec.toNat_add]
        have h1 := offw.isLt
        have h2 := wl.isLt
        have h3 := len2.isLt
        rw [hwl, hlen2S]
        have hbl := hbuf_lim
        rw [heapLimit_val] at hbl
        omega
      · rw [hpost1, List.append_assoc]; exact heff_goal
      · rw [hpost1]; exact heff_goal.hp_le
      · rw [hpost1]; exact hNH_post
      · rw [hpost1]; exact hext_post
      · rw [hpost1]; exact hKS_post
      · intro n hn off h8 hlt h24
        have h8n : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
        have hsz := nodeSize_ge32 (memW s n)
        have hlt64 : n + off < 2 ^ 64 := by
          have h2 := (hN.1 n hn).2.2.1.2
          simp only [Inside, nodeIvl] at h2
          have := hlim
          omega
        rw [hpost1]
        exact memW_eq_of_heapByteEff_disj hAR heff_goal (by omega) (hal_any n hn off hlt)
          hlt64 (hdisj_full n hn off h8 h24 hlt)
      · exact (hpost_loc "node" (by decide) (by decide) (by decide) (by decide)).trans hln
      · exact (hpost_loc "fr" (by decide) (by decide) (by decide) (by decide)).trans hlf
      · exact (hpost_loc "k" (by decide) (by decide) (by decide) (by decide)).trans hlk
      · exact (hpost_loc "payload" (by decide) (by decide) (by decide) (by decide)).trans hlp
      · exact (hpost_loc "cbuf" (by decide) (by decide) (by decide) (by decide)).trans hlcb
      · exact (hpost_loc "clen" (by decide) (by decide) (by decide) (by decide)).trans hlcl
      · exact (hpost_loc "buf" (by decide) (by decide) (by decide) (by decide)).trans hlb
      · rw [hpost1]
        dsimp only
        rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
        simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_pos (by decide)]
      · exact (hpost_loc "hl" (by decide) (by decide) (by decide) (by decide)).trans hhl
    · -- k = 2: the child-reference write
      rw [if_neg hkw1] at hite_none
      rw [if_pos rfl] at hite_none
      have hkt1 : kw.toNat ≠ 1 := by
        intro h
        exact hkw1 (BitVec.eq_of_toNat_eq h)
      have hkmem : memW s nodew.toNat = 2 := by
        have h1 := hk_le3
        have h2 := hk123.1
        have h3 := hkt1
        have h4 := hkw_ne3
        have h5 : kw.toNat = memW s nodew.toNat := hkw_nat
        omega
      have hA_code : sA.code = originalRuntimeCode := by
        rw [hsA_eq]
        simp only [setVarHOLFinite]
        exact hAR_mid.1.code
      have hroot := hroot_ext hkmem
      have hAR_sA : ArenaReady sA := localsFree_arenaReady mid _ _ heff_w.arena
      have hnooff : offw.toNat + wl.toNat < 2 ^ 64 := by
        have h1 := offw.isLt
        have h2 := wl.isLt
        omega
      have hdst0 : (bufw + (offw + wl)).toNat = bufw.toNat + (offw.toNat + wl.toNat) := by
        rw [BitVec.toNat_add, BitVec.toNat_add]
        have h1 := bufw.isLt
        have h2 := offw.isLt
        have h3 := wl.isLt
        omega
      have hfit2' : offw.toNat + wl.toNat + nodeRefBytes s v48.toNat ≤ bufLen := by
        have h2 := hfit2 hkmem
        rw [← hv48s] at h2
        have := hwl
        omega
      have hroot48 : RootIn Nd v48.toNat := by rw [hv48s]; exact hroot
      have hndb : nodeRefBytes sA v48.toNat = nodeRefBytes s v48.toNat := by
        by_cases h0 : v48.toNat = 0
        · unfold nodeRefBytes; simp [h0]
        · rcases hroot48 with h48 | h48
          · exact absurd h48 h0
          · obtain ⟨_, hal_c, hin_c, hw_c, _⟩ := hN.1 v48.toNat h48
            have hsz_c := nodeSize_ge32 (memW s v48.toNat)
            have hn8c : v48.toNat % 8 = 0 := hw_c.1
            have hlt_c : v48.toNat + nodeSize (memW s v48.toNat) < 2 ^ 64 := by
              have h2 := hin_c.2
              dsimp [nodeIvl] at h2
              have := hlim
              omega
            have hext48 : (v48.toNat, nodeSize (memW s v48.toNat)) ∈ nodeExtents s Nd := by
              simp only [nodeExtents]
              exact List.mem_flatMap.2 ⟨v48.toNat, h48, by simp [nodeIvl]⟩
            have hmemw : ∀ X : Nat, X % 8 = 0 → v48.toNat ≤ X →
                X + 8 ≤ v48.toNat + nodeSize (memW s v48.toNat) → memW mid X = memW s X := by
              intro X h8 h1 h2
              refine memW_eq_of_heapByteEff_disj hAR heff_w h8 ?_ (by omega) ?_
              · have hal' := hal_c
                unfold Allocated Inside at hal' ⊢
                simp only [nodeIvl] at hal'
                dsimp only at hal' ⊢
                rcases hal' with ⟨k1, k2⟩ | ⟨k1, k2⟩
                · exact Or.inl ⟨by omega, by omega⟩
                · exact Or.inr ⟨by omega, by omega⟩
              · intro iv hiv hpos
                have hsub : ∀ j : Ivl,
                    Disj (v48.toNat, nodeSize (memW s v48.toNat)) j → Disj (X, 8) j := by
                  intro j hdj
                  dsimp [Disj] at hdj ⊢
                  rcases hdj with h0' | h0' | hd1 | hd2
                  · exact absurd h0' (by have := hsz_c; omega)
                  · exact Or.inr (Or.inl h0')
                  · exact Or.inr (Or.inr (Or.inl (by omega)))
                  · exact Or.inr (Or.inr (Or.inr (by omega)))
                rcases List.mem_append.1 hiv with hiv | hiv
                · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
                  rcases hiv with rfl
                  exact hsub _ (disj_comm (hbuf_disj _ hext48))
                · simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hiv
                  rcases hiv with rfl | rfl
                  · exact hsub _ ((hKS ("keccak_pad", 136) (by decide)).2 _ hext48)
                  · exact hsub _ ((hKS ("keccak_st", 200) (by decide)).2 _ hext48)
            have hm1 : memW sA v48.toNat = memW mid v48.toNat :=
              memW_eq_of_cell_eq (hA_memory (BitVec.ofNat 64 v48.toNat))
            have hm2 : memW sA (v48.toNat + 16) = memW mid (v48.toNat + 16) :=
              memW_eq_of_cell_eq (hA_memory (BitVec.ofNat 64 (v48.toNat + 16)))
            unfold nodeRefBytes
            rw [hm1, hm2, hmemw v48.toNat (by omega) (by omega) (by omega),
              hmemw (v48.toNat + 16) (by omega) (by omega) (by omega)]
      have hmem_nd : ∀ n ∈ Nd, ∀ off : Nat, n ≤ off → off % 8 = 0 →
          off + 8 ≤ n + nodeSize (memW s n) → memW mid off = memW s off := by
        intro n hn off h1 h8 h2
        obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
        have hsz_n := nodeSize_ge32 (memW s n)
        have hlt_n : n + nodeSize (memW s n) < 2 ^ 64 := by
          have h3 := hin_n.2
          dsimp [nodeIvl] at h3
          have := hlim
          omega
        have halloc : Allocated s (off, 8) := by
          have hal' := hal_n
          unfold Allocated Inside at hal' ⊢
          simp only [nodeIvl] at hal'
          dsimp only at hal' ⊢
          rcases hal' with ⟨k1, k2⟩ | ⟨k1, k2⟩
          · exact Or.inl ⟨by omega, by omega⟩
          · exact Or.inr ⟨by omega, by omega⟩
        have hext_n : (n, nodeSize (memW s n)) ∈ nodeExtents s Nd :=
          List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
        refine memW_eq_of_heapByteEff_disj hAR heff_w h8 halloc (by omega) ?_
        intro iv hiv hpos
        have hsub : ∀ j : Ivl, Disj (n, nodeSize (memW s n)) j → Disj (off, 8) j := by
          intro j hdj
          dsimp [Disj] at hdj ⊢
          rcases hdj with h0' | h0' | hd1 | hd2
          · exact absurd h0' (by have := hsz_n; omega)
          · exact Or.inr (Or.inl h0')
          · exact Or.inr (Or.inr (Or.inl (by omega)))
          · exact Or.inr (Or.inr (Or.inr (by omega)))
        rcases List.mem_append.1 hiv with hiv | hiv
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
          rcases hiv with rfl
          exact hsub _ (disj_comm (hbuf_disj _ hext_n))
        · simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hiv
          rcases hiv with rfl | rfl
          · exact hsub _ ((hKS ("keccak_pad", 136) (by decide)).2 _ hext_n)
          · exact hsub _ ((hKS ("keccak_st", 200) (by decide)).2 _ hext_n)
      have hmem_nd_sA : ∀ n ∈ Nd, ∀ off : Nat, n ≤ off → off % 8 = 0 →
          off + 8 ≤ n + nodeSize (memW s n) → memW sA off = memW s off := by
        intro n hn off h1 h8 h2
        rw [memW_eq_of_cell_eq (hA_memory (BitVec.ofNat 64 off))]
        exact hmem_nd n hn off h1 h8 h2
      have hext_sA_mem : ∀ o ∈ nodeExtents sA Nd, o ∈ nodeExtents s Nd := by
        intro o ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        refine List.mem_flatMap.2 ⟨n, hn, ?_⟩
        have hsz_n := nodeSize_ge32 (memW s n)
        have h8n : n % 8 = 0 := by
          obtain ⟨_, _, _, hw_nn, _⟩ := hN.1 n hn
          exact hw_nn.1
        have hm_n : memW sA n = memW s n := hmem_nd_sA n hn n (by omega) h8n (by omega)
        simp only [nodeIvl, nodePath, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hno ⊢
        rcases hno with hno | hno
        · left
          rw [hno, hm_n]
        · right
          rw [hno, hm_n]
          by_cases hk12 : memW s n = 1 ∨ memW s n = 2
          · have hsz48 : nodeSize (memW s n) ≥ 48 := by
              rcases hk12 with hk | hk
              · rw [hk]; simp [nodeSize]
              · rw [hk]; simp [nodeSize]
            rw [hmem_nd_sA n hn (n + 32) (by omega) (by omega) (by omega),
              hmem_nd_sA n hn (n + 40) (by omega) (by omega) (by omega)]
          · have hcFs : ¬((memW s n = 1 ∨ memW s n = 2) ∧ memW s (n + 40) ≠ 0) :=
              fun hc => hk12 hc.1
            have hcFa : ¬((memW s n = 1 ∨ memW s n = 2) ∧ memW sA (n + 40) ≠ 0) :=
              fun hc => hk12 hc.1
            rw [if_neg hcFa, if_neg hcFs]
      have hA_glob : sA.globals = mid.globals := by
        rw [hsA_eq]; simp only [setVarHOLFinite]
      have hkp_sA : globN sA "keccak_pad" = globN s "keccak_pad" := by
        unfold globN
        rw [hA_glob, ← hmid_gl]
      have hks_sA : globN sA "keccak_st" = globN s "keccak_st" := by
        unfold globN
        rw [hA_glob, ← hmid_gl]
      have hbr_pad : bufferRegion sA ("keccak_pad", 136) = bufferRegion s ("keccak_pad", 136) := by
        simp [bufferRegion, hkp_sA]
      have hbr_st : bufferRegion sA ("keccak_st", 200) = bufferRegion s ("keccak_st", 200) := by
        simp [bufferRegion, hks_sA]
      have hAG_sA : AllocatorGrows s sA := by
        refine ⟨?_, ?_⟩
        · unfold globN; rw [hA_glob]; exact heff_w.hp_le
        · unfold globN; rw [hA_glob]; exact heff_w.sp_le
      have hGI_sA : GuestInv sA :=
        ⟨hA_code, by rw [hA_memaddr]; exact hAR.1.memaddrs,
          by rw [hsA_eq]; simp only [setVarHOLFinite]; exact hAR_mid.1.shMemaddrs,
          by rw [hsA_eq]; simp only [setVarHOLFinite]; exact hAR_mid.1.baseAddr⟩
      have hN_sA : NodeHeap sA Nd := by
        refine (nodeHeap_congr_cache hAR.1 hGI_sA hAG_sA hN ?_ ?_ ?_).1
        · intro n hn k hk hk1 hk2 hk3
          obtain ⟨_, hal_n, hin_n, hw_n, _, _, _, _, _, _⟩ := hN.1 n hn
          have hn8 : n % 8 = 0 := hw_n.1
          have hsz_mod := nodeSize_mod8 (memW s n)
          exact hmem_nd_sA n hn (n + 8 * k) (by omega) (by omega) (by omega)
        · intro n hn
          obtain ⟨_, _, _, hw_n, _, _, _, _, _, _⟩ := hN.1 n hn
          have hn8 : n % 8 = 0 := hw_n.1
          have hsz_n := nodeSize_ge32 (memW s n)
          rw [hmem_nd_sA n hn (n + 16) (by omega) (by omega) (by omega)]
          exact (hN.1 n hn).2.2.2.2.2.2.2.1
        · intro n hn h12 hlen0 j hj
          obtain ⟨_, _, _, _, _, _, hkey_n, _⟩ := hN.1 n hn
          rcases hkey_n h12 with h0 | ⟨_, hal_p, hin_p, hdisj_p⟩
          · exact absurd h0 hlen0
          · have hp_mem : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
              unfold nodeExtents
              exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
            have hb_lt : memW s (n + 32) + j < 2 ^ 64 := by
              have := hin_p.2; dsimp at this; omega
            by_contra hne
            rcases heff_w.byte_frame (memW s (n + 32) + j) hb_lt hne with
              ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
            · rcases List.mem_append.1 hiv with hbufcase | hkec
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbufcase
                rcases hbufcase with rfl
                have hdj := hbuf_disj _ hp_mem
                rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
              · simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hkec
                rcases hkec with hkec | hkec
                · rw [hkec] at hb1 hb2
                  have hdj := disj_comm ((hKS ("keccak_pad", 136) (by decide)).2 _ hp_mem)
                  rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
                · rw [hkec] at hb1 hb2
                  have hdj := disj_comm ((hKS ("keccak_st", 200) (by decide)).2 _ hp_mem)
                  rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
            · have hdj := P3MptSet.disj_allocated_freeGap hAR.2 hal_p
              dsimp [freeGap] at hdj hfg1 hfg2
              rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
            · have hdj := P3MptSet.disj_allocated_heapFree hAR.2 hal_p
              dsimp [heapFree] at hdj hhf1 hhf2
              rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      rcases eval_decCall_node_write_ref sA Nd "w3"
          (.load .one (.op .add [.var .local (ofString "node"), .const 48]))
          (.op .add [.var .local (ofString "buf"), .var .local (ofString "off")])
          v48 (bufw + (offw + wl))
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w3")]))
          ([(bufw.toNat, bufLen)]) ["heap_ptr"] hA_code hAR_sA hN_sA hroot48 hld48
          (by simp [evalHOLExact, evalListHOLExact, hA_buf, hA_off, wordOpHOL, wordOp,
            valueIsWord, valueWord])
          (by rw [hdst0, hndb]; have := hbuf_lim; have := hlim_he; have := hfit2'; omega)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]
              refine ⟨(bufw.toNat, bufLen), by simp, ?_, ?_⟩
              · change bufw.toNat ≤ (bufw + (offw + wl)).toNat
                rw [hdst0]; omega
              · change (bufw + (offw + wl)).toNat + nodeRefBytes sA v48.toNat ≤
                  bufw.toNat + bufLen
                rw [hdst0, hndb]; have := hfit2'; omega)
          (by simp) (by rw [hite_none]; simp) with
        ⟨w3v, sB, hw3, hsB_lc, heff_w3, heff_w3', himp, hnt2, hdc3⟩ | hright
      have hA1 : ∀ e ∈ ([(bufw.toNat, bufLen)] : List Ivl), 0 < e.2 →
          ∀ o ∈ nodeExtents sA Nd, Disj e o := by
        intro e he hpos o ho
        have ho' : o ∈ nodeExtents s Nd := hext_sA_mem o ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl
        exact hbuf_disj o ho'
      have hA2 : ∀ o ∈ nodeExtents sA Nd,
          Disj (bufferRegion sA ("keccak_pad", 136)) o ∧
          Disj (bufferRegion sA ("keccak_st", 200)) o := by
        intro o ho
        have ho' : o ∈ nodeExtents s Nd := hext_sA_mem o ho
        refine ⟨?_, ?_⟩
        · rw [hbr_pad]
          exact keccakBufIvls_disj_of_safe hKS _ (by simp [keccakBufIvls]) o ho'
        · rw [hbr_st]
          exact keccakBufIvls_disj_of_safe hKS _ (by simp [keccakBufIvls]) o ho'
      obtain ⟨hNH_sB, hext_sB, hpres, href⟩ := himp hA1 hA2
      have hB_off : sB.locals.lookup (ofString "off") = some (.val (.word (offw + wl))) := by
        rw [hsB_lc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, hA_off,
          show (ofString "w3") ≠ (ofString "off") by decide]
      have hB_w3 : sB.locals.lookup (ofString "w3") = some (.val (.word w3v)) := by
        rw [hsB_lc]
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have heoffB : @evalHOLExact 64 F _ sB.toExact (fun a => Classical.propDecidable (sB.memaddrs a))
          (.op .add [.var .local (ofString "off"), .var .local (ofString "w3")]) =
        some (.val (.word ((offw + wl) + w3v))) := by
        simp [evalHOLExact, evalListHOLExact, hB_off, hB_w3, wordOpHOL, wordOp, valueIsWord,
          valueWord]
      have hval_off : isValidValueHOLFinite sB .local (ofString "off")
          (.val (.word ((offw + wl) + w3v))) = true := by
        simp [isValidValueHOLFinite, lookupKvarHOLFinite, hB_off, shapeOfHOLExact, shapeEqHOL]
      have hassign : (evaluateHOLFiniteState sB
          (.assign .local (ofString "off")
            (.op .add [.var .local (ofString "off"), .var .local (ofString "w3")]))) =
        (none, setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB) := by
        rw [evaluateHOLFiniteState_assign, heoffB]
        dsimp only
        rw [if_pos hval_off]
        rfl
      rw [hdc3] at hite_none
      dsimp only at hite_none
      rw [hassign] at hite_none
      -- the final post state (two resVarEq layers over the assign's store)
      have hpost : (evaluateHOLFiniteState s finDispatch).2 =
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } := by
        rw [finDispatch, evaluateHOLFiniteState_ite, hcnd]
        dsimp only
        rw [hsel, if_neg hkw3, finPhaseA, hdc]
        dsimp only
        rw [hseq_eq]
        dsimp only
        rw [evaluateHOLFiniteState_ite, hcnd1]
        dsimp only
        rw [if_neg hkw1, if_pos rfl]
        rw [hdc3]
        dsimp only
        rw [hassign]
      -- the effect chain
      have hshuf1 : ∀ i ∈ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s),
          i ∈ (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s)) := by
        intro i hi
        rcases List.mem_append.1 hi with hi | hi
        · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl hi)))
        · exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr hi)))
      have heff_sA : R16Shards.WkBlockTxEnc.HeapByteEff s sA
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        (heff_w.locals_clock _ _).mono
          (fun i hi _ => Or.inl ⟨i, hshuf1 i hi, le_rfl, le_rfl⟩) (by simp)
      have heff_w3R : R16Shards.WkBlockTxEnc.HeapByteEff sA sB
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] := by
        refine heff_w3.mono (fun i hi _ => ?_) (fun _ hg => hg)
        rcases List.mem_append.1 hi with hrl | hrest
        · exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_left _ hrl), le_rfl, le_rfl⟩
        · rcases List.mem_append.1 hrest with hm24 | hkc
          · exact Or.inl ⟨i, List.mem_append_left _ hm24, le_rfl, le_rfl⟩
          · have hkec_sA : keccakBufIvls sA = keccakBufIvls s := by
              simp only [keccakBufIvls, bufferRegion, hkp_sA, hks_sA]
            rw [hkec_sA] at hkc
            exact Or.inl ⟨i, List.mem_append_right _ (List.mem_append_right _ hkc), le_rfl, le_rfl⟩
      have heff_sB : R16Shards.WkBlockTxEnc.HeapByteEff s sB
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        heff_sA.trans heff_w3R
      have heff_sC : R16Shards.WkBlockTxEnc.HeapByteEff s
          (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB)
          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        heff_sB.locals_clock _ _
      have heff_goal : R16Shards.WkBlockTxEnc.HeapByteEff s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) }          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr"] :=
        heff_sC.locals_clock _ _
      have heff_big : R16Shards.WkBlockTxEnc.HeapByteEff s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) }          (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr", "keccak_pad", "keccak_st"] :=
        heff_goal.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (by simp)
      have heff_cache : R16Shards.WkBlockTxEnc.HeapByteEff s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) }          (nodeCacheIvls Nd ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s))
          ["heap_ptr", "keccak_pad", "keccak_st"] := by
        refine heff_big.mono (fun i hi _ => ?_) (fun _ hg => hg)
        rcases List.mem_append.1 hi with hm24 | hrest
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm24
          exact Or.inl ⟨(m + 8, 24), List.mem_append_left _ (List.mem_map.2 ⟨m, hm, rfl⟩),
            by dsimp; omega, by dsimp; omega⟩
        · exact Or.inl ⟨i, List.mem_append_right _ hrest, le_rfl, le_rfl⟩
      -- NodeHeap/extents via the cache lemma
      have hextra_disj : ∀ e ∈ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s),
          ∀ o ∈ nodeExtents s Nd, Disj e o := by
        intro e he o ho
        rcases List.mem_append.1 he with he | he
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl
          exact hbuf_disj o ho
        · exact keccakBufIvls_disj_of_safe hKS e he o ho
      have hal_any : ∀ n ∈ Nd, ∀ off : Nat, off + 8 ≤ nodeSize (memW s n) →
          Allocated s (n + off, 8) := by
        intro n hn off hlt
        obtain ⟨_, hal_n', _, _, _, _, _, _, _, _⟩ := hN.1 n hn
        unfold Allocated Inside at hal_n' ⊢
        simp only [nodeIvl] at hal_n'
        dsimp only at hal_n' ⊢
        rcases hal_n' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      have hext_mem' : ∀ n ∈ Nd, (n, nodeSize (memW s n)) ∈ nodeExtents s Nd := by
        intro n hn
        simp only [nodeExtents]
        exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
      have disj_sub : ∀ i i' j j' : Ivl, i.1 ≤ i'.1 → i'.1 + i'.2 ≤ i.1 + i.2 →
          j.1 ≤ j'.1 → j'.1 + j'.2 ≤ j.1 + j.2 → Disj i j → Disj i' j' := by
        intro i i' j j' hi1 hi2 hj1 hj2 h
        dsimp [Disj] at h ⊢
        rcases h with h0 | h0 | h1 | h2
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr (by omega)))
      have hdisj_full : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 → off ≠ 24 →
          off + 8 ≤ nodeSize (memW s n) →
          ∀ iv ∈ (Nd.map (fun n => (n + 24, 8)) ++ ([(bufw.toNat, bufLen)] ++ keccakBufIvls s)), 0 < iv.2 → Disj (n + off, 8) iv := by
        intro n hn off h8 h24 hlt iv hiv hpos
        have hsz := nodeSize_ge32 (memW s n)
        rcases List.mem_append.1 hiv with hiv | hiv
        · obtain ⟨n', hn', rfl⟩ := List.mem_map.1 hiv
          by_cases hnn : n' = n
          · subst hnn
            dsimp only [Disj]
            rcases Nat.lt_or_ge off 24 with h | h
            · exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inr (Or.inr (Or.inr (by omega)))
          · have hsz' := nodeSize_ge32 (memW s n')
            exact disj_sub (n, nodeSize (memW s n)) (n + off, 8)
              (n', nodeSize (memW s n')) (n' + 24, 8) (by omega) (by omega) (by omega) (by omega)
              (hN.2 n hn n' hn' (Ne.symm hnn))
        · rcases List.mem_append.1 hiv with hiv | hiv
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
            rcases hiv with rfl
            exact disj_sub (n, nodeSize (memW s n)) (n + off, 8)
              (bufw.toNat, bufLen) (bufw.toNat, bufLen) (by omega) (by omega) (by omega) (by omega)
              (disj_comm (hbuf_disj _ (hext_mem' n hn)))
          · exact disj_sub (n, nodeSize (memW s n)) (n + off, 8) iv iv (by omega) (by omega) (by omega) (by omega)
              (disj_comm (keccakBufIvls_disj_of_safe hKS iv hiv _ (hext_mem' n hn)))
      have hrlp_post : ∀ n ∈ Nd, memW
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } (n + 16) < 2 ^ 40 := by
        intro n hn
        have h8n : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
        have hsz := nodeSize_ge32 (memW s n)
        have hlt : n + 16 < 2 ^ 64 := by
          have h2 := (hN.1 n hn).2.2.1.2
          simp only [Inside, nodeIvl] at h2
          have := hlim
          omega
        have hmem16 : memW
            { ({setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                locals := HolFiniteMapExact.resVarEq
                  (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                  (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } (n + 16) =
            memW s (n + 16) :=
          memW_eq_of_heapByteEff_disj hAR heff_goal (by omega) (hal_any n hn 16 (by omega))
            (by omega) (hdisj_full n hn 16 (by omega) (by decide) (by omega))
        rw [hmem16]
        exact (hN.1 n hn).2.2.2.2.2.2.2.1
      obtain ⟨hNH_post, hext_post⟩ :=
        nodeHeap_of_heapByteEff_cache hAR hN heff_cache hextra_disj hrlp_post
      have hag_post : AllocatorGrows s
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } :=        ⟨heff_big.hp_le, heff_big.sp_le⟩
      have hkp_eq : globN
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } "keccak_pad" =          globN s "keccak_pad" := by
        unfold globN
        rw [← heff_goal.globals (ofString "keccak_pad") (by decide)]
      have hks_eq : globN
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } "keccak_st" =          globN s "keccak_st" := by
        unfold globN
        rw [← heff_goal.globals (ofString "keccak_st") (by decide)]
      have hKS_post : KeccakBufsSafe
          { ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
              locals := HolFiniteMapExact.resVarEq
                (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                (ofString "w3", sA.locals.lookup (ofString "w3")) }) with
            locals := HolFiniteMapExact.resVarEq
              ({ setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB with
                 locals := HolFiniteMapExact.resVarEq
                   (setVarHOLFinite (ofString "off") (.val (.word ((offw + wl) + w3v))) sB).locals
                   (ofString "w3", sA.locals.lookup (ofString "w3")) }).locals
              (ofString "w", s.locals.lookup (ofString "w")) } Nd :=        keccakBufsSafe_of_grows hKS hag_post
          (fun gs hgs => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
            rcases hgs with rfl | rfl
            · simp [bufferRegion, hkp_eq]
            · simp [bufferRegion, hks_eq])
        hext_post
      have hpost_loc : ∀ nm : String, (ofString nm) ≠ (ofString "w") →
          (ofString nm) ≠ (ofString "w3") →
          (ofString "off") ≠ (ofString nm) → (ofString "w3") ≠ (ofString nm) →
          (evaluateHOLFiniteState s finDispatch).2.locals.lookup (ofString nm) =
            s.locals.lookup (ofString nm) := by
        intro nm h1 h2 h3 h4
        rw [hpost]
        dsimp only
        rw [resVarEq_lookup_ne _ _ _ _ h1, resVarEq_lookup_ne _ _ _ _ h2]
        simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by intro hcon; exact h3 (beq_iff_eq.mp hcon))]
        rw [hsB_lc]
        simp only [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by intro hcon; exact h4 (beq_iff_eq.mp hcon))]
        exact hA_loc nm h3 (Ne.symm h1)
      refine ⟨(offw + wl) + w3v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hkmem]
        rw [if_neg (show ¬((2 : Nat) = 1) by decide),
          if_pos (show ((2 : Nat) = 2) by decide)]
        rw [BitVec.toNat_add, BitVec.toNat_add, hwl, hw3, ← hv48s, hndb]
        have hfit := hfit2'
        omega
      · rw [BitVec.toNat_add, BitVec.toNat_add]
        have h1 := offw.isLt
        have h2 := wl.isLt
        have h3 := w3v.isLt
        rw [hwl, hw3, hndb]
        have hfit := hfit2'
        have hbl := hbuf_lim
        rw [heapLimit_val] at hbl
        omega
      · rw [hpost, List.append_assoc]; exact heff_goal
      · rw [hpost]; exact heff_goal.hp_le
      · rw [hpost]; exact hNH_post
      · rw [hpost]; exact hext_post
      · rw [hpost]; exact hKS_post
      · intro n hn off h8 hlt h24
        have h8n : n % 8 = 0 := (hN.1 n hn).2.2.2.1.1
        have hsz := nodeSize_ge32 (memW s n)
        have hlt64 : n + off < 2 ^ 64 := by
          have h2 := (hN.1 n hn).2.2.1.2
          simp only [Inside, nodeIvl] at h2
          have := hlim
          omega
        rw [hpost]
        exact memW_eq_of_heapByteEff_disj hAR heff_goal (by omega) (hal_any n hn off hlt)
          hlt64 (hdisj_full n hn off h8 h24 hlt)
      · exact (hpost_loc "node" (by decide) (by decide) (by decide) (by decide)).trans hln
      · exact (hpost_loc "fr" (by decide) (by decide) (by decide) (by decide)).trans hlf
      · exact (hpost_loc "k" (by decide) (by decide) (by decide) (by decide)).trans hlk
      · exact (hpost_loc "payload" (by decide) (by decide) (by decide) (by decide)).trans hlp
      · exact (hpost_loc "cbuf" (by decide) (by decide) (by decide) (by decide)).trans hlcb
      · exact (hpost_loc "clen" (by decide) (by decide) (by decide) (by decide)).trans hlcl
      · exact (hpost_loc "buf" (by decide) (by decide) (by decide) (by decide)).trans hlb
      · rw [hpost]
        dsimp only
        rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
        simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_pos (by decide)]
      · exact (hpost_loc "hl" (by decide) (by decide) (by decide) (by decide)).trans hhl
      · exact absurd hite_none hright.1

private theorem eval_finRest_returned {F : Type}
    (sp0 : Nat) (st : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (nodew frw kw payv cbufw clenw : BitVec 64) (rv : ValueHOL 64)
    (hc : st.code = originalRuntimeCode)
    (hAR : ArenaReady st) (hN : NodeHeap st Nd) (hKS : KeccakBufsSafe st Nd)
    (hvs : NodeValuesSafe sp0 st Nd)
    (hsp_le_sp0 : globN st "scratch_ptr" ≤ sp0)
    (hnode_in : nodew.toNat ∈ Nd)
    (hk123 : 1 ≤ memW st nodew.toNat ∧ memW st nodew.toNat ≤ 3)
    (hkw_nat : kw.toNat = memW st nodew.toNat)
    (hpay_pos : 1 ≤ payv.toNat)
    (hpay_lt : payv.toNat < 2 ^ 42)
    (hpay_eq_write : payv.toNat = finishWriteLen st frw.toNat nodew.toNat)
    (hcb_eq : cbufw.toNat = memW st (frw.toNat + 24))
    (hcl_eq : clenw.toNat = memW st (frw.toNat + 32))
    (hclen60 : (memW st nodew.toNat = 1 ∨ memW st nodew.toNat = 2) → clenw.toNat < 2 ^ 60)
    (hcb_in : (memW st nodew.toNat = 1 ∨ memW st nodew.toNat = 2) →
      1 ≤ clenw.toNat ∧ Inside (cbufw.toNat, clenw.toNat) sourceBase (globN st "heap_ptr"))
    (hdom1 : memW st nodew.toNat = 1 → 0 < memW st (nodew.toNat + 56) →
      st.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW st (nodew.toNat + 48)))))
    (hdom3 : memW st nodew.toNat = 3 → 0 < memW st (nodew.toNat + 168) →
      st.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW st (nodew.toNat + 160)))))
    (hln : st.locals.lookup (ofString "node") = some (.val (.word nodew)))
    (hlf : st.locals.lookup (ofString "fr") = some (.val (.word frw)))
    (hlk : st.locals.lookup (ofString "k") = some (.val (.word kw)))
    (hlp : st.locals.lookup (ofString "payload") = some (.val (.word payv)))
    (hlcb : st.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)))
    (hlcl : st.locals.lookup (ofString "clen") = some (.val (.word clenw)))
    (hret : (evaluateHOLFiniteState st finRest).1 = some (.returned rv)) :
    let post := (evaluateHOLFiniteState st finRest).2
    rv = .val (.word 0) ∧
    ∃ (hlBv offF : BitVec 64),
      hlBv.toNat = rlpHeaderLenPure payv.toNat ∧
      1 ≤ hlBv.toNat ∧ hlBv.toNat ≤ 9 ∧
      offF.toNat = hlBv.toNat + payv.toNat ∧
      globN st "heap_ptr" + (hlBv.toNat + payv.toNat) ≤ heapLimit ∧
      (∀ o ∈ nodeExtents st Nd, Disj (globN st "heap_ptr", hlBv.toNat + payv.toNat) o) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff st post
        ((globN st "heap_ptr", hlBv.toNat + payv.toNat) ::
          (nodeCacheIvls Nd ++ keccakBufIvls st)) ["heap_ptr"] ∧
      globN st "heap_ptr" < globN post "heap_ptr" ∧
      NodeHeap post Nd ∧
      nodeExtents post Nd = nodeExtents st Nd ∧
      KeccakBufsSafe post Nd ∧
      memW post (nodew.toNat + 8) = globN st "heap_ptr" ∧
      memW post (nodew.toNat + 16) = offF.toNat ∧
      (∀ n ∈ Nd, n ≠ nodew.toNat → memW post (n + 8) = memW st (n + 8) ∧
        memW post (n + 16) = memW st (n + 16)) ∧
      (∀ n ∈ Nd, memW post n = memW st n ∧
        (1 ≤ memW st n → memW post (n + 40) = memW st (n + 40)) ∧
        (memW st n = 1 → memW post (n + 48) = memW st (n + 48) ∧
          memW post (n + 56) = memW st (n + 56))) := by
  intro post; dsimp only [post]
  rw [finRest] at hret ⊢
  obtain ⟨hlBv, s1, hhl_eq, hhl1, hhl9, hs1_g, hs1_m, hs1_be, hs1_ma, hs1_l,
    heff1, hnt1, hdc1⟩ :=
    eval_decCall_rlp_list_header_len_exact' st "hl" (.var .local (ofString "payload"))
      payv finHlCont [] ["heap_ptr"] hc hAR
      (by simp [evalHOLExact, hlp]) (Or.inr ⟨rv, hret⟩)
  rw [hdc1] at hret ⊢
  dsimp only at hret ⊢
  have hs1_AR : ArenaReady s1 := heff1.arena
  have hs1_c : s1.code = originalRuntimeCode := hs1_AR.1.code
  have hs1_ln : s1.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
    rw [hs1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hln,
      show ofString "hl" ≠ ofString "node" by decide]
  have hs1_lf : s1.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    rw [hs1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlf,
      show ofString "hl" ≠ ofString "fr" by decide]
  have hs1_lk : s1.locals.lookup (ofString "k") = some (.val (.word kw)) := by
    rw [hs1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlk,
      show ofString "hl" ≠ ofString "k" by decide]
  have hs1_lp : s1.locals.lookup (ofString "payload") = some (.val (.word payv)) := by
    rw [hs1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlp,
      show ofString "hl" ≠ ofString "payload" by decide]
  have hs1_lcb : s1.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
    rw [hs1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlcb,
      show ofString "hl" ≠ ofString "cbuf" by decide]
  have hs1_lcl : s1.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
    rw [hs1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlcl,
      show ofString "hl" ≠ ofString "clen" by decide]
  have hs1_lhl : s1.locals.lookup (ofString "hl") = some (.val (.word hlBv)) := by
    rw [hs1_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hsum_nat : (hlBv + payv).toNat = hlBv.toNat + payv.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [finHlCont] at hret ⊢
  obtain ⟨bufw, q, s2, hbuf_eq, hbuf8, hq_eq, hbuf_le_q, hq_lim, hs2_hp,
    hs2_g, hs2_m, hs2_be, hs2_l, heff2, hnt2, hdc2⟩ :=
    eval_decCall_alloc_exact' s1 "buf"
      (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")])
      (hlBv + payv) finAllocCont [] ["heap_ptr"] hs1_c hs1_AR (List.Mem.head _)
      (by simp [evalHOLExact, evalListHOLExact, hs1_lhl, hs1_lp,
        wordOpHOL, wordOp, valueIsWord, valueWord])
      (Or.inr ⟨rv, hret⟩)
  rw [hdc2] at hret ⊢
  dsimp only at hret ⊢
  have hs1_hp : globN s1 "heap_ptr" = globN st "heap_ptr" := by simp [globN, hs1_g]
  have hbuf_st : bufw.toNat = globN st "heap_ptr" := hbuf_eq.trans hs1_hp
  set bufLen := hlBv.toNat + payv.toNat
  have hbuf_lim : bufw.toNat + bufLen ≤ heapLimit := by
    rw [hbuf_eq]; rw [hsum_nat] at hbuf_le_q; exact hbuf_le_q.trans hq_lim
  have htot40 : bufLen < 2 ^ 40 := by
    have hlim40 : heapLimit < 2 ^ 40 := by decide
    omega
  have hbuf_disj : ∀ o ∈ nodeExtents st Nd, Disj (globN st "heap_ptr", bufLen) o := by
    intro o ho
    by_cases hz : o.2 = 0
    · exact Or.inr (Or.inl hz)
    · rcases nodeExtents_allocated st Nd hN o ho hz with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · exact Or.inr (Or.inr (Or.inr (by dsimp only at hhi ⊢; omega)))
      · have hss : heapLimit ≤ scratchStart := by decide
        have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
        exact Or.inr (Or.inr (Or.inl (by dsimp only at hlo ⊢; omega)))
  have hs2_AR : ArenaReady s2 := heff2.arena
  have hs2_c : s2.code = originalRuntimeCode := hs2_AR.1.code
  have hs2_ln : s2.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
    rw [hs2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_ln,
      show ofString "buf" ≠ ofString "node" by decide]
  have hs2_lf : s2.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    rw [hs2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_lf,
      show ofString "buf" ≠ ofString "fr" by decide]
  have hs2_lk : s2.locals.lookup (ofString "k") = some (.val (.word kw)) := by
    rw [hs2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_lk,
      show ofString "buf" ≠ ofString "k" by decide]
  have hs2_lp : s2.locals.lookup (ofString "payload") = some (.val (.word payv)) := by
    rw [hs2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_lp,
      show ofString "buf" ≠ ofString "payload" by decide]
  have hs2_lcb : s2.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
    rw [hs2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_lcb,
      show ofString "buf" ≠ ofString "cbuf" by decide]
  have hs2_lcl : s2.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
    rw [hs2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_lcl,
      show ofString "buf" ≠ ofString "clen" by decide]
  have hs2_lhl : s2.locals.lookup (ofString "hl") = some (.val (.word hlBv)) := by
    rw [hs2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_lhl,
      show ofString "buf" ≠ ofString "hl" by decide]
  have hs2_lb : s2.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
    rw [hs2_l]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  -- Evaluate finAllocCont = .seq (rlp_encode_list_header(buf, payload)) finCallCont
  rw [finAllocCont, evaluateHOLFiniteState_seq_line780] at hret ⊢
  rcases hhdr : evaluateHOLFiniteState s2
      (.call (some (none, none)) (ofString "rlp_encode_list_header")
        [.var .local (ofString "buf"), .var .local (ofString "payload")]) with ⟨rhdr, s3⟩
  simp only [hhdr] at hret ⊢
  have hhdr_none : rhdr = none := by
    cases rhdr with
    | none => rfl
    | some o =>
      cases o with
      | returned vr =>
        exfalso
        refine bareCall_ne_returned s2 (.var .local (ofString "buf"))
          (.var .local (ofString "payload")) vr ⟨[.val (.word bufw), .val (.word payv)],
            sourceFnBody Guest.Software.guestFn_rlp_encode_list_header,
            (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word bufw))).update
              (ofString "payload_len", ValueHOL.val (.word payv)),
            .one, ?_, ?_⟩ (by rw [hhdr])
        · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs2_lb, hs2_lp]
        · exact pan_two_word_lookup s2.code.lookup (ofString "rlp_encode_list_header")
            (ofString "dst") (ofString "payload_len")
            (sourceFnBody Guest.Software.guestFn_rlp_encode_list_header) bufw payv
            (by decide) (by rw [hs2_c]; exact WkBlockTxEnc.lookup_rlp_encode_list_header)
      | _ => simp at hret
  subst hhdr_none
  dsimp only at hret ⊢
  obtain ⟨s3', hs3_ev, hs3_l, hs3_g, hs3_be, hs3_ma, heff3_bre⟩ :=
    eval_call_none_rlp_encode_list_header s2
      (.var .local (ofString "buf")) (.var .local (ofString "payload"))
      bufw payv [(bufw.toNat, bufLen)] hs2_c hs2_AR
      (by simp [evalHOLExact, hs2_lb]) (by simp [evalHOLExact, hs2_lp])
      ⟨(bufw.toNat, bufLen), List.Mem.head _, le_rfl, by dsimp [bufLen]; omega⟩
      (by rw [hhdr])
  rw [hhdr] at hs3_ev
  injection hs3_ev with _ hs3_eq
  subst hs3_eq
  have heff3 : R16Shards.WkBlockTxEnc.HeapByteEff s2 s3 [(bufw.toNat, bufLen)] ["heap_ptr"] :=
    R16Shards.WkBlockTxEnc.HeapByteEff.of_m11_bre hs2_AR heff3_bre
  -- Unfold finCallCont = .dec "off" .one (.var .local "hl") finWrite
  rw [finCallCont, evaluateHOLFiniteState_dec_total] at hret ⊢
  have hs3_lhl : s3.locals.lookup (ofString "hl") = some (.val (.word hlBv)) := by
    rw [hs3_l]; exact hs2_lhl
  have hev_hl : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.var .local (ofString "hl")) = some (.val (.word hlBv)) := by
    simp [evalHOLExact, hs3_lhl]
  have hsh_hl : shapeEqHOL .one (shapeOfHOLExact (.val (.word hlBv) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hret ⊢
  rw [hev_hl] at hret ⊢; dsimp only at hret ⊢
  rw [if_pos hsh_hl] at hret ⊢
  set s4 := setVarHOLFinite (ofString "off") (.val (.word hlBv)) s3
  have heff_st_s4 : R16Shards.WkBlockTxEnc.HeapByteEff st s4 [(bufw.toNat, bufLen)] ["heap_ptr"] := by
    have h12 : R16Shards.WkBlockTxEnc.HeapByteEff st s2 [(bufw.toNat, bufLen)] ["heap_ptr"] :=
      (heff1.trans heff2).mono (fun _ h => by simp at h) (fun _ h => h)
    exact (h12.trans heff3).locals_clock s4.locals s4.clock
  have hs4_AR : ArenaReady s4 := heff_st_s4.arena
  have hs4_c : s4.code = originalRuntimeCode := hs4_AR.1.code
  have hbuf_disj' : ∀ e ∈ ([(bufw.toNat, bufLen)] : List Ivl), 0 < e.2 →
      ∀ o ∈ nodeExtents st Nd, Disj e o := by
    intro e he _ o ho
    simp only [List.mem_singleton] at he; subst he
    rw [hbuf_st]; exact hbuf_disj o ho
  obtain ⟨hs4_N, hs4_ext⟩ :=
    nodeHeap_of_heapByteEff_disj hAR hN heff_st_s4 hbuf_disj'
  have hs4_kc_eq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion s4 gs = bufferRegion st gs := by
    intro gs hgs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl
    · unfold bufferRegion globN
      rw [← heff_st_s4.globals (ofString "keccak_pad") (by decide)]
    · unfold bufferRegion globN
      rw [← heff_st_s4.globals (ofString "keccak_st") (by decide)]
  have hs4_kcIvls : keccakBufIvls s4 = keccakBufIvls st := by
    simp only [keccakBufIvls, hs4_kc_eq ("keccak_pad", 136) (by decide),
      hs4_kc_eq ("keccak_st", 200) (by decide)]
  have hs4_KS : KeccakBufsSafe s4 Nd :=
    keccakBufsSafe_of_grows hKS ⟨heff_st_s4.hp_le, heff_st_s4.sp_le⟩ hs4_kc_eq hs4_ext
  have hs4_nd_w : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 → off + 8 ≤ nodeSize (memW st n) →
      memW s4 (n + off) = memW st (n + off) := by
    intro n hn off hoff8 hoff_lt
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
    have hn8 : n % 8 = 0 := hw_n.1
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    have hal_off : Allocated st (n + off, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    have ha_lt : n + off < 2 ^ 64 := by have := hin_n.2; dsimp [nodeIvl] at this; omega
    apply memW_eq_of_heapByteEff_disj hAR heff_st_s4 (by omega) hal_off ha_lt
    intro iv hiv _
    simp only [List.mem_singleton] at hiv; subst hiv
    have ho_mem : nodeIvl st n ∈ nodeExtents st Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
    have hdj := hbuf_disj (nodeIvl st n) ho_mem
    rw [← hbuf_st] at hdj
    dsimp [Disj, nodeIvl] at hdj ⊢
    rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
  have hs4_k : memW s4 nodew.toNat = memW st nodew.toNat := by
    have hsz := nodeSize_ge32 (memW st nodew.toNat)
    simpa using hs4_nd_w nodew.toNat hnode_in 0 (by decide) (by omega)
  have hs4_ln : s4.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_l, hs2_ln,
      show ofString "off" ≠ ofString "node" by decide]
  have hs4_lf : s4.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_l, hs2_lf,
      show ofString "off" ≠ ofString "fr" by decide]
  have hs4_lk : s4.locals.lookup (ofString "k") = some (.val (.word kw)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_l, hs2_lk,
      show ofString "off" ≠ ofString "k" by decide]
  have hs4_lp : s4.locals.lookup (ofString "payload") = some (.val (.word payv)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_l, hs2_lp,
      show ofString "off" ≠ ofString "payload" by decide]
  have hs4_lcb : s4.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_l, hs2_lcb,
      show ofString "off" ≠ ofString "cbuf" by decide]
  have hs4_lcl : s4.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_l, hs2_lcl,
      show ofString "off" ≠ ofString "clen" by decide]
  have hs4_lb : s4.locals.lookup (ofString "buf") = some (.val (.word bufw)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_l, hs2_lb,
      show ofString "off" ≠ ofString "buf" by decide]
  have hs4_lo : s4.locals.lookup (ofString "off") = some (.val (.word hlBv)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs4_lhl : s4.locals.lookup (ofString "hl") = some (.val (.word hlBv)) := by
    simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_l, hs2_lhl,
      show ofString "off" ≠ ofString "hl" by decide]
  -- Preserve cbuf first byte (when k = 1 or 2) and value bytes across st -> s4
  have hs4_cb_b : (memW st nodew.toNat = 1 ∨ memW st nodew.toNat = 2) →
      memB s4 cbufw.toNat = memB st cbufw.toNat := by
    intro hk12
    obtain ⟨hcl1, hcb_lo, hcb_hi⟩ := hcb_in hk12
    dsimp only at hcb_lo hcb_hi
    have hlt64 : cbufw.toNat < 2 ^ 64 := cbufw.isLt
    by_contra hne
    rcases heff_st_s4.byte_frame cbufw.toNat hlt64 hne with
      ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
    · simp only [List.mem_singleton] at hiv; subst hiv
      rw [hbuf_st] at hb1; omega
    · have := hAR.2.2.2.1; have : heapLimit ≤ scratchStart := by decide
      dsimp [freeGap] at hfg1 hfg2; omega
    · dsimp [heapFree] at hhf1 hhf2; omega
  have hs4_nrb : ∀ m, RootIn Nd m → nodeRefBytes s4 m = nodeRefBytes st m := by
    intro m hm
    unfold nodeRefBytes
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hm_nd : m ∈ Nd := by
        rcases hm with h | h
        · exact absurd h hm0
        · exact h
      have hsz_m := nodeSize_ge32 (memW st m)
      have hw0 : memW s4 m = memW st m := by
        simpa using hs4_nd_w m hm_nd 0 (by decide) (by omega)
      have hw16 : memW s4 (m + 16) = memW st (m + 16) :=
        hs4_nd_w m hm_nd 16 (by decide) (by omega)
      simp [hm0, hw0, hw16]
  have hs4_val1_no : memW s4 nodew.toNat = 1 → memW s4 (nodew.toNat + 56) = 1 →
      ¬ InIvl (memW s4 (nodew.toNat + 48)) (bufw.toNat, bufLen) ∧
      (∀ iv ∈ keccakBufIvls s4, ¬ InIvl (memW s4 (nodew.toNat + 48)) iv) ∧
      ¬ InIvl (memW s4 (nodew.toNat + 48)) (freeGap s4) ∧
      ¬ InIvl (memW s4 (nodew.toNat + 48)) (heapFree s4) := by
    intro hk1_s4 hv1_s4
    have hk1 : memW st nodew.toNat = 1 := hs4_k ▸ hk1_s4
    have hns64 : nodeSize (memW st nodew.toNat) = 64 := by rw [hk1]; decide
    have hw48 := hs4_nd_w nodew.toNat hnode_in 48 (by decide) (by omega)
    have hw56 := hs4_nd_w nodew.toNat hnode_in 56 (by decide) (by omega)
    rw [hw48]
    have hv1 : memW st (nodew.toNat + 56) = 1 := hw56 ▸ hv1_s4
    have hdom_ord : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW st (nodew.toNat + 48)))) := by
      rw [← hAR.1.memaddrs]; exact hdom1 hk1 (by omega)
    obtain ⟨_, hkc_no, hfg_no, hhf_no⟩ := (hvs nodew.toNat hnode_in).1 hk1 hv1 hdom_ord
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨h1, h2⟩
      exact hhf_no ⟨by dsimp [heapFree]; rw [← hbuf_st]; exact h1,
        by dsimp [heapFree]; omega⟩
    · intro iv hiv
      rw [hs4_kcIvls] at hiv
      simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl
      · intro hin
        exact hkc_no ("keccak_pad", 136) (by decide) (by dsimp [InIvl] at hin; omega) hin
      · intro hin
        exact hkc_no ("keccak_st", 200) (by decide) (by dsimp [InIvl] at hin; omega) hin
    · intro ⟨h1, h2⟩
      dsimp [freeGap] at h1 h2
      rw [heff_st_s4.fp_eq] at h1 h2
      have hsp4 := heff_st_s4.sp_le
      exact hfg_no ⟨by dsimp [freeGapTo]; omega, by dsimp [freeGapTo]; omega⟩
    · intro ⟨h1, h2⟩
      dsimp [heapFree] at h1 h2
      have hhp4 := heff_st_s4.hp_le
      exact hhf_no ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩
  have hs4_val3_no : memW s4 nodew.toNat = 3 → memW s4 (nodew.toNat + 168) = 1 →
      ¬ InIvl (memW s4 (nodew.toNat + 160)) (bufw.toNat, bufLen) ∧
      (∀ n ∈ Nd, ¬ InIvl (memW s4 (nodew.toNat + 160)) (n + 24, 8)) ∧
      (∀ iv ∈ keccakBufIvls s4, ¬ InIvl (memW s4 (nodew.toNat + 160)) iv) ∧
      ¬ InIvl (memW s4 (nodew.toNat + 160)) (freeGap s4) ∧
      ¬ InIvl (memW s4 (nodew.toNat + 160)) (heapFree s4) := by
    intro hk3_s4 hv1_s4
    have hk3 : memW st nodew.toNat = 3 := hs4_k ▸ hk3_s4
    have hns176 : nodeSize (memW st nodew.toNat) = 176 := by rw [hk3]; decide
    have hw160 := hs4_nd_w nodew.toNat hnode_in 160 (by decide) (by omega)
    have hw168 := hs4_nd_w nodew.toNat hnode_in 168 (by decide) (by omega)
    rw [hw160]
    have hv1 : memW st (nodew.toNat + 168) = 1 := hw168 ▸ hv1_s4
    have hdom_ord : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW st (nodew.toNat + 160)))) := by
      rw [← hAR.1.memaddrs]; exact hdom3 hk3 (by omega)
    obtain ⟨hnc_no, hkc_no, hfg_no, hhf_no⟩ := (hvs nodew.toNat hnode_in).2 hk3 hv1 hdom_ord
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro ⟨h1, h2⟩
      exact hhf_no ⟨by dsimp [heapFree]; rw [← hbuf_st]; exact h1,
        by dsimp [heapFree]; omega⟩
    · intro n hn ⟨h1, h2⟩
      exact hnc_no n hn ⟨by dsimp at h1 ⊢; omega, by dsimp at h2 ⊢; omega⟩
    · intro iv hiv
      rw [hs4_kcIvls] at hiv
      simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl
      · intro hin
        exact hkc_no ("keccak_pad", 136) (by decide) (by dsimp [InIvl] at hin; omega) hin
      · intro hin
        exact hkc_no ("keccak_st", 200) (by decide) (by dsimp [InIvl] at hin; omega) hin
    · intro ⟨h1, h2⟩
      dsimp [freeGap] at h1 h2
      rw [heff_st_s4.fp_eq] at h1 h2
      have hsp4 := heff_st_s4.sp_le
      exact hfg_no ⟨by dsimp [freeGapTo]; omega, by dsimp [freeGapTo]; omega⟩
    · intro ⟨h1, h2⟩
      dsimp [heapFree] at h1 h2
      have hhp4 := heff_st_s4.hp_le
      exact hhf_no ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩
  have hs4_rlp_val1 : memW st nodew.toNat = 1 →
      rlpBytesLenPure
        (if 0 < memW s4 (nodew.toNat + 56) then memB s4 (memW s4 (nodew.toNat + 48)) else 0)
        (memW s4 (nodew.toNat + 56)) =
      rlpBytesLenPure
        (if 0 < memW st (nodew.toNat + 56) then memB st (memW st (nodew.toNat + 48)) else 0)
        (memW st (nodew.toNat + 56)) := by
    intro hk1
    have hns64 : nodeSize (memW st nodew.toNat) = 64 := by rw [hk1]; decide
    have hw48 := hs4_nd_w nodew.toNat hnode_in 48 (by decide) (by omega)
    have hw56 := hs4_nd_w nodew.toNat hnode_in 56 (by decide) (by omega)
    rw [hw48, hw56]
    by_cases hv1 : memW st (nodew.toNat + 56) = 1
    · have hdom_ord : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW st (nodew.toNat + 48)))) := by
        rw [← hAR.1.memaddrs]; exact hdom1 hk1 (by omega)
      obtain ⟨_, _, hfg_no, hhf_no⟩ := (hvs nodew.toNat hnode_in).1 hk1 hv1 hdom_ord
      have hlt64 := memW_lt_two_pow_64 st (nodew.toNat + 48)
      have hmb : memB s4 (memW st (nodew.toNat + 48)) = memB st (memW st (nodew.toNat + 48)) := by
        by_contra hne
        rcases heff_st_s4.byte_frame _ hlt64 hne with
          ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
        · simp only [List.mem_singleton] at hiv; subst hiv
          exact hhf_no ⟨by dsimp [heapFree]; rw [← hbuf_st]; exact hb1,
            by dsimp [heapFree]; omega⟩
        · dsimp [freeGap] at hfg1 hfg2
          exact hfg_no ⟨by dsimp [freeGapTo]; omega, by dsimp [freeGapTo]; omega⟩
        · exact hhf_no ⟨hhf1, hhf2⟩
      rw [hmb]
    · exact rlpBytesLenPure_congr_ne_one hv1
  have hs4_rlp_val3 : memW st nodew.toNat = 3 →
      rlpBytesLenPure
        (if 0 < memW s4 (nodew.toNat + 168) then memB s4 (memW s4 (nodew.toNat + 160)) else 0)
        (memW s4 (nodew.toNat + 168)) =
      rlpBytesLenPure
        (if 0 < memW st (nodew.toNat + 168) then memB st (memW st (nodew.toNat + 160)) else 0)
        (memW st (nodew.toNat + 168)) := by
    intro hk3
    have hns176 : nodeSize (memW st nodew.toNat) = 176 := by rw [hk3]; decide
    have hw160 := hs4_nd_w nodew.toNat hnode_in 160 (by decide) (by omega)
    have hw168 := hs4_nd_w nodew.toNat hnode_in 168 (by decide) (by omega)
    rw [hw160, hw168]
    by_cases hv1 : memW st (nodew.toNat + 168) = 1
    · have hdom_ord : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW st (nodew.toNat + 160)))) := by
        rw [← hAR.1.memaddrs]; exact hdom3 hk3 (by omega)
      obtain ⟨_, _, hfg_no, hhf_no⟩ := (hvs nodew.toNat hnode_in).2 hk3 hv1 hdom_ord
      have hlt64 := memW_lt_two_pow_64 st (nodew.toNat + 160)
      have hmb : memB s4 (memW st (nodew.toNat + 160)) = memB st (memW st (nodew.toNat + 160)) := by
        by_contra hne
        rcases heff_st_s4.byte_frame _ hlt64 hne with
          ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
        · simp only [List.mem_singleton] at hiv; subst hiv
          exact hhf_no ⟨by dsimp [heapFree]; rw [← hbuf_st]; exact hb1,
            by dsimp [heapFree]; omega⟩
        · dsimp [freeGap] at hfg1 hfg2
          exact hfg_no ⟨by dsimp [freeGapTo]; omega, by dsimp [freeGapTo]; omega⟩
        · exact hhf_no ⟨hhf1, hhf2⟩
      rw [hmb]
    · exact rlpBytesLenPure_congr_ne_one hv1
  have hs4_br_eq : memW st nodew.toNat = 3 →
      branchRefsLenSum s4 nodew.toNat 16 = branchRefsLenSum st nodew.toNat 16 := by
    intro hk3
    have hns176 : nodeSize (memW st nodew.toNat) = 176 := by rw [hk3]; decide
    refine branchRefsLenSum_congr ((hN.1 nodew.toNat hnode_in).2.2.2.2.2.1 hk3) ?_ hs4_nrb 16 (le_refl _)
    intro i hi
    have : nodew.toNat + 32 + 8 * i = nodew.toNat + (32 + 8 * i) := by omega
    rw [this]
    exact hs4_nd_w nodew.toNat hnode_in (32 + 8 * i) (by omega) (by omega)
  have hfit1_s4 : memW s4 nodew.toNat = 1 →
      hlBv.toNat + rlpBytesLenPure (memB s4 cbufw.toNat) clenw.toNat +
        rlpBytesLenPure (if 0 < memW s4 (nodew.toNat + 56) then memB s4 (memW s4 (nodew.toNat + 48)) else 0)
          (memW s4 (nodew.toNat + 56)) ≤ bufLen := by
    intro hk1_s4
    have hk1 : memW st nodew.toNat = 1 := hs4_k ▸ hk1_s4
    rw [hs4_cb_b (Or.inl hk1), hs4_rlp_val1 hk1, hcb_eq, hcl_eq]
    have hp1 : payv.toNat = rlpBytesLenPure (memB st (memW st (frw.toNat + 24))) (memW st (frw.toNat + 32)) +
        rlpBytesLenPure (if 0 < memW st (nodew.toNat + 56) then memB st (memW st (nodew.toNat + 48)) else 0)
          (memW st (nodew.toNat + 56)) := by
      rw [hpay_eq_write]; simp [finishWriteLen, hk1]
    dsimp [bufLen]; omega
  have hfit2_s4 : memW s4 nodew.toNat = 2 →
      hlBv.toNat + rlpBytesLenPure (memB s4 cbufw.toNat) clenw.toNat +
        nodeRefBytes s4 (memW s4 (nodew.toNat + 48)) ≤ bufLen := by
    intro hk2_s4
    have hk2 : memW st nodew.toNat = 2 := hs4_k ▸ hk2_s4
    have hns56 : nodeSize (memW st nodew.toNat) = 56 := by rw [hk2]; decide
    have hw48 := hs4_nd_w nodew.toNat hnode_in 48 (by decide) (by omega)
    rw [hs4_cb_b (Or.inr hk2), hw48, hs4_nrb _ ((hN.1 nodew.toNat hnode_in).2.2.2.2.1 hk2),
      hcb_eq, hcl_eq]
    have hp2 : payv.toNat = rlpBytesLenPure (memB st (memW st (frw.toNat + 24))) (memW st (frw.toNat + 32)) +
        nodeRefBytes st (memW st (nodew.toNat + 48)) := by
      rw [hpay_eq_write]; simp [finishWriteLen, hk2]
    dsimp [bufLen]; omega
  have hfit3_s4 : memW s4 nodew.toNat = 3 →
      hlBv.toNat + branchRefsLenSum s4 nodew.toNat 16 +
        rlpBytesLenPure (if 0 < memW s4 (nodew.toNat + 168) then memB s4 (memW s4 (nodew.toNat + 160)) else 0)
          (memW s4 (nodew.toNat + 168)) ≤ bufLen := by
    intro hk3_s4
    have hk3 : memW st nodew.toNat = 3 := hs4_k ▸ hk3_s4
    rw [hs4_br_eq hk3, hs4_rlp_val3 hk3]
    have hp3 : payv.toNat = branchRefsLenSum st nodew.toNat 16 +
        rlpBytesLenPure (if 0 < memW st (nodew.toNat + 168) then memB st (memW st (nodew.toNat + 160)) else 0)
          (memW st (nodew.toNat + 168)) := by
      rw [hpay_eq_write]; simp [finishWriteLen, hk3]
    dsimp [bufLen]; omega
  -- Split finWrite = .seq finDispatch (stores + return 0)
  have hfw_eq : finWrite = .seq finDispatch
      (.seq (.store (.op .add [.var .local (ofString "node"), .const 8])
          (.var .local (ofString "buf")))
        (.seq (.store (.op .add [.var .local (ofString "node"), .const 16])
            (.var .local (ofString "off")))
          (.return (.const 0)))) := rfl
  rw [hfw_eq, evaluateHOLFiniteState_seq_line780] at hret ⊢
  rcases hdisp : evaluateHOLFiniteState s4 finDispatch with ⟨rdisp, sM⟩
  simp only [hdisp] at hret ⊢
  have hrdisp_none : rdisp = none := by
    cases rdisp with
    | none => rfl
    | some o =>
      cases o with
      | returned vr =>
        exact False.elim (evaluate_noReturnLocal finDispatch (by decide) s4 vr (by rw [hdisp]))
      | _ => simp at hret
  subst hrdisp_none
  dsimp only at hret ⊢
  obtain ⟨offF, hoffF_s4, hoffF_lt, heff_disp, hs4_hp_le, hsM_N, hsM_ext, hsM_KS,
    hsM_nd_w, hsM_ln, hsM_lf, hsM_lk, hsM_lp, hsM_lcb, hsM_lcl, hsM_lb, hsM_lo, hsM_lhl⟩ :=
    eval_finWrite_none s4 Nd nodew frw kw payv cbufw clenw hlBv bufw hlBv bufLen
      hs4_c hs4_AR hs4_N hs4_KS hnode_in (hs4_k ▸ hk123) (hkw_nat.trans hs4_k.symm)
      hs4_ln hs4_lf hs4_lk hs4_lp hs4_lcb hs4_lcl hs4_lb hs4_lo hs4_lhl hbuf_lim
      (fun o ho => by rw [hs4_ext] at ho; rw [hbuf_st]; exact hbuf_disj o ho)
      hfit1_s4 hfit2_s4 hfit3_s4 (fun h12 => hclen60 (hs4_k ▸ h12)) hs4_val1_no hs4_val3_no (by rw [hdisp])
  rw [hdisp] at heff_disp hs4_hp_le hsM_N hsM_ext hsM_KS hsM_nd_w
  rw [hdisp] at hsM_ln hsM_lf hsM_lk hsM_lp hsM_lcb hsM_lcl hsM_lb hsM_lo hsM_lhl
  dsimp only at heff_disp hs4_hp_le hsM_N hsM_ext hsM_KS hsM_nd_w
  dsimp only at hsM_ln hsM_lf hsM_lk hsM_lp hsM_lcb hsM_lcl hsM_lb hsM_lo hsM_lhl
  have hoffF_nat : offF.toNat = hlBv.toNat + payv.toNat := by
    rw [hoffF_s4, hs4_k]
    by_cases hk1 : memW st nodew.toNat = 1
    · rw [if_pos hk1, hs4_cb_b (Or.inl hk1), hs4_rlp_val1 hk1, hcb_eq, hcl_eq, hpay_eq_write]
      simp [finishWriteLen, hk1]
    · rw [if_neg hk1]
      by_cases hk2 : memW st nodew.toNat = 2
      · have hns56 : nodeSize (memW st nodew.toNat) = 56 := by rw [hk2]; decide
        have hw48 := hs4_nd_w nodew.toNat hnode_in 48 (by decide) (by omega)
        rw [if_pos hk2, hs4_cb_b (Or.inr hk2), hw48,
          hs4_nrb _ ((hN.1 nodew.toNat hnode_in).2.2.2.2.1 hk2), hcb_eq, hcl_eq, hpay_eq_write]
        simp [finishWriteLen, hk2]
      · have hk3 : memW st nodew.toNat = 3 := by omega
        rw [if_neg hk2, hs4_br_eq hk3, hs4_rlp_val3 hk3, hpay_eq_write]
        simp [finishWriteLen, hk3]
  -- Deduce rv = .val (.word 0) from the two stores + return 0
  have hrv0 : rv = .val (.word 0) := by
    have htail_ev := hret
    rw [evaluateHOLFiniteState_seq_line780] at htail_ev
    rcases hest1 : evaluateHOLFiniteState sM
      (.store (.op .add [.var .local (ofString "node"), .const 8])
        (.var .local (ofString "buf"))) with ⟨ro1, st1⟩
    simp only [hest1] at htail_ev
    cases ro1 with
    | some o =>
      cases o with
      | returned vr =>
        exact False.elim (evaluate_noReturnLocal
          (.store (.op .add [.var .local (ofString "node"), .const 8])
            (.var .local (ofString "buf"))) (by decide) sM vr (by rw [hest1]))
      | _ => simp at htail_ev
    | none =>
      dsimp only at htail_ev
      rw [evaluateHOLFiniteState_seq_line780] at htail_ev
      rcases hest2 : evaluateHOLFiniteState st1
        (.store (.op .add [.var .local (ofString "node"), .const 16])
          (.var .local (ofString "off"))) with ⟨ro2, st2⟩
      simp only [hest2] at htail_ev
      cases ro2 with
      | some o =>
        cases o with
        | returned vr =>
          exact False.elim (evaluate_noReturnLocal
            (.store (.op .add [.var .local (ofString "node"), .const 16])
              (.var .local (ofString "off"))) (by decide) st1 vr (by rw [hest2]))
        | _ => simp at htail_ev
      | none =>
        dsimp only at htail_ev
        rw [evaluateHOLFiniteState_return] at htail_ev
        have hc0 : @evalHOLExact 64 F _ st2.toExact
            (fun a => Classical.propDecidable (st2.memaddrs a)) (.const 0) =
            some (.val (.word 0)) := rfl
        rw [hc0] at htail_ev; dsimp only at htail_ev
        split at htail_ev
        · simp at htail_ev; exact htail_ev.symm
        · simp at htail_ev
  subst hrv0
  have hsM_kc_eq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion sM gs = bufferRegion s4 gs := by
    intro gs hgs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl
    · unfold bufferRegion globN
      rw [← heff_disp.globals (ofString "keccak_pad") (by decide)]
    · unfold bufferRegion globN
      rw [← heff_disp.globals (ofString "keccak_st") (by decide)]
  have hsM_kcIvls : keccakBufIvls sM = keccakBufIvls s4 := by
    simp only [keccakBufIvls, hsM_kc_eq ("keccak_pad", 136) (by decide),
      hsM_kc_eq ("keccak_st", 200) (by decide)]
  have heffB : R16Shards.WkBlockTxEnc.HeapByteEff st sM
      (Nd.map (fun n => (n + 24, 8)) ++
        ([(globN st "heap_ptr", hlBv.toNat + payv.toNat)] ++ keccakBufIvls sM))
      ["heap_ptr"] := by
    have heff_st_s4' : R16Shards.WkBlockTxEnc.HeapByteEff st s4
        (Nd.map (fun n => (n + 24, 8)) ++
          ([(globN st "heap_ptr", hlBv.toNat + payv.toNat)] ++ keccakBufIvls sM))
        ["heap_ptr"] := by
      refine heff_st_s4.mono (fun i hi _ => ?_) (fun _ h => h)
      simp only [List.mem_singleton] at hi; subst hi
      rw [hbuf_st]
      exact Or.inl ⟨(globN st "heap_ptr", bufLen),
        List.mem_append_right _ (List.Mem.head _), le_rfl, le_rfl⟩
    have heff_disp' : R16Shards.WkBlockTxEnc.HeapByteEff s4 sM
        (Nd.map (fun n => (n + 24, 8)) ++
          ([(globN st "heap_ptr", hlBv.toNat + payv.toNat)] ++ keccakBufIvls sM))
        ["heap_ptr"] := by
      refine heff_disp.mono (fun i hi _ => ?_) (fun _ h => h)
      rcases List.mem_append.1 hi with h12 | hkc
      · rcases List.mem_append.1 h12 with hm24 | hbuf_m
        · exact Or.inl ⟨i, List.mem_append_left _ hm24, le_rfl, le_rfl⟩
        · simp only [List.mem_singleton] at hbuf_m; subst hbuf_m
          rw [hbuf_st]
          exact Or.inl ⟨(globN st "heap_ptr", bufLen),
            List.mem_append_right _ (List.Mem.head _), le_rfl, le_rfl⟩
      · rw [← hsM_kcIvls] at hkc
        exact Or.inl ⟨i, List.mem_append_right _ (List.Mem.tail _ hkc), le_rfl, le_rfl⟩
    exact heff_st_s4'.trans heff_disp'
  have hW_M : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 → off + 8 ≤ nodeSize (memW st n) →
      off ≠ 24 → memW sM (n + off) = memW st (n + off) := by
    intro n hn off hoff8 hoff_lt hoff24
    have hsz0 := nodeSize_ge32 (memW st n)
    have hk_eq_n : memW s4 n = memW st n := by
      simpa using hs4_nd_w n hn 0 (by decide) (by omega)
    exact (hsM_nd_w n hn off hoff8 (by rw [hk_eq_n]; exact hoff_lt) hoff24).trans
      (hs4_nd_w n hn off hoff8 hoff_lt)
  have hM_hp : globN st "heap_ptr" < globN sM "heap_ptr" := by
    have hs4_hp_eq : globN s4 "heap_ptr" = q.toNat := by
      have : globN s4 "heap_ptr" = globN s3 "heap_ptr" := rfl
      rw [this]; unfold globN; rw [hs3_g]; exact hs2_hp
    have : globN st "heap_ptr" + (hlBv.toNat + payv.toNat) ≤ q.toNat := by
      rw [← hs1_hp]; change globN s1 "heap_ptr" + bufLen ≤ q.toNat
      rw [← hsum_nat]; exact hbuf_le_q
    omega
  set tailProg : ProgHOL 64 := (.seq (.store (.op .add [.var .local (ofString "node"), .const 8])
          (.var .local (ofString "buf")))
        (.seq (.store (.op .add [.var .local (ofString "node"), .const 16])
            (.var .local (ofString "off")))
          (.return (.const 0))))
  let Lv := HolFiniteMapExact.resVarEq
    (HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState sM tailProg).2.locals
        (ofString "off", s3.locals.lookup (ofString "off")))
      (ofString "buf", s1.locals.lookup (ofString "buf")))
    (ofString "hl", st.locals.lookup (ofString "hl"))
  obtain ⟨offF', hoffF'_nat, heff_fin, hhp_lt, hN_fin, hext_fin, hKS_fin,
    h8_fin, h16_fin, hother_fin, hword_fin⟩ :=
    finRest_tail_close st Nd nodew bufw payv hlBv hhl1 htot40 hAR hN hKS
      hnode_in hbuf_st hbuf_disj sM heffB hW_M hsM_ln hsM_lb
      ⟨offF, hsM_lo, hoffF_nat⟩ hM_hp hret
      { (evaluateHOLFiniteState sM tailProg).2 with locals := Lv } Lv rfl
  refine ⟨rfl, hlBv, offF', hhl_eq, hhl1, hhl9, hoffF'_nat, ?_, hbuf_disj,
    heff_fin, hhp_lt, hN_fin, hext_fin, hKS_fin, h8_fin, h16_fin, hother_fin, hword_fin⟩
  rw [← hbuf_st]; exact hbuf_lim

private theorem eval__node_rlp_finish_returned {F : Type}
    (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (frw nodew : BitVec 64) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (hN : NodeHeap s Nd) (hKS : KeccakBufsSafe s Nd)
    (hvs : NodeValuesSafe sp0 s Nd)
    (hsp_le_sp0 : globN s "scratch_ptr" ≤ sp0)
    (hfr : ValidRlpFrame s Nd frw.toNat)
    (hnode : memW s (frw.toNat + 8) = nodew.toNat)
    (hfr_loc : s.locals.lookup (ofString "fr") = some (.val (.word frw)))
    (hnode_loc : s.locals.lookup (ofString "node") = some (.val (.word nodew)))
    (hret : (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn__node_rlp_finish)).1 = some (.returned rv)) :
    let post := (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn__node_rlp_finish)).2
    rv = .val (.word 0) ∧
    ∃ totLen : Nat,
      1 ≤ totLen ∧
      globN s "heap_ptr" + totLen ≤ heapLimit ∧
      (∀ o ∈ nodeExtents s Nd, Disj (globN s "heap_ptr", totLen) o) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s post
        ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] ∧
      globN s "heap_ptr" < globN post "heap_ptr" ∧
      NodeHeap post Nd ∧
      nodeExtents post Nd = nodeExtents s Nd ∧
      KeccakBufsSafe post Nd ∧
      NodeValuesSafe sp0 post Nd ∧
      memW post (nodew.toNat + 8) = globN s "heap_ptr" ∧
      memW post (nodew.toNat + 16) = totLen ∧
      (∀ n ∈ Nd, n ≠ nodew.toNat → memW post (n + 8) = memW s (n + 8) ∧
        memW post (n + 16) = memW s (n + 16)) ∧
      (∀ n ∈ Nd, memW post n = memW s n ∧
        (1 ≤ memW s n → memW post (n + 40) = memW s (n + 40)) ∧
        (memW s n = 1 → memW post (n + 48) = memW s (n + 48) ∧
          memW post (n + 56) = memW s (n + 56))) := by
  intro post; dsimp only [post]
  obtain ⟨kw, payw, cbufw, clenw, hkw_nat, hpay_nat, hcb_nat, hcl_nat,
    hloads_1, hloads_m, hloads_g, hloads_be, hloads_ma, hloads_c,
    hloads_sh, hloads_ba, hloads_str⟩ :=
    eval__node_rlp_finish_loads s Nd frw nodew hN hfr hnode hfr_loc hnode_loc
  set entry := setVarHOLFinite (ofString "clen") (.val (.word clenw))
    (setVarHOLFinite (ofString "cbuf") (.val (.word cbufw))
      (setVarHOLFinite (ofString "payload") (.val (.word payw))
        (setVarHOLFinite (ofString "k") (.val (.word kw)) s)))
  rw [hloads_1, finishAfterLoads_eq_finLoadsRest, finLoadsRest] at hret
  have hent_AR : ArenaReady entry := localsFree_arenaReady s entry.locals entry.clock hAR
  have hent_c : entry.code = originalRuntimeCode := hc
  have hent_N : NodeHeap entry Nd := hN
  have hent_KS : KeccakBufsSafe entry Nd := hKS
  have hent_ln : entry.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnode_loc,
      show ofString "clen" ≠ ofString "node" by decide,
      show ofString "cbuf" ≠ ofString "node" by decide,
      show ofString "payload" ≠ ofString "node" by decide,
      show ofString "k" ≠ ofString "node" by decide]
  have hent_lf : entry.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hfr_loc,
      show ofString "clen" ≠ ofString "fr" by decide,
      show ofString "cbuf" ≠ ofString "fr" by decide,
      show ofString "payload" ≠ ofString "fr" by decide,
      show ofString "k" ≠ ofString "fr" by decide]
  have hent_lk : entry.locals.lookup (ofString "k") = some (.val (.word kw)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "clen" ≠ ofString "k" by decide,
      show ofString "cbuf" ≠ ofString "k" by decide,
      show ofString "payload" ≠ ofString "k" by decide]
  have hent_lp : entry.locals.lookup (ofString "payload") = some (.val (.word payw)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "clen" ≠ ofString "payload" by decide,
      show ofString "cbuf" ≠ ofString "payload" by decide]
  have hent_lcb : entry.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "clen" ≠ ofString "cbuf" by decide]
  have hent_lcl : entry.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
    simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Step 1: evaluate ite (k == 2)
  set ite2 := ProgHOL.ite (.cmp .equal (.var .local (ofString "k")) (.const 2))
    (.decCall (ofString "rl") .one (ofString "node_ref_len")
      [.load .one (.op .add [.var .local (ofString "node"), .const 48])]
      finishExtLenCont)
    .skip
  set ite3 := ProgHOL.ite (.cmp .equal (.var .local (ofString "k")) (.const 3))
    (.dec (ofString "i") .one (.const 0) finishBranchLenCont)
    .skip
  rw [evaluateHOLFiniteState_seq_line780] at hret
  rcases hev_ite2 : evaluateHOLFiniteState entry ite2 with ⟨r_ite2, sA⟩
  rw [hev_ite2] at hret
  have hrite2_none : r_ite2 = none := by
    cases r_ite2 with
    | none => rfl
    | some o =>
      cases o with
      | returned vr =>
        exact False.elim (evaluate_noReturnLocal ite2 (by decide) entry vr (by rw [hev_ite2]))
      | _ => simp at hret
  subst hrite2_none
  dsimp only at hret
  rw [evaluateHOLFiniteState_seq_line780] at hret
  rcases hev_ite3 : evaluateHOLFiniteState sA ite3 with ⟨r_ite3, st⟩
  rw [hev_ite3] at hret
  have hrite3_none : r_ite3 = none := by
    cases r_ite3 with
    | none => rfl
    | some o =>
      cases o with
      | returned vr =>
        exact False.elim (evaluate_noReturnLocal ite3 (by decide) sA vr (by rw [hev_ite3]))
      | _ => simp at hret
  subst hrite3_none
  dsimp only at hret
  -- Characterize entry -> sA -> st
  have hnode_in : nodew.toNat ∈ Nd := hnode ▸ hfr.2.2.2.1
  have hk123 : 1 ≤ memW s nodew.toNat ∧ memW s nodew.toNat ≤ 3 :=
    ⟨hnode ▸ hfr.2.2.2.2.1, hnode ▸ hfr.2.2.2.2.2.1⟩
  have hcnd2 : @evalHOLExact 64 F _ entry.toExact
      (fun a => Classical.propDecidable (entry.memaddrs a))
      (.cmp .equal (.var .local (ofString "k")) (.const 2)) =
      some (.val (.word (if kw = (2 : BitVec 64) then 1 else 0))) := by
    simp [evalHOLExact, hent_lk, Compiler.Encoders.Asm.wordCmpHOL]
  have hsA_char : ∃ payA : BitVec 64,
      payA.toNat = (if memW s nodew.toNat = 2 then
          memW s (frw.toNat + 40) + nodeRefBytes s (memW s (nodew.toNat + 48))
        else memW s (frw.toNat + 40)) ∧
      sA.globals = s.globals ∧ sA.memory = s.memory ∧ sA.be = s.be ∧
      HeapByteEff entry sA [] ["heap_ptr"] ∧
      sA.locals.lookup (ofString "node") = some (.val (.word nodew)) ∧
      sA.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
      sA.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
      sA.locals.lookup (ofString "payload") = some (.val (.word payA)) ∧
      sA.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) ∧
      sA.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
    have hite2_ev := hev_ite2
    dsimp only [ite2] at hite2_ev
    rw [evaluateHOLFiniteState_ite, hcnd2] at hite2_ev
    dsimp only at hite2_ev
    by_cases hkw2 : kw = (2 : BitVec 64)
    · rw [if_pos hkw2, if_neg (by decide)] at hite2_ev
      have hk2 : memW s nodew.toNat = 2 := by
        have : kw.toNat = 2 := by simp [hkw2]
        omega
      obtain ⟨payA, hpayA_eq, hg, hm, hbe, heffA, hlnA, hlfA, hlkA, hlpA, hlcbA, hlclA⟩ :=
        eval_finishExtLen_none entry Nd nodew frw kw payw cbufw clenw
          hent_c hent_AR hent_N hnode_in hk2
          hent_ln hent_lf hent_lk hent_lp hent_lcb hent_lcl
          (by rw [hpay_nat]; exact hfr.2.2.2.2.2.2.2.1)
          (by rw [hite2_ev])
      rw [hite2_ev] at hg hm hbe heffA hlnA hlfA hlkA hlpA hlcbA hlclA
      dsimp only at hg hm hbe heffA hlnA hlfA hlkA hlpA hlcbA hlclA
      exact ⟨payA, by rw [if_pos hk2, hpayA_eq, hpay_nat]; rfl,
        hg, hm, hbe, heffA, hlnA, hlfA, hlkA, hlpA, hlcbA, hlclA⟩
    · rw [if_neg hkw2] at hite2_ev
      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hite2_ev
      injection hite2_ev with _ hsA_eq
      subst hsA_eq
      have hk_ne2 : memW s nodew.toNat ≠ 2 := by
        intro hk2; apply hkw2; apply BitVec.eq_of_toNat_eq; rw [hkw_nat, hk2]; rfl
      exact ⟨payw, by rw [if_neg hk_ne2, hpay_nat], rfl, rfl, rfl,
        HeapByteEff.refl hent_AR [] ["heap_ptr"],
        hent_ln, hent_lf, hent_lk, hent_lp, hent_lcb, hent_lcl⟩
  obtain ⟨payA, hpayA_nat, hsA_g, hsA_m, hsA_be, heff_sA,
    hsA_ln, hsA_lf, hsA_lk, hsA_lp, hsA_lcb, hsA_lcl⟩ := hsA_char
  have hsA_AR : ArenaReady sA := heff_sA.arena
  have hsA_c : sA.code = originalRuntimeCode := hsA_AR.1.code
  have hsA_N : NodeHeap sA Nd := by
    have hext := nodeHeap_of_heapByteEff_disj hent_AR hent_N heff_sA (fun _ h => by simp at h)
    exact hext.1
  have hsA_memW : memW sA = memW s := by ext a; unfold memW; rw [hsA_m]
  have hsA_memB : memB sA = memB s := by ext a; unfold memB; rw [hsA_m, hsA_be]
  have hcnd3 : @evalHOLExact 64 F _ sA.toExact
      (fun a => Classical.propDecidable (sA.memaddrs a))
      (.cmp .equal (.var .local (ofString "k")) (.const 3)) =
      some (.val (.word (if kw = (3 : BitVec 64) then 1 else 0))) := by
    simp [evalHOLExact, hsA_lk, Compiler.Encoders.Asm.wordCmpHOL]
  have hst_char : ∃ payv : BitVec 64,
      payv.toNat = finishPayloadLen s frw.toNat nodew.toNat ∧
      (memW s nodew.toNat = 3 → 0 < memW s (nodew.toNat + 168) →
        s.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW s (nodew.toNat + 160))))) ∧
      st.globals = s.globals ∧ st.memory = s.memory ∧ st.be = s.be ∧
      HeapByteEff entry st [] ["heap_ptr"] ∧
      st.locals.lookup (ofString "node") = some (.val (.word nodew)) ∧
      st.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
      st.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
      st.locals.lookup (ofString "payload") = some (.val (.word payv)) ∧
      st.locals.lookup (ofString "cbuf") = some (.val (.word cbufw)) ∧
      st.locals.lookup (ofString "clen") = some (.val (.word clenw)) := by
    have hite3_ev := hev_ite3
    dsimp only [ite3] at hite3_ev
    rw [evaluateHOLFiniteState_ite, hcnd3] at hite3_ev
    dsimp only at hite3_ev
    by_cases hkw3 : kw = (3 : BitVec 64)
    · rw [if_pos hkw3, if_neg (by decide)] at hite3_ev
      have hk3 : memW s nodew.toNat = 3 := by
        have : kw.toNat = 3 := by simp [hkw3]
        omega
      have hk3_ne2 : memW s nodew.toNat ≠ 2 := by omega
      have hpayA0 : payA.toNat = 0 := by
        rw [hpayA_nat, if_neg hk3_ne2]
        exact hfr.2.2.2.2.2.2.2.2.1 (hnode.symm ▸ hk3)
      obtain ⟨payv, hpayv_eq, hdom3_sA, hg, hm, hbe, heff3, hln3, hlf3, hlk3, hlp3, hlcb3, hlcl3⟩ :=
        eval_finishBranchLen_none sA Nd nodew frw kw payA cbufw clenw
          hsA_c hsA_AR hsA_N hnode_in (by rw [hsA_memW]; exact hk3)
          hsA_ln hsA_lf hsA_lk hsA_lp hsA_lcb hsA_lcl hpayA0
          (by rw [hite3_ev])
      rw [hite3_ev] at hg hm hbe heff3 hln3 hlf3 hlk3 hlp3 hlcb3 hlcl3
      dsimp only at hg hm hbe heff3 hln3 hlf3 hlk3 hlp3 hlcb3 hlcl3
      have hbr_sA : branchRefsLenSum sA nodew.toNat 16 = branchRefsLenSum s nodew.toNat 16 := by
        refine branchRefsLenSum_congr ((hN.1 nodew.toNat hnode_in).2.2.2.2.2.1 hk3)
          (fun _ _ => by rw [hsA_memW])
          (fun m _ => by unfold nodeRefBytes; rw [hsA_memW]) 16 (le_refl _)
      have hpayv_fin : payv.toNat = finishPayloadLen s frw.toNat nodew.toNat := by
        unfold finishPayloadLen
        rw [if_neg hk3_ne2, if_pos hk3, hpayv_eq, hpayA0, hbr_sA, hsA_memW, hsA_memB]
        have hp0 := hfr.2.2.2.2.2.2.2.2.1 (hnode.symm ▸ hk3)
        omega
      have hdom3_s : memW s nodew.toNat = 3 → 0 < memW s (nodew.toNat + 168) →
          s.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW s (nodew.toNat + 160)))) := by
        intro _ hpos
        change entry.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW s (nodew.toNat + 160))))
        rw [← heff_sA.memaddrs]
        rw [hsA_memW] at hdom3_sA
        exact hdom3_sA hpos
      exact ⟨payv, hpayv_fin, hdom3_s, hg.trans hsA_g, hm.trans hsA_m, hbe.trans hsA_be,
        heff_sA.trans heff3, hln3, hlf3, hlk3, hlp3, hlcb3, hlcl3⟩
    · rw [if_neg hkw3] at hite3_ev
      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hite3_ev
      injection hite3_ev with _ hst_eq
      subst hst_eq
      have hk_ne3 : memW s nodew.toNat ≠ 3 := by
        intro hk3; apply hkw3; apply BitVec.eq_of_toNat_eq; rw [hkw_nat, hk3]; rfl
      have hpayA_fin : payA.toNat = finishPayloadLen s frw.toNat nodew.toNat := by
        unfold finishPayloadLen
        by_cases hk2 : memW s nodew.toNat = 2
        · rw [if_pos hk2, hpayA_nat, if_pos hk2]
        · rw [if_neg hk2, if_neg hk_ne3, hpayA_nat, if_neg hk2]
      exact ⟨payA, hpayA_fin, fun hk3 => absurd hk3 hk_ne3, hsA_g, hsA_m, hsA_be,
        heff_sA, hsA_ln, hsA_lf, hsA_lk, hsA_lp, hsA_lcb, hsA_lcl⟩
  obtain ⟨payv, hpayv_nat, hdom3_s, hst_g, hst_m, hst_be, heff_st,
    hst_ln, hst_lf, hst_lk, hst_lp, hst_lcb, hst_lcl⟩ := hst_char
  have hst_AR : ArenaReady st := heff_st.arena
  have hst_c : st.code = originalRuntimeCode := hst_AR.1.code
  have hst_ma : st.memaddrs = s.memaddrs := heff_st.memaddrs
  have hst_memW : memW st = memW s := by ext a; unfold memW; rw [hst_m]
  have hst_memB : memB st = memB s := by ext a; unfold memB; rw [hst_m, hst_be]
  have hst_globN : ∀ nm, globN st nm = globN s nm := fun nm => by simp [globN, hst_g]
  obtain ⟨hst_N, hst_ext⟩ :=
    nodeHeap_of_heapByteEff_disj hent_AR hent_N heff_st (fun _ h => by simp at h)
  have hst_kc_eq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion st gs = bufferRegion s gs := by
    intro gs _
    unfold bufferRegion; rw [hst_globN]
  have hst_kcIvls : keccakBufIvls st = keccakBufIvls s := by
    simp only [keccakBufIvls, hst_kc_eq ("keccak_pad", 136) (by decide),
      hst_kc_eq ("keccak_st", 200) (by decide)]
  have hst_KS : KeccakBufsSafe st Nd :=
    keccakBufsSafe_of_grows hKS ⟨by rw [hst_globN], by rw [hst_globN]⟩ hst_kc_eq hst_ext
  have hst_vs : NodeValuesSafe sp0 st Nd := by
    have heff_s_st : HeapByteEff s st
        (nodeCacheIvls Nd ++ keccakBufIvls s ++ []) ["heap_ptr"] :=
      ((HeapByteEff.refl hAR _ ["heap_ptr"]).locals_clock entry.locals entry.clock).trans
        (heff_st.mono (fun _ h => by simp at h) (fun _ h => h))
    exact nodeValuesSafe_of_heapByteEff hAR hN hKS (by decide) (by decide) heff_s_st
      (fun _ h => by simp at h) hvs
  have hpay_pos : 1 ≤ payv.toNat := by
    rw [hpayv_nat, ← hnode]; exact finishPayloadLen_pos s Nd frw.toNat hfr
  have hpay_lt : payv.toNat < 2 ^ 42 := by
    rw [hpayv_nat, ← hnode]; exact finishPayloadLen_lt s Nd frw.toNat hN hfr
  have hfw_st_eq : finishWriteLen st frw.toNat nodew.toNat =
      finishWriteLen s frw.toNat nodew.toNat := by
    unfold finishWriteLen
    have hbr_st : memW s nodew.toNat = 3 →
        branchRefsLenSum st nodew.toNat 16 = branchRefsLenSum s nodew.toNat 16 := fun hk3 =>
      branchRefsLenSum_congr ((hN.1 nodew.toNat hnode_in).2.2.2.2.2.1 hk3)
        (fun _ _ => by rw [hst_memW])
        (fun m _ => by unfold nodeRefBytes; rw [hst_memW]) 16 (le_refl _)
    have hnrb_st : nodeRefBytes st (memW s (nodew.toNat + 48)) =
        nodeRefBytes s (memW s (nodew.toNat + 48)) := by
      unfold nodeRefBytes; rw [hst_memW]
    by_cases hk3 : memW s nodew.toNat = 3
    · simp [hst_memW, hst_memB, hk3, hbr_st hk3]
    · simp [hst_memW, hst_memB, hk3, hnrb_st]
  have hpay_eq_write : payv.toNat = finishWriteLen st frw.toNat nodew.toNat := by
    rw [hfw_st_eq, hpayv_nat, ← hnode, (finishWriteLen_eq_payload s Nd frw.toNat hfr).symm]
  have hclen60 : (memW st nodew.toNat = 1 ∨ memW st nodew.toNat = 2) → clenw.toNat < 2 ^ 60 := by
    rw [hst_memW, hcl_nat]
    have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAR.2.2.1
    have hlim60 : heapLimit < 2 ^ 60 := by decide
    rintro (hk1 | hk2)
    · have hin := (hfr.2.2.2.2.2.2.2.2.2.1 (hnode.symm ▸ hk1)).2.2.1
      dsimp [Inside] at hin; omega
    · have hin := (hfr.2.2.2.2.2.2.2.2.2.2.1 (hnode.symm ▸ hk2)).2.2.1
      dsimp [Inside] at hin; omega
  have hcb_in_st : (memW st nodew.toNat = 1 ∨ memW st nodew.toNat = 2) →
      1 ≤ clenw.toNat ∧ Inside (cbufw.toNat, clenw.toNat) sourceBase (globN st "heap_ptr") := by
    rw [hst_memW, hcb_nat, hcl_nat, hst_globN]
    rintro (hk1 | hk2)
    · have hl := hfr.2.2.2.2.2.2.2.2.2.1 (hnode.symm ▸ hk1)
      exact ⟨hl.1, hl.2.2.1⟩
    · have he := hfr.2.2.2.2.2.2.2.2.2.2.1 (hnode.symm ▸ hk2)
      exact ⟨he.1, he.2.2.1⟩
  have hdom1_st : memW st nodew.toNat = 1 → 0 < memW st (nodew.toNat + 56) →
      st.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW st (nodew.toNat + 48)))) := by
    rw [hst_memW, hst_ma]
    intro hk1 hpos
    have hl := (hfr.2.2.2.2.2.2.2.2.2.1 (hnode.symm ▸ hk1)).2.2.2.2.2.2
    rw [hnode] at hl
    exact hl hpos
  have hdom3_st : memW st nodew.toNat = 3 → 0 < memW st (nodew.toNat + 168) →
      st.memaddrs (panByteAlignHOL (BitVec.ofNat 64 (memW st (nodew.toNat + 160)))) := by
    rw [hst_memW, hst_ma]
    exact hdom3_s
  obtain ⟨hrv0, hlBv, offF, hhl_eq, hhl1, hhl9, hoffF_nat, hbuf_lim, hbuf_disj,
    heff_fin, hhp_lt, hN_fin, hext_fin, hKS_fin, h8_fin, h16_fin, hother_fin, hword_fin⟩ :=
    eval_finRest_returned sp0 st Nd nodew frw kw payv cbufw clenw rv
      hst_c hst_AR hst_N hst_KS hst_vs (by rw [hst_globN]; exact hsp_le_sp0)
      hnode_in (by rw [hst_memW]; exact hk123) (by rw [hst_memW]; exact hkw_nat)
      hpay_pos hpay_lt hpay_eq_write
      (by rw [hst_memW]; exact hcb_nat) (by rw [hst_memW]; exact hcl_nat)
      hclen60 hcb_in_st hdom1_st hdom3_st
      hst_ln hst_lf hst_lk hst_lp hst_lcb hst_lcl hret
  set postFin := (evaluateHOLFiniteState st finRest).2
  have hinner_2 : (evaluateHOLFiniteState entry finishAfterLoads).2 = postFin := by
    rw [finishAfterLoads_eq_finLoadsRest, finLoadsRest, evaluateHOLFiniteState_seq_line780,
      hev_ite2]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780, hev_ite3]
  let outer2 := (evaluateHOLFiniteState s
    (sourceFnBody Guest.Software.guestFn__node_rlp_finish)).2
  have hom : outer2.memory = postFin.memory := hloads_m.trans (congrArg (·.memory) hinner_2)
  have hog : outer2.globals = postFin.globals := hloads_g.trans (congrArg (·.globals) hinner_2)
  have hob : outer2.be = postFin.be := hloads_be.trans (congrArg (·.be) hinner_2)
  have homa : outer2.memaddrs = postFin.memaddrs := hloads_ma.trans (congrArg (·.memaddrs) hinner_2)
  have hoc : outer2.code = postFin.code := hloads_c.trans (congrArg (·.code) hinner_2)
  have hosh : outer2.shMemaddrs = postFin.shMemaddrs := hloads_sh.trans (congrArg (·.shMemaddrs) hinner_2)
  have hoba : outer2.baseAddr = postFin.baseAddr := hloads_ba.trans (congrArg (·.baseAddr) hinner_2)
  have homW : memW outer2 = memW postFin := by ext a; unfold memW; rw [hom]
  have homB : memB outer2 = memB postFin := by ext a; unfold memB; rw [hom, hob]
  have hogN : ∀ nm, globN outer2 nm = globN postFin nm := fun nm => by simp [globN, hog]
  have hoAR : ArenaReady outer2 :=
    ⟨guestInv_congr hoc homa hosh hoba heff_fin.arena.1,
     arenaOK_congr_globals hog heff_fin.arena.2⟩
  set totLen := hlBv.toNat + payv.toNat
  have hdisj_s : ∀ o ∈ nodeExtents s Nd, Disj (globN s "heap_ptr", totLen) o := by
    intro o ho
    change o ∈ nodeExtents entry Nd at ho
    rw [← hst_ext] at ho
    simpa [hst_globN] using hbuf_disj o ho
  have heff_s_outer : R16Shards.WkBlockTxEnc.HeapByteEff s outer2
      ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] := by
    have heff_s_st : R16Shards.WkBlockTxEnc.HeapByteEff s st
        ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] :=
      ((HeapByteEff.refl hAR _ ["heap_ptr"]).locals_clock entry.locals entry.clock).trans
        (heff_st.mono (fun _ h => by simp at h) (fun _ h => h))
    have heff_st_pf : R16Shards.WkBlockTxEnc.HeapByteEff st postFin
        ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] := by
      simpa [hst_globN, hst_kcIvls] using heff_fin
    have heff_s_pf := heff_s_st.trans heff_st_pf
    refine ⟨hoAR, homa.trans heff_s_pf.memaddrs,
      by rw [hogN]; exact heff_s_pf.hp_le,
      by rw [hogN]; exact heff_s_pf.fp_eq,
      by rw [hogN]; exact heff_s_pf.sp_le,
      hob.trans heff_s_pf.be,
      fun k hk => (heff_s_pf.globals k hk).trans (congrArg (fun g => g.lookup k) hog.symm),
      fun a hne => heff_s_pf.out_dom a (hom ▸ hne),
      fun a hne => heff_s_pf.cell_frame a (hom ▸ hne),
      fun b hb hne => heff_s_pf.byte_frame b hb (homB ▸ hne)⟩
  have hother_s : ∀ n ∈ Nd, n ≠ nodew.toNat → memW outer2 (n + 8) = memW s (n + 8) ∧
      memW outer2 (n + 16) = memW s (n + 16) := by
    intro n hn hne
    rw [homW, ← hst_memW]
    exact hother_fin n hn hne
  have h8_s : memW outer2 (nodew.toNat + 8) = globN s "heap_ptr" := by
    rw [homW, h8_fin, hst_globN]
  have h16_s : memW outer2 (nodew.toNat + 16) = totLen := by
    rw [homW, h16_fin, hoffF_nat]
  have hword_s : ∀ n ∈ Nd, memW outer2 n = memW s n ∧
      (1 ≤ memW s n → memW outer2 (n + 40) = memW s (n + 40)) ∧
      (memW s n = 1 → memW outer2 (n + 48) = memW s (n + 48) ∧
        memW outer2 (n + 56) = memW s (n + 56)) := by
    intro n hn
    rw [homW, ← hst_memW]
    exact hword_fin n hn
  have htot40 : totLen < 2 ^ 40 := by
    have hlim40 : heapLimit < 2 ^ 40 := by decide
    have := hbuf_lim
    omega
  obtain ⟨hoN, hoext⟩ : NodeHeap outer2 Nd ∧ nodeExtents outer2 Nd = nodeExtents s Nd := by
    have heff_cache : R16Shards.WkBlockTxEnc.HeapByteEff s outer2
        (nodeCacheIvls Nd ++ ((globN s "heap_ptr", totLen) :: keccakBufIvls s)) ["heap_ptr"] := by
      refine heff_s_outer.mono (fun i hi _ => ?_) (fun _ h => h)
      rcases List.mem_cons.1 hi with rfl | hr
      · exact Or.inl ⟨(globN s "heap_ptr", totLen),
          List.mem_append_right _ (List.Mem.head _), le_rfl, le_rfl⟩
      · rcases List.mem_append.1 hr with hc | hkc
        · exact Or.inl ⟨i, List.mem_append_left _ hc, le_rfl, le_rfl⟩
        · exact Or.inl ⟨i, List.mem_append_right _ (List.Mem.tail _ hkc), le_rfl, le_rfl⟩
    refine nodeHeap_of_heapByteEff_cache hAR hN heff_cache ?_ ?_
    · intro e he o ho
      rcases List.mem_cons.1 he with rfl | hkc
      · exact hdisj_s o ho
      · exact keccakBufIvls_disj_of_safe hKS e hkc o ho
    · intro n hn
      by_cases hnn : n = nodew.toNat
      · subst hnn; rw [h16_s]; exact htot40
      · rw [(hother_s n hn hnn).2]; exact (hN.1 n hn).2.2.2.2.2.2.2.1
  have hoKS : KeccakBufsSafe outer2 Nd := by
    have hkc_eq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
        bufferRegion outer2 gs = bufferRegion s gs := by
      intro gs hgs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
      rcases hgs with rfl | rfl
      · unfold bufferRegion globN
        rw [← heff_s_outer.globals (ofString "keccak_pad") (by decide)]
      · unfold bufferRegion globN
        rw [← heff_s_outer.globals (ofString "keccak_st") (by decide)]
    exact keccakBufsSafe_of_grows hKS ⟨heff_s_outer.hp_le, heff_s_outer.sp_le⟩ hkc_eq hoext
  have hoVS : NodeValuesSafe sp0 outer2 Nd := by
    have heff_vs : R16Shards.WkBlockTxEnc.HeapByteEff s outer2
        (nodeCacheIvls Nd ++ keccakBufIvls s ++ [(globN s "heap_ptr", totLen)]) ["heap_ptr"] := by
      refine heff_s_outer.mono (fun i hi _ => ?_) (fun _ h => h)
      rcases List.mem_cons.1 hi with rfl | hr
      · exact Or.inl ⟨(globN s "heap_ptr", totLen),
          List.mem_append_right _ (List.Mem.head _), le_rfl, le_rfl⟩
      · exact Or.inl ⟨i, List.mem_append_left _ hr, le_rfl, le_rfl⟩
    refine nodeValuesSafe_of_heapByteEff hAR hN hKS (by decide) (by decide) heff_vs ?_ hvs
    intro e he _ o ho
    simp only [List.mem_singleton] at he; subst he
    exact hdisj_s o ho
  refine ⟨hrv0, totLen, by dsimp [totLen]; omega, by rw [← hst_globN]; exact hbuf_lim,
    hdisj_s, heff_s_outer, ?_, hoN, hoext, hoKS, hoVS, h8_s, h16_s, hother_s, hword_s⟩
  rw [hogN, ← hst_globN]; exact hhp_lt

private theorem eval_call__node_rlp_finish_none {F : Type}
    (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (frExp nodeExp : ExpHOL 64) (frw nodew : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (hN : NodeHeap s Nd) (hKS : KeccakBufsSafe s Nd)
    (hvs : NodeValuesSafe sp0 s Nd)
    (hsp_le_sp0 : globN s "scratch_ptr" ≤ sp0)
    (hfr_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
      some (.val (.word frw)))
    (hnode_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
      some (.val (.word nodew)))
    (hfr : ValidRlpFrame s Nd frw.toNat)
    (hnode : memW s (frw.toNat + 8) = nodew.toNat)
    (hnone : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "_node_rlp_finish") [frExp, nodeExp])).1 = none) :
    let post := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "_node_rlp_finish") [frExp, nodeExp])).2
    post.locals = s.locals ∧
    ∃ totLen : Nat,
      1 ≤ totLen ∧
      globN s "heap_ptr" + totLen ≤ heapLimit ∧
      (∀ o ∈ nodeExtents s Nd, Disj (globN s "heap_ptr", totLen) o) ∧
      R16Shards.WkBlockTxEnc.HeapByteEff s post
        ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] ∧
      globN s "heap_ptr" < globN post "heap_ptr" ∧
      NodeHeap post Nd ∧
      nodeExtents post Nd = nodeExtents s Nd ∧
      KeccakBufsSafe post Nd ∧
      NodeValuesSafe sp0 post Nd ∧
      memW post (nodew.toNat + 8) = globN s "heap_ptr" ∧
      memW post (nodew.toNat + 16) = totLen ∧
      (∀ n ∈ Nd, n ≠ nodew.toNat → memW post (n + 8) = memW s (n + 8) ∧
        memW post (n + 16) = memW s (n + 16)) ∧
      (∀ n ∈ Nd, memW post n = memW s n ∧
        (1 ≤ memW s n → memW post (n + 40) = memW s (n + 40)) ∧
        (memW s n = 1 → memW post (n + 48) = memW s (n + 48) ∧
          memW post (n + 56) = memW s (n + 56))) := by
  intro post; dsimp only [post]
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [frExp, nodeExp] = some [.val (.word frw), .val (.word nodew)] := by
    simp [evalListHOLFinite, evalListHOLExact, hfr_ev, hnode_ev]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "_node_rlp_finish")
    (ofString "fr") (ofString "node")
    (sourceFnBody Guest.Software.guestFn__node_rlp_finish) frw nodew
    (by decide) (by rw [hc]; exact lookup__node_rlp_finish)
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
    rcases hcal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn__node_rlp_finish) with ⟨rc, sc⟩
    simp only [hcal] at hnone ⊢
    cases rc with
    | none => simp at hnone
    | some rc' =>
      cases rc' with
      | returned vc =>
        obtain ⟨rfl, totLen, htot1, hbuf_lim, hdisj, heff_ent, hhp_lt,
          hN_sc, hext_sc, hKS_sc, hVS_sc, h8_sc, h16_sc, hother_sc, hword_sc⟩ :=
          eval__node_rlp_finish_returned sp0 ent Nd frw nodew vc
            hc hent_AR hN hKS (nodeValuesSafe_with_locals sp0 s _ _ hvs)
            hsp_le_sp0 hfr hnode hent_fr hent_node (by rw [hcal])
        rw [hcal] at heff_ent hhp_lt hN_sc hext_sc hKS_sc hVS_sc h8_sc h16_sc hother_sc hword_sc
        dsimp only at heff_ent hhp_lt hN_sc hext_sc hKS_sc hVS_sc h8_sc h16_sc hother_sc hword_sc
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only; rw [if_pos hsh]; dsimp only
        have heff0 : R16Shards.WkBlockTxEnc.HeapByteEff s ent
            ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] :=
          (HeapByteEff.refl hAR _ ["heap_ptr"]).locals_clock ent.locals ent.clock
        have heff_out : R16Shards.WkBlockTxEnc.HeapByteEff s { sc with locals := s.locals }
            ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] :=
          (heff0.trans heff_ent).locals_clock s.locals sc.clock
        exact ⟨rfl, totLen, htot1, hbuf_lim, hdisj, heff_out, hhp_lt,
          hN_sc, hext_sc, hKS_sc, hVS_sc, h8_sc, h16_sc, hother_sc, hword_sc⟩
      | _ => simp at hnone

/-! ## `_node_rlp_fill` strong proof: scan, push/pop step, prologue, and top-level bound. -/


private theorem dec_eval_word_eq_sc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (e : ExpHOL 64) (w : BitVec 64) (b : ProgHOL 64)
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w))) :
    evaluateHOLFiniteState s (.dec x .one e b) =
      ((evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) b).1,
       { (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) b).2 with
         locals := HolFiniteMapExact.resVarEq
           (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) b).2.locals
           (x, s.locals.lookup x) }) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [hev]
  dsimp only
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh]

private theorem assign_local_word_eq_sc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (e : ExpHOL 64) (w w_old : BitVec 64)
    (hlk : s.locals.lookup x = some (.val (.word w_old)))
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w))) :
    evaluateHOLFiniteState s (.assign .local x e) =
      (none, setVarHOLFinite x (.val (.word w)) s) := by
  rw [evaluateHOLFiniteState_assign, hev]
  simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
    hlk, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]

private theorem scratch_alloc_48_returned_sc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (value : ValueHOL 64) (pa : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw_sp : "scratch_ptr" ∈ gw)
    (hcallee_n : callee.lookup (ofString "n") = some (.val (.word 48)))
    (hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_scratch_alloc) = (some (.returned value), pa)) :
    ∃ (qw : BitVec 64),
      value = .val (.word qw) ∧
      let mid := setVarHOLFinite name value { pa with locals := s.locals }
      mid.code = originalRuntimeCode ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (name, .val (.word qw)) ∧
      (∀ k : MlS, k ≠ ofString "scratch_ptr" → mid.globals.lookup k = s.globals.lookup k) ∧
      HeapByteEff s mid Rl gw ∧
      qw.toNat % 8 = 0 ∧
      globN s "frame_mem_ptr" ≤ qw.toNat ∧
      qw.toNat + 48 = globN s "scratch_ptr" ∧
      globN mid "scratch_ptr" = qw.toNat ∧
      WordsOK mid (qw.toNat, 48) := by
  obtain ⟨_, fp, sp, _, _, hfp_lk, hfp_glob, hsp_lk, hsp_glob⟩ :=
    InitECandidate.Solver.Wave8Contracts.M26.arenaOK_globals s hAR.2
  let entry := callEntryStateHOLFinite s callee
  have hsa := InitECandidate.Solver.Wave8GuestInv.R13.scratch_alloc_body_resumes entry sp fp hc
    hsp_lk hfp_lk (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨value, rfl⟩)
  dsimp only [entry] at hsa
  rw [hrun] at hsa
  obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hsa
  have hnw_eq : (48 : BitVec 64) = nw' := by
    change callee.lookup (ofString "n") = _ at hnw'_lk
    rw [hcallee_n] at hnw'_lk
    injection hnw'_lk with h'; injection h' with h'; injection h'
  subst hnw_eq
  dsimp only at hrv_eq hpa_eq
  injection hrv_eq with hrv_eq'; injection hrv_eq' with hval_eq
  let qw := (sp - 48) &&& ((0 : BitVec 64) - 8)
  have hval : value = .val (.word qw) := hval_eq
  subst hval
  refine ⟨qw, rfl, ?_⟩
  intro mid
  have hmid_next : mid = { s with
      globals := s.globals.update (ofString "scratch_ptr", .val (.word qw)),
      locals := s.locals.update (name, .val (.word qw)), clock := pa.clock } := by
    dsimp only [mid, setVarHOLFinite]; rw [hpa_eq]; rfl
  rcases hAR.2 with ⟨hc_hp_lo, hc_hp_hi, hc_fm_lo, hc_fm_hi, hc_sp_hi, hc_hp_al, hc_fm_al, hc_sp_al, hc_gw⟩
  have hfp_le_sp : fp.toNat ≤ sp.toNat := by rw [hfp_glob, hsp_glob]; exact hc_fm_hi
  have hsp_al : sp.toNat % 8 = 0 := by rw [hsp_glob]; exact hc_sp_al
  obtain ⟨hq_al, hfp_le_q, hq_le_sp, hq_add, _⟩ :=
    InitECandidate.Solver.Wave8GuestInv.R13.scratch_alloc_arith sp fp 48 hfp_le_sp hsp_al hcmp1 hcmp2
  change qw.toNat % 8 = 0 at hq_al
  change fp.toNat ≤ qw.toNat at hfp_le_q
  change qw.toNat ≤ sp.toNat at hq_le_sp
  change qw.toNat + ((48 : BitVec 64).toNat + 7) / 8 * 8 = sp.toNat at hq_add
  have hq_add48 : qw.toNat + 48 = sp.toNat := by
    have h48 : ((48 : BitVec 64).toNat + 7) / 8 * 8 = 48 := by decide
    rw [h48] at hq_add; exact hq_add
  have hn_globs : mid.globals = s.globals.update (ofString "scratch_ptr", .val (.word qw)) := by
    rw [hmid_next]
  have hn_hp : globN mid "heap_ptr" = globN s "heap_ptr" := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
  have hn_fmp : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hn_sp : globN mid "scratch_ptr" = qw.toNat := by
    unfold globN; rw [hn_globs, HolFiniteMapExact.lookup_update]; simp [FUPDATE]
  have hn_G : GuestInv mid :=
    guestInv_congr (by rw [hmid_next]) (by rw [hmid_next]) (by rw [hmid_next]) (by rw [hmid_next]) hAR.1
  have hn_gw : GlobalsWord mid :=
    globalsWord_update (s := s) (t := mid) (ofString "scratch_ptr") qw hn_globs hc_gw
  have hn_A : ArenaOK mid := by
    unfold ArenaOK; rw [hn_hp, hn_fmp, hn_sp]
    exact ⟨hc_hp_lo, hc_hp_hi, hc_fm_lo, by rw [← hfp_glob]; exact hfp_le_q,
      le_trans hq_le_sp (by rw [hsp_glob]; exact hc_sp_hi),
      hc_hp_al, hc_fm_al, hq_al, hn_gw⟩
  have hn_kept : GlobalsKept gw s mid := by
    intro k hk
    have hne : k ≠ ofString "scratch_ptr" := fun heq => hk (heq ▸ List.mem_map_of_mem hgw_sp)
    rw [hn_globs, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, Ne.symm hne]
  have hsb_ss : sourceBase ≤ scratchStart := by decide
  have hse_he : scratchEnd ≤ heapEnd := by rw [heapEnd_val]; decide
  have hq_lo_sb : sourceBase ≤ qw.toNat :=
    le_trans hsb_ss (le_trans hc_fm_lo (by rw [← hfp_glob]; exact hfp_le_q))
  have hq_hi_he : qw.toNat + 48 ≤ heapEnd := by
    rw [hq_add48]; exact le_trans (by rw [hsp_glob]; exact hc_sp_hi) hse_he
  have hwok : WordsOK mid (qw.toNat, 48) :=
    R10Shards.P26_P28.wordsOK_of_inside_heap hn_G hq_al (by decide) hq_lo_sb hq_hi_he
  have heff_mid : HeapByteEff s mid Rl gw :=
    ⟨⟨hn_G, hn_A⟩, by rw [hmid_next], by rw [hn_hp], hn_fmp,
     by rw [hn_sp, ← hsp_glob]; exact hq_le_sp, by rw [hmid_next], hn_kept,
     fun a hne => absurd (by rw [hmid_next]) hne,
     fun a hne => absurd (by rw [hmid_next]) hne,
     fun b _ hne => absurd (by unfold memB; rw [hmid_next]) hne⟩
  exact ⟨by rw [hmid_next]; exact hc, by rw [hmid_next], by rw [hmid_next],
    fun k hk => by rw [hn_globs, HolFiniteMapExact.lookup_update]; simp [FUPDATE, Ne.symm hk],
    heff_mid, hq_al, by rw [← hfp_glob]; exact hfp_le_q, by rw [← hsp_glob]; exact hq_add48,
    hn_sp, hwok⟩

private theorem eval_decCall_scratch_alloc_48_none_sc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS) (cont : ProgHOL 64)
    (Rl : List Ivl) (gw : List String)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw_sp : "scratch_ptr" ∈ gw)
    (hnone : (evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc") [.const 48] cont)).1 = none) :
    ∃ (qw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      mid.code = originalRuntimeCode ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (name, .val (.word qw)) ∧
      (∀ k : MlS, k ≠ ofString "scratch_ptr" → mid.globals.lookup k = s.globals.lookup k) ∧
      HeapByteEff s mid Rl gw ∧
      qw.toNat % 8 = 0 ∧
      globN s "frame_mem_ptr" ≤ qw.toNat ∧
      qw.toNat + 48 = globN s "scratch_ptr" ∧
      globN mid "scratch_ptr" = qw.toNat ∧
      WordsOK mid (qw.toNat, 48) ∧
      (evaluateHOLFiniteState mid cont).1 = none ∧
      evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc") [.const 48] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (name, s.locals.lookup name) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnone ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 48] =
      some [.val (.word 48)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_scratch_alloc) 48 (by rw [hc]; exact lookup_scratch_alloc)
  simp only [hargs, hlk] at hnone ⊢
  by_cases hz : s.clock = 0
  · simp [hz] at hnone
  · simp only [hz, ↓reduceIte] at hnone ⊢
    set cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      HolFiniteMapExact.empty.update (ofString "n", .val (.word (48 : BitVec 64)))
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
      (sourceFnBody Guest.Software.guestFn_scratch_alloc) with ⟨res, pa⟩
    simp only [hrun] at hnone ⊢
    cases res with
    | none => simp at hnone
    | some r1 =>
      cases r1 with
      | returned value =>
        have hcn : cmap.lookup (ofString "n") = some (.val (.word 48)) := by
          simp [cmap, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨qw, rfl, hmid_c, hmid_mem, hmid_loc, hmid_glob, heff_mid,
          hq_al, hfp_q, hq_sp, hmid_sp, hwok⟩ :=
          scratch_alloc_48_returned_sc s name cmap value pa Rl gw hc hAR hgw_sp hcn hrun
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word qw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word qw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        simp only [hsh, ↓reduceIte] at hnone ⊢
        exact ⟨qw, _, hmid_c, hmid_mem, hmid_loc, hmid_glob, heff_mid,
          hq_al, hfp_q, hq_sp, hmid_sp, hwok, hnone, rfl⟩
      | _ => simp at hnone

private theorem word_of_locN_ne_zero {F : Type} {s : PanSemStateFiniteExact 64 F} {nm : String}
    (hne : locN s nm ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup (ofString nm) = some (.val (.word w)) ∧ w.toNat = locN s nm := by
  unfold locN at hne ⊢
  rcases hlk : s.locals.lookup (ofString nm) with _ | v
  · simp [hlk] at hne
  · rcases v with x | _ | _
    · cases x with
      | word w => exact ⟨w, rfl, by simp [hlk]⟩
    · simp [hlk] at hne
    · simp [hlk] at hne

private theorem loopActive_top_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ha : LoopActive (.cmp .notEqual (.var .local (ofString "top")) (.const 0)) s) :
    ∃ topw : BitVec 64,
      s.locals.lookup (ofString "top") = some (.val (.word topw)) ∧
      topw ≠ 0 ∧ topw.toNat = locN s "top" := by
  obtain ⟨cw, he, hcw⟩ := ha
  rw [evalHOLFinite_eq_toExact] at he
  rcases ht : s.locals.lookup (ofString "top") with _ | vt
  · simp [evalHOLExact, evalListHOLExact, ht] at he
  · rcases vt with ⟨⟨topw⟩⟩ | _ | _
    · refine ⟨topw, rfl, ?_, by simp [locN, ht]⟩
      intro hz
      subst hz
      simp [evalHOLExact, evalListHOLExact, ht, Compiler.Encoders.Asm.wordCmpHOL] at he
      exact hcw he.symm
    · simp [evalHOLExact, evalListHOLExact, ht, Compiler.Encoders.Asm.wordCmpHOL] at he
    · simp [evalHOLExact, evalListHOLExact, ht, Compiler.Encoders.Asm.wordCmpHOL] at he

private theorem signedLess_16_sc (iw : BitVec 64) (hlt : iw.toNat < 16) :
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess iw 16 = true := by
  have hi_msb : iw.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.2 (by omega)
  have h16_msb : (16 : BitVec 64).msb = false := by decide
  have h16_nat : (16 : BitVec 64).toNat = 16 := rfl
  simp [Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, BitVec.slt, BitVec.toInt,
    hi_msb, h16_msb, h16_nat, hlt]

private theorem scratch_mark_returned_sc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (value : ValueHOL 64) (pm : PanSemStateFiniteExact 64 F)
    (hAR : ArenaReady s)
    (hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_scratch_mark) = (some (.returned value), pm)) :
    ∃ sp : BitVec 64,
      value = .val (.word sp) ∧
      sp.toNat = globN s "scratch_ptr" ∧
      setVarHOLFinite name value { pm with locals := s.locals } =
        { s with locals := s.locals.update (name, .val (.word sp)), clock := pm.clock } := by
  obtain ⟨_, _, sp, _, _, _, _, hsp_lk, hsp_eq⟩ :=
    InitECandidate.Solver.Wave8Contracts.M26.arenaOK_globals s hAR.2
  have hbsm : sourceFnBody Guest.Software.guestFn_scratch_mark =
      .return (.var .global (ofString "scratch_ptr")) := rfl
  rw [hbsm, evaluateHOLFiniteState_return] at hrun
  have hg_sp : (callEntryStateHOLFinite s callee).globals.lookup (ofString "scratch_ptr") =
      some (.val (.word sp)) := hsp_lk
  simp [evalHOLExact, hg_sp, shapeOfHOLExact] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  exact ⟨sp, rfl, hsp_eq, rfl⟩

private theorem keccak_sp0_of_safe {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hAR : ArenaReady s) (hKS : KeccakBufsSafe s Nd) :
    ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      0 < (bufferRegion s gs).2 →
      (bufferRegion s gs).1 + (bufferRegion s gs).2 ≤ globN s "heap_ptr" ∨
        globN s "scratch_ptr" ≤ (bufferRegion s gs).1 := by
  intro gs hgs hpos
  rcases (hKS gs hgs).1 with hz | hal
  · rw [hz] at hpos; omega
  · rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
    · exact Or.inl hhi
    · exact Or.inr hlo

private theorem disj_new_frame_keccak {F : Type} {s : PanSemStateFiniteExact 64 F}
    {fr sp0 : Nat}
    (hAR : ArenaReady s)
    (hfr_lo : globN s "frame_mem_ptr" ≤ fr) (hfr_sp0 : fr + 48 ≤ sp0)
    (hkc_sp0 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      0 < (bufferRegion s gs).2 →
      (bufferRegion s gs).1 + (bufferRegion s gs).2 ≤ globN s "heap_ptr" ∨
        sp0 ≤ (bufferRegion s gs).1) :
    ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      Disj (fr, 48) (bufferRegion s gs) := by
  intro gs hgs
  by_cases hpos : 0 < (bufferRegion s gs).2
  · rcases hkc_sp0 gs hgs hpos with hhi | hlo
    · have := hAR.2.2.1; have := hAR.2.2.2.1
      have : heapLimit ≤ scratchStart := by decide
      exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
    · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inl (by omega))



private theorem eval_fillScan_loop_none :
    ∀ (rem : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (ndw iw cw fw : BitVec 64),
      s.code = originalRuntimeCode →
      NodeHeap s Nd →
      ndw.toNat ∈ Nd →
      memW s ndw.toNat = 3 →
      iw.toNat ≤ 16 →
      16 - iw.toNat = rem →
      (fw ≠ 0 → cw.toNat ∈ Nd ∧ 1 ≤ memW s cw.toNat ∧ memW s cw.toNat ≤ 3) →
      s.locals.lookup (ofString "nd") = some (.val (.word ndw)) →
      s.locals.lookup (ofString "i") = some (.val (.word iw)) →
      s.locals.lookup (ofString "child") = some (.val (.word cw)) →
      s.locals.lookup (ofString "found") = some (.val (.word fw)) →
      (evaluateHOLFiniteState s (.while fillScanCond fillScanBody)).1 = none →
      ∃ (iw' cw' fw' : BitVec 64),
        iw'.toNat ≤ 16 ∧
        (fw' ≠ 0 → cw'.toNat ∈ Nd ∧ 1 ≤ memW s cw'.toNat ∧ memW s cw'.toNat ≤ 3) ∧
        (evaluateHOLFiniteState s (.while fillScanCond fillScanBody)).2 =
          { (setVarHOLFinite (ofString "found") (.val (.word fw'))
              (setVarHOLFinite (ofString "i") (.val (.word iw'))
                (setVarHOLFinite (ofString "child") (.val (.word cw')) s))) with
            clock := (evaluateHOLFiniteState s (.while fillScanCond fillScanBody)).2.clock }
  | 0, F, s, Nd, ndw, iw, cw, fw, _, _, _, _, hi_le, hrem, hfw_inv, _, hl_i, hl_c, hl_f, _ => by
    have hi16 : iw = 16 := BitVec.eq_of_toNat_eq (by
      have : (16 : BitVec 64).toNat = 16 := rfl
      omega)
    subst hi16
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        fillScanCond = some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [fillScanCond, evalHOLExact, evalListHOLExact, hl_i, hl_f,
        Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess,
        wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [hcond]; dsimp only
    rw [if_neg (by decide : ¬ (0 : BitVec 64) ≠ 0)]
    refine ⟨16, cw, fw, by decide, hfw_inv, ?_⟩
    cases s; simp only [setVarHOLFinite]; congr 1
    apply HolFiniteMapExact.ext; funext x
    by_cases hxf : x = ofString "found"
    · subst hxf; simpa [HolFiniteMapExact.lookup_update, FUPDATE] using hl_f
    · by_cases hxi : x = ofString "i"
      · subst hxi
        simpa [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "found" ≠ ofString "i" by decide] using hl_i
      · by_cases hxc : x = ofString "child"
        · subst hxc
          simpa [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "found" ≠ ofString "child" by decide,
            show ofString "i" ≠ ofString "child" by decide] using hl_c
        · simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxf, Ne.symm hxi, Ne.symm hxc]
  | rem + 1, F, s, Nd, ndw, iw, cw, fw, hc, hN, hnd_in, hk3, hi_le, hrem, hfw_inv, hl_nd, hl_i, hl_c, hl_f, hnone => by
    have hi_lt16 : iw.toNat < 16 := by omega
    have hlt_true : Compiler.Encoders.Asm.holAsmSignedLess iw 16#64 = true :=
      signedLess_16_sc iw hi_lt16
    by_cases hfz : fw = 0
    · subst hfz
      have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
          fillScanCond = some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        simp [fillScanCond, evalHOLExact, evalListHOLExact, hl_i, hl_f,
          Compiler.Encoders.Asm.wordCmpHOL, hlt_true, wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
      rw [hcond] at hnone ⊢; dsimp only at hnone ⊢
      rw [if_pos (by decide : (1 : BitVec 64) ≠ 0)] at hnone ⊢
      by_cases hcz : s.clock = 0
      · simp [hcz] at hnone
      · rw [if_neg hcz] at hnone ⊢
        set s0 := decClockHOLFinite s
        obtain ⟨_, _, hin_nd, hw_nd, _, hch3, _⟩ := hN.1 ndw.toNat hnd_in
        have hsz3 : nodeSize (memW s ndw.toNat) = 176 := by simp [nodeSize, hk3]
        have h264_lim : heapLimit ≤ 2 ^ 64 := by decide
        have hhi_nd : ndw.toNat + nodeSize (memW s ndw.toNat) ≤ 2 ^ 64 := by
          have := hin_nd.2; dsimp [nodeIvl] at this; omega
        have hev_addr : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
            (.op .add
              [.var .local (ofString "nd"), .const 32,
               .panop .mul [.var .local (ofString "i"), .const 8]]) =
            some (.val (.word (ndw + BitVec.ofNat 64 (32 + 8 * iw.toNat)))) := by
          have hadd_off : 32#64 + iw * 8#64 = BitVec.ofNat 64 (32 + 8 * iw.toNat) := by
            apply BitVec.eq_of_toNat_eq
            have h32 : (32#64).toNat = 32 := rfl
            have h8 : (8#64).toNat = 8 := rfl
            rw [BitVec.toNat_add, h32, BitVec.toNat_mul, h8, BitVec.toNat_ofNat]
            have hlt1 : iw.toNat * 8 < 2 ^ 64 := by omega
            have hlt2 : 32 + iw.toNat * 8 < 2 ^ 64 := by omega
            have hlt3 : 32 + 8 * iw.toNat < 2 ^ 64 := by omega
            rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt3]
            omega
          have hl_nd0 : s0.locals.lookup (ofString "nd") = some (.val (.word ndw)) := hl_nd
          have hl_i0 : s0.locals.lookup (ofString "i") = some (.val (.word iw)) := hl_i
          simp [evalHOLExact, evalListHOLExact, hl_nd0, hl_i0, panOpHOL,
            wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_assoc, hadd_off]
        obtain ⟨chw, hld_ch, hchw_nat⟩ := eval_load_memW_of_wordsOK (s := s0) (base := ndw)
          (off := 32 + 8 * iw.toNat) (len := nodeSize (memW s ndw.toNat)) hw_nd
          (by omega) (by omega) hhi_nd
          (e := .op .add
            [.var .local (ofString "nd"), .const 32,
             .panop .mul [.var .local (ofString "i"), .const 8]]) hev_addr
        have hch_root : RootIn Nd chw.toNat := by
          have hr := hch3 hk3 iw.toNat hi_lt16
          have hm0 : memW s0 (ndw.toNat + (32 + 8 * iw.toNat)) = memW s (ndw.toNat + 32 + 8 * iw.toNat) := by
            have : ndw.toNat + (32 + 8 * iw.toNat) = ndw.toNat + 32 + 8 * iw.toNat := by omega
            rw [this]; rfl
          rwa [hchw_nat, hm0]
        have hev_a1 : evaluateHOLFiniteState s0
            (.assign .local (ofString "child")
              (.load .one
                (.op .add
                  [.var .local (ofString "nd"), .const 32,
                   .panop .mul [.var .local (ofString "i"), .const 8]]))) =
            (none, setVarHOLFinite (ofString "child") (.val (.word chw)) s0) :=
          assign_local_word_eq_sc s0 (ofString "child") _ chw cw hl_c hld_ch
        set s1 := setVarHOLFinite (ofString "child") (.val (.word chw)) s0
        have hl_i1 : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          simp [s1, s0, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_i,
            show ofString "child" ≠ ofString "i" by decide]
        have hev_a2 : evaluateHOLFiniteState s1
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) =
            (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1))) s1) :=
          assign_local_word_eq_sc s1 (ofString "i") _ (iw + 1) iw hl_i1
            (by simp [evalHOLExact, evalListHOLExact, hl_i1, wordOpHOL, wordOp, valueIsWord, valueWord])
        set s2 := setVarHOLFinite (ofString "i") (.val (.word (iw + 1))) s1
        have hl_c2 : s2.locals.lookup (ofString "child") = some (.val (.word chw)) := by
          simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "child" by decide]
        have hl_f2 : s2.locals.lookup (ofString "found") = some (.val (.word 0)) := by
          simp [s2, s1, s0, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_f,
            show ofString "i" ≠ ofString "found" by decide,
            show ofString "child" ≠ ofString "found" by decide]
        have hbody_pre : evaluateHOLFiniteState s0 fillScanBody =
            evaluateHOLFiniteState s2
              (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
                [.var .local (ofString "child")]) := by
          unfold fillScanBody
          rw [evaluateHOLFiniteState_seq_line780, hev_a1]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hev_a2]
        rw [hbody_pre] at hnone ⊢
        have hcall_none : (evaluateHOLFiniteState s2
            (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
              [.var .local (ofString "child")])).1 = none := by
          have hnb := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
            (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
              [.var .local (ofString "child")]) rfl s2
          have hnc := evaluate_noTopContinue
            (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
              [.var .local (ofString "child")]) rfl s2
          rcases hcev : evaluateHOLFiniteState s2
              (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
                [.var .local (ofString "child")]) with ⟨rc, s3⟩
          rw [hcev] at hnone hnb hnc
          cases rc with
          | none => rfl
          | some rc' =>
            cases rc' with
            | «break» => exact absurd rfl hnb
            | «continue» => exact absurd rfl hnc
            | _ => simp at hnone
        obtain ⟨fw1, hfw1_nz, _, hs3_eq⟩ :=
          eval_call_local__node_needs_rlp s2 Nd "found" (.var .local (ofString "child")) chw
            hc hN ⟨0, hl_f2⟩ hch_root (by simp [evalHOLExact, hl_c2]) hcall_none
        have hcev_split : evaluateHOLFiniteState s2
            (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
              [.var .local (ofString "child")]) =
            (none, (evaluateHOLFiniteState s2
              (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
                [.var .local (ofString "child")])).2) :=
          Prod.ext hcall_none rfl
        rw [hcev_split] at hnone ⊢
        dsimp only at hnone ⊢
        set s3 := (evaluateHOLFiniteState s2
            (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
              [.var .local (ofString "child")])).2
        have hs3_c : s3.code = originalRuntimeCode := by rw [hs3_eq]; exact hc
        have hs3_N : NodeHeap s3 Nd := by rw [hs3_eq]; exact hN
        have hmem_s3_s : ∀ addr, memW s3 addr = memW s addr := fun addr => by rw [hs3_eq]; rfl
        have hi1_nat : (iw + 1).toNat = iw.toNat + 1 := by
          rw [BitVec.toNat_add]
          have : (1 : BitVec 64).toNat = 1 := rfl
          rw [this, Nat.mod_eq_of_lt (by omega)]
        have hl_nd3 : s3.locals.lookup (ofString "nd") = some (.val (.word ndw)) := by
          rw [hs3_eq]; simp [s2, s1, s0, decClockHOLFinite, setVarHOLFinite,
            HolFiniteMapExact.lookup_update, FUPDATE, hl_nd,
            show ofString "found" ≠ ofString "nd" by decide,
            show ofString "i" ≠ ofString "nd" by decide,
            show ofString "child" ≠ ofString "nd" by decide]
        have hl_i3 : s3.locals.lookup (ofString "i") = some (.val (.word (iw + 1))) := by
          rw [hs3_eq]; simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "found" ≠ ofString "i" by decide]
        have hl_c3 : s3.locals.lookup (ofString "child") = some (.val (.word chw)) := by
          rw [hs3_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hl_c2,
            show ofString "found" ≠ ofString "child" by decide]
        have hl_f3 : s3.locals.lookup (ofString "found") = some (.val (.word fw1)) := by
          rw [hs3_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨iw', cw', fw', hiw'_le, hfw'_nz, hrec_st⟩ :=
          eval_fillScan_loop_none rem s3 Nd ndw (iw + 1) chw fw1 hs3_c hs3_N hnd_in
            (by rw [hmem_s3_s]; exact hk3) (by omega) (by omega)
            (fun hnz => by
              obtain ⟨h1, h2, h3⟩ := hfw1_nz hnz
              rw [hmem_s3_s]; exact ⟨h1, h2, h3⟩)
            hl_nd3 hl_i3 hl_c3 hl_f3 hnone
        refine ⟨iw', cw', fw', hiw'_le,
          fun hnz => by
            obtain ⟨h1, h2, h3⟩ := hfw'_nz hnz
            rw [← hmem_s3_s]; exact ⟨h1, h2, h3⟩, ?_⟩
        rw [hrec_st, hs3_eq]
        cases s; simp only [s2, s1, s0, decClockHOLFinite, setVarHOLFinite]; congr 1
        apply HolFiniteMapExact.ext; funext x
        by_cases hxf : x = ofString "found"
        · subst hxf; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        · by_cases hxi : x = ofString "i"
          · subst hxi
            simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "found" ≠ ofString "i" by decide]
          · by_cases hxc : x = ofString "child"
            · subst hxc
              simp [HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "found" ≠ ofString "child" by decide,
                show ofString "i" ≠ ofString "child" by decide]
            · simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxf, Ne.symm hxi, Ne.symm hxc]
    · have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
          fillScanCond = some (.val (.word 0)) := by
        have hfz' : ¬ (fw = 0#64) := hfz
        rw [evalHOLFinite_eq_toExact]
        simp [fillScanCond, evalHOLExact, evalListHOLExact, hl_i, hl_f,
          Compiler.Encoders.Asm.wordCmpHOL, hlt_true, hfz', wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      rw [hcond]; dsimp only
      rw [if_neg (by decide : ¬ (0 : BitVec 64) ≠ 0)]
      refine ⟨iw, cw, fw, hi_le, hfw_inv, ?_⟩
      cases s; simp only [setVarHOLFinite]; congr 1
      apply HolFiniteMapExact.ext; funext x
      by_cases hxf : x = ofString "found"
      · subst hxf; simpa [HolFiniteMapExact.lookup_update, FUPDATE] using hl_f
      · by_cases hxi : x = ofString "i"
        · subst hxi
          simpa [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "found" ≠ ofString "i" by decide] using hl_i
        · by_cases hxc : x = ofString "child"
          · subst hxc
            simpa [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "found" ≠ ofString "child" by decide,
              show ofString "i" ≠ ofString "child" by decide] using hl_c
          · simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxf, Ne.symm hxi, Ne.symm hxc]



private theorem validRlpFrame_after_store16_s {F : Type}
    {sp0 : Nat} {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {fr : Nat}
    {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (hvs : NodeValuesSafe sp0 s Nd)
    (hext_eq : nodeExtents post Nd = nodeExtents s Nd)
    (hbuf_eq : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      bufferRegion post gs = bufferRegion s gs)
    (heff : HeapByteEff s post [(fr + 16, 8)] gw)
    (hfr_sp0 : fr + 48 ≤ sp0)
    (hfg_sp0 : globN s "scratch_ptr" ≤ sp0)
    (hm16_post : memW post (fr + 16) ≤ 16)
    (hv : ValidRlpFrame s Nd fr) :
    ValidRlpFrame post Nd fr := by
  obtain ⟨hfr8, hfr_in, hfr_W, hnd_in, hk1, hk3, _hidx, hpay, hk3_pay, hk1_pay, hk2_pay, hfr_kb⟩ := hv
  have hse : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have h264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hhl_sc : heapLimit ≤ scratchStart := by decide
  have hfmp_le := hAs.2.2.2.1
  have hsp_ge := hAs.2.2.2.2.1
  have hsp_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := heff.sp_le
  have hfr_in_post : Inside (fr, 48) (globN post "scratch_ptr") scratchEnd :=
    ⟨hsp_le.trans hfr_in.1, hfr_in.2⟩
  have hfr_W_post : WordsOK post (fr, 48) :=
    P3MptSet.wordsOK_transfer hAs.1 heff.arena.1 hfr_W
  have hword_ne16 : ∀ off, off % 8 = 0 → off + 8 ≤ 48 → off ≠ 16 →
      memW post (fr + off) = memW s (fr + off) := by
    intro off hoff8 hoff_le hne16
    obtain ⟨hfr_lo, hfr_hi⟩ := hfr_in
    dsimp only at hfr_lo hfr_hi
    apply memW_eq_of_heapByteEff_disj hAs heff (by omega)
      (Or.inr ⟨by omega, by omega⟩) (by omega)
    intro iv hiv _
    simp only [List.mem_singleton] at hiv; subst hiv
    by_cases hlt : off < 16
    · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
    · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
  have hw8 := hword_ne16 8 (by decide) (by decide) (by decide)
  have hw24 := hword_ne16 24 (by decide) (by decide) (by decide)
  have hw32 := hword_ne16 32 (by decide) (by decide) (by decide)
  have hw40 := hword_ne16 40 (by decide) (by decide) (by decide)
  have hnd_word : ∀ n ∈ Nd, ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
      memW post (n + off) = memW s (n + off) := by
    intro n hn off hoff8 hoff_lt
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
    have hn8 : n % 8 = 0 := hw_n.1
    have hal_off : Allocated s (n + off, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    have ha_lt : n + off < 2 ^ 64 := by have := hin_n.2; dsimp [nodeIvl] at this; omega
    apply memW_eq_of_heapByteEff_disj hAs heff (by omega) hal_off ha_lt
    intro iv hiv _
    simp only [List.mem_singleton] at hiv; subst hiv
    have := hin_n.2; dsimp [nodeIvl] at this
    exact Or.inr (Or.inr (Or.inl (by dsimp [Inside] at hfr_in ⊢; omega)))
  have hnd_in' : memW post (fr + 8) ∈ Nd := hw8 ▸ hnd_in
  have hsz_nd := nodeSize_ge32 (memW s (memW s (fr + 8)))
  have hk_eq : memW post (memW post (fr + 8)) = memW s (memW s (fr + 8)) := by
    rw [hw8]
    simpa using hnd_word (memW s (fr + 8)) hnd_in 0 (by decide) (by omega)
  have hn40_eq : (memW s (memW s (fr + 8)) = 1 ∨ memW s (memW s (fr + 8)) = 2) →
      memW post (memW post (fr + 8) + 40) = memW s (memW s (fr + 8) + 40) := by
    intro h12
    have hsz12 : 48 ≤ nodeSize (memW s (memW s (fr + 8))) := by
      rcases h12 with h1 | h2
      · simp [nodeSize, h1]
      · simp [nodeSize, h2]
    rw [hw8]
    exact hnd_word (memW s (fr + 8)) hnd_in 40 (by decide) hsz12
  have hcb_byte_eq : (memW s (memW s (fr + 8)) = 1 ∨ memW s (memW s (fr + 8)) = 2) →
      1 ≤ memW s (fr + 32) → Inside (memW s (fr + 24), memW s (fr + 32)) sourceBase (globN s "heap_ptr") →
      memB post (memW s (fr + 24)) = memB s (memW s (fr + 24)) := by
    intro _ hcl1 hcb_in
    obtain ⟨hcb_lo, hcb_hi⟩ := hcb_in
    dsimp only at hcb_lo hcb_hi
    have hhp_hi := hAs.2.2.1
    have hb_lt : memW s (fr + 24) < 2 ^ 64 := by omega
    by_contra hne
    rcases heff.byte_frame (memW s (fr + 24)) hb_lt hne with
      ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
    · simp only [List.mem_singleton] at hiv; subst hiv
      dsimp [Inside] at hfr_in hb1 hb2; omega
    · dsimp [freeGap] at hfg1 hfg2; omega
    · dsimp [heapFree] at hhf1 hhf2; omega
  refine ⟨hfr8, hfr_in_post, hfr_W_post, hnd_in',
    by rw [hk_eq]; exact hk1, by rw [hk_eq]; exact hk3,
    hm16_post, by rw [hw40]; exact hpay,
    fun h3 => by rw [hw40]; exact hk3_pay (hk_eq ▸ h3), ?_, ?_,
    fun gs hgs => by rw [hbuf_eq gs hgs]; exact hfr_kb gs hgs⟩
  · intro h1
    have h1s : memW s (memW s (fr + 8)) = 1 := hk_eq ▸ h1
    have hsz1 : nodeSize (memW s (memW s (fr + 8))) = 64 := by simp [nodeSize, h1s]
    have hn48_eq : memW post (memW post (fr + 8) + 48) = memW s (memW s (fr + 8) + 48) := by
      rw [hw8]; exact hnd_word (memW s (fr + 8)) hnd_in 48 (by decide) (by omega)
    have hn56_eq : memW post (memW post (fr + 8) + 56) = memW s (memW s (fr + 8) + 56) := by
      rw [hw8]; exact hnd_word (memW s (fr + 8)) hnd_in 56 (by decide) (by omega)
    obtain ⟨hcl1, hcl_hi, hcb_in, hcb_disj, hcb_kb, hpay_lo, hdom1⟩ := hk1_pay h1s
    have hcb_b := hcb_byte_eq (Or.inl h1s) hcl1 hcb_in
    refine ⟨by rw [hw32]; exact hcl1, by rw [hw32, hn40_eq (Or.inl h1s)]; exact hcl_hi,
      ⟨by rw [hw24]; exact hcb_in.1, by rw [hw24, hw32]; exact hcb_in.2.trans heff.hp_le⟩,
      fun o ho => by rw [hext_eq] at ho; rw [hw24, hw32]; exact hcb_disj o ho,
      fun gs hgs => by rw [hbuf_eq gs hgs, hw24, hw32]; exact hcb_kb gs hgs,
      ?_, ?_⟩
    · unfold leafPayloadExact at hpay_lo ⊢
      rw [hw40, hw24, hw32, hn48_eq, hn56_eq, hcb_b]
      by_cases hv1 : memW s (memW s (fr + 8) + 56) = 1
      · have hpos1 : 0 < memW s (memW s (fr + 8) + 56) := by omega
        have hdom_ord : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW s (memW s (fr + 8) + 48)))) := by
          rw [← hAs.1.memaddrs]; exact hdom1 hpos1
        obtain ⟨_, _, hfg_no, hhf_no⟩ := (hvs _ hnd_in).1 h1s hv1 hdom_ord
        have hvp_lt : memW s ((memW s (fr + 8)) + 48) < 2 ^ 64 :=
          memW_lt_two_pow_64 s ((memW s (fr + 8)) + 48)
        have hvp_b : memB post (memW s ((memW s (fr + 8)) + 48)) =
            memB s (memW s ((memW s (fr + 8)) + 48)) := by
          by_contra hne
          rcases heff.byte_frame (memW s ((memW s (fr + 8)) + 48)) hvp_lt hne with
            ⟨iv, hiv, hb1, hb2⟩ | ⟨hfg1, hfg2⟩ | ⟨hhf1, hhf2⟩
          · simp only [List.mem_singleton] at hiv; subst hiv
            apply hfg_no
            dsimp [InIvl, freeGapTo, Inside] at hfr_in hb1 hb2 ⊢
            omega
          · apply hfg_no
            dsimp [InIvl, freeGapTo]; dsimp [freeGap] at hfg1 hfg2
            omega
          · exact hhf_no ⟨hhf1, hhf2⟩
        rw [hvp_b]; exact hpay_lo
      · rw [rlpBytesLenPure_congr_ne_one hv1]; exact hpay_lo
    · intro hpos
      rw [hn56_eq] at hpos
      rw [hn48_eq]
      exact heff.memaddrs.symm ▸ hdom1 hpos
  · intro h2
    have h2s : memW s (memW s (fr + 8)) = 2 := hk_eq ▸ h2
    obtain ⟨hcl1, hcl_hi, hcb_in, hcb_disj, hcb_kb, hpay2⟩ := hk2_pay h2s
    have hcb_b := hcb_byte_eq (Or.inr h2s) hcl1 hcb_in
    refine ⟨by rw [hw32]; exact hcl1, by rw [hw32, hn40_eq (Or.inr h2s)]; exact hcl_hi,
      ⟨by rw [hw24]; exact hcb_in.1, by rw [hw24, hw32]; exact hcb_in.2.trans heff.hp_le⟩,
      fun o ho => by rw [hext_eq] at ho; rw [hw24, hw32]; exact hcb_disj o ho,
      fun gs hgs => by rw [hbuf_eq gs hgs, hw24, hw32]; exact hcb_kb gs hgs, ?_⟩
    rw [hw40, hw24, hw32, hcb_b, hpay2]



private theorem chainOK_bound_sp0_s {F : Type} {sp0 : Nat} {Nd : List Nat}
    {s : PanSemStateFiniteExact 64 F} {fr : Nat}
    (h : ChainOK sp0 Nd s fr) :
    fr = 0 ∨ (ValidRlpFrame s Nd fr ∧ fr + 48 ≤ sp0) := by
  induction h with
  | chainNil => exact Or.inl rfl
  | chainDone fr' hv hsp0 _ => exact Or.inr ⟨hv, hsp0⟩
  | chainStep fr' p hv _ hle _ ih =>
    rcases ih with rfl | ⟨_, hp_sp0⟩
    · omega
    · exact Or.inr ⟨hv, by omega⟩

private theorem chainOK_lift_disj_s {F : Type}
    {sp0 : Nat} {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {fr : Nat}
    {Rl : List Ivl} {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (hvs : NodeValuesSafe sp0 s Nd)
    (hext_eq : nodeExtents post Nd = nodeExtents s Nd)
    (hbuf_eq : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      bufferRegion post gs = bufferRegion s gs)
    (hw_nd_eq : ∀ n ∈ Nd, memW post n = memW s n ∧
      (1 ≤ memW s n → memW post (n + 40) = memW s (n + 40)) ∧
      (memW s n = 1 → memW post (n + 48) = memW s (n + 48) ∧ memW post (n + 56) = memW s (n + 56)))
    (heff : HeapByteEff s post Rl gw)
    (hfg_sp0 : globN s "scratch_ptr" ≤ sp0)
    (hfr_disj : ∀ g, ValidRlpFrame s Nd g → fr ≤ g → g + 48 ≤ sp0 →
      (∀ iv ∈ Rl, 0 < iv.2 → Disj iv (g, 48)) ∧
      (∀ iv ∈ Rl, 0 < iv.2 →
        (memW s (memW s (g + 8)) = 1 ∨ memW s (memW s (g + 8)) = 2) →
        Disj iv (memW s (g + 24), memW s (g + 32))) ∧
      (memW s (memW s (g + 8)) = 1 → memW s (memW s (g + 8) + 56) = 1 →
        ∀ iv ∈ Rl, 0 < iv.2 → ¬ InIvl (memW s (memW s (g + 8) + 48)) iv))
    (hch : ChainOK sp0 Nd s fr) :
    ChainOK sp0 Nd post fr := by
  have h264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hse : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  induction hch with
  | chainNil => exact ChainOK.chainNil post
  | chainDone g hv hg_sp0 hm0 =>
    obtain ⟨hd1, hd2, hd3⟩ := hfr_disj g hv le_rfl hg_sp0
    have hv' := validRlpFrame_of_heapByteEff_disj hAs hN hvs hext_eq hbuf_eq hw_nd_eq
      heff hd1 hd2 hd3 hfg_sp0 hv
    have hm0' : memW post (g + 0) = 0 := by
      obtain ⟨hg8, hg_in, _⟩ := hv
      dsimp [Inside] at hg_in
      rw [memW_eq_of_heapByteEff_disj hAs heff (by omega)
        (Or.inr ⟨by omega, by omega⟩) (by omega)
        (fun iv hiv hpos => by
          have hdj := hd1 iv hiv hpos
          dsimp [Disj] at hdj ⊢
          rcases hdj with h0 | h0 | h1 | h2 <;> omega)]
      exact hm0
    exact ChainOK.chainDone post g hv' hg_sp0 hm0'
  | chainStep g p hv hm0 hgp htail ih =>
    have hp_sp0 : g + 48 ≤ sp0 := by
      rcases chainOK_bound_sp0_s htail with rfl | ⟨_, hps⟩ <;> omega
    obtain ⟨hd1, hd2, hd3⟩ := hfr_disj g hv le_rfl hp_sp0
    have hv' := validRlpFrame_of_heapByteEff_disj hAs hN hvs hext_eq hbuf_eq hw_nd_eq
      heff hd1 hd2 hd3 hfg_sp0 hv
    have hm0' : memW post (g + 0) = p := by
      obtain ⟨hg8, hg_in, _⟩ := hv
      dsimp [Inside] at hg_in
      rw [memW_eq_of_heapByteEff_disj hAs heff (by omega)
        (Or.inr ⟨by omega, by omega⟩) (by omega)
        (fun iv hiv hpos => by
          have hdj := hd1 iv hiv hpos
          dsimp [Disj] at hdj ⊢
          rcases hdj with h0 | h0 | h1 | h2 <;> omega)]
      exact hm0
    have ih' := ih (fun q hq hqp hq_sp0 => hfr_disj q hq (by omega) hq_sp0)
    exact ChainOK.chainStep post g p hv' hm0' hgp ih'

private theorem chainOK_after_store16_s {F : Type}
    {sp0 : Nat} {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {top : Nat}
    {gw : List String}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (hvs : NodeValuesSafe sp0 s Nd)
    (hext_eq : nodeExtents post Nd = nodeExtents s Nd)
    (hbuf_eq : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      bufferRegion post gs = bufferRegion s gs)
    (heff : HeapByteEff s post [(top + 16, 8)] gw)
    (hfg_sp0 : globN s "scratch_ptr" ≤ sp0)
    (htop_ne : top ≠ 0)
    (hm16_post : memW post (top + 16) ≤ 16)
    (hch : ChainOK sp0 Nd s top) :
    ChainOK sp0 Nd post top := by
  have h264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hse : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hhl_sc : heapLimit ≤ scratchStart := by decide
  cases hch with
  | chainNil => exact absurd rfl htop_ne
  | chainDone _ hv htop_sp0 hm0 =>
    have hv' := validRlpFrame_after_store16_s hAs hN hvs hext_eq hbuf_eq heff htop_sp0 hfg_sp0 hm16_post hv
    have hm0' : memW post (top + 0) = 0 := by
      obtain ⟨ht8, ht_in, _⟩ := hv
      dsimp [Inside] at ht_in
      rw [memW_eq_of_heapByteEff_disj hAs heff (by omega)
        (Or.inr ⟨by omega, by omega⟩) (by omega)
        (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))]
      exact hm0
    exact ChainOK.chainDone post top hv' htop_sp0 hm0'
  | chainStep _ p hv hm0 htp htail =>
    have hp_sp0 : top + 48 ≤ sp0 := by
      rcases chainOK_bound_sp0_s htail with rfl | ⟨_, hps⟩ <;> omega
    have hv' := validRlpFrame_after_store16_s hAs hN hvs hext_eq hbuf_eq heff hp_sp0 hfg_sp0 hm16_post hv
    have hm0' : memW post (top + 0) = p := by
      obtain ⟨ht8, ht_in, _⟩ := hv
      dsimp [Inside] at ht_in
      rw [memW_eq_of_heapByteEff_disj hAs heff (by omega)
        (Or.inr ⟨by omega, by omega⟩) (by omega)
        (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))]
      exact hm0
    obtain ⟨ht8, ht_in, _⟩ := hv
    have hw_nd_eq : ∀ n ∈ Nd, memW post n = memW s n ∧
        (1 ≤ memW s n → memW post (n + 40) = memW s (n + 40)) ∧
        (memW s n = 1 → memW post (n + 48) = memW s (n + 48) ∧ memW post (n + 56) = memW s (n + 56)) := by
      intro n hn
      obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
      have hnd_off : ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) → memW post (n + off) = memW s (n + off) := by
        intro off hoff8 hoff_le
        have hal_off : Allocated s (n + off, 8) := by
          rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
          · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
        have hn8 : n % 8 = 0 := hw_n.1
        have hn_hi : n + nodeSize (memW s n) ≤ heapLimit := hin_n.2
        apply memW_eq_of_heapByteEff_disj hAs heff (by omega) hal_off
          (by omega)
        intro iv hiv _
        simp only [List.mem_singleton] at hiv; subst hiv
        have := hAs.2.2.2.1; have := hAs.2.2.2.2.1
        dsimp [Inside] at ht_in; exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
      refine ⟨by simpa using hnd_off 0 rfl (by have := nodeSize_ge32 (memW s n); omega),
        fun hk1 => hnd_off 40 (by decide) (by
          have hk3 := (hN.1 n hn).1
          unfold nodeSize; split_ifs <;> omega),
        fun h1 => ⟨hnd_off 48 (by decide) (by simp [nodeSize, h1]),
          hnd_off 56 (by decide) (by simp [nodeSize, h1])⟩⟩
    have htail' := chainOK_lift_disj_s hAs hN hvs hext_eq hbuf_eq hw_nd_eq heff hfg_sp0
      (fun g hg hpg hg_sp0 => by
        refine ⟨fun iv hiv _ => ?_, fun iv hiv _ h12 => ?_, fun h1 hv1 iv hiv _ hin => ?_⟩
        · simp only [List.mem_singleton] at hiv; subst hiv
          exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
        · simp only [List.mem_singleton] at hiv; subst hiv
          have hcb_in : Inside (memW s (g + 24), memW s (g + 32)) sourceBase (globN s "heap_ptr") := by
            rcases h12 with h1 | h2
            · exact (hg.2.2.2.2.2.2.2.2.2.1 h1).2.2.1
            · exact (hg.2.2.2.2.2.2.2.2.2.2.1 h2).2.2.1
          have := hAs.2.2.1; have := hAs.2.2.2.1; have := hAs.2.2.2.2.1
          dsimp [Inside] at ht_in hcb_in; exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
        · simp only [List.mem_singleton] at hiv; subst hiv
          have hdom1 := (hg.2.2.2.2.2.2.2.2.2.1 h1).2.2.2.2.2.2 (by omega)
          have hdom_ord : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW s (memW s (g + 8) + 48)))) := by
            rw [← hAs.1.memaddrs]; exact hdom1
          obtain ⟨_, _, hfg_no, _⟩ := (hvs _ hg.2.2.2.1).1 h1 hv1 hdom_ord
          apply hfg_no
          have := hAs.2.2.2.2.1
          dsimp [InIvl, freeGapTo, Inside] at ht_in hin ⊢; omega)
      htail
    exact ChainOK.chainStep post top p hv' hm0' htp htail'



private theorem nodeHeap_of_store16_s {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {top : Nat}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (hin_top : Inside (top, 48) (globN s "scratch_ptr") scratchEnd)
    (heff : HeapByteEff s post [(top + 16, 8)] []) :
    NodeHeap post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhl_sc : heapLimit ≤ scratchStart := by decide
  have hfmp_le := hAs.2.2.2.1
  have hsp_ge := hAs.2.2.2.2.1
  have hrlp_len : ∀ n ∈ Nd, memW post (n + 16) < 2 ^ 40 := by
    intro n hn
    obtain ⟨_, hal_n, hin_n, hw_n, _, _, _, hrlp_s, _⟩ := hN.1 n hn
    have hsz := nodeSize_ge32 (memW s n)
    have hal_16 : Allocated s (n + 16, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    have hn8 : n % 8 = 0 := hw_n.1
    have hw16_eq : memW post (n + 16) = memW s (n + 16) := by
      apply memW_eq_of_heapByteEff_disj hAs heff (by omega) hal_16
        (by have := hin_n.2; dsimp [nodeIvl] at this; omega)
      intro iv hiv _; simp only [List.mem_singleton] at hiv; subst hiv
      have := hin_n.2; dsimp [nodeIvl, Inside] at this hin_top ⊢
      exact Or.inr (Or.inr (Or.inl (by omega)))
    rw [hw16_eq]; exact hrlp_s
  have hag : AllocatorGrows s post := ⟨heff.hp_le, heff.sp_le⟩
  apply nodeHeap_congr_cache hAs.1 heff.arena.1 hag hN ?_ hrlp_len ?_
  · intro n hn k hk hk1 hk2 hk3
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
    have hn8 : n % 8 = 0 := hw_n.1
    have hsz : 8 * k + 8 ≤ nodeSize (memW s n) := by
      have : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> decide
      omega
    have hal_k : Allocated s (n + 8 * k, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    exact memW_eq_of_heapByteEff_disj hAs heff (by omega) hal_k
      (by have := hin_n.2; dsimp [nodeIvl] at this; omega)
      (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        have := hin_n.2; dsimp [nodeIvl, Inside] at this hin_top ⊢
        exact Or.inr (Or.inr (Or.inl (by omega))))
  · intro n hn h12 hlen0 j hj
    obtain ⟨_, _, _, _, _, _, hkey_n, _⟩ := hN.1 n hn
    rcases hkey_n h12 with hz | ⟨_, hal_k, hin_k, _⟩
    · exact absurd hz hlen0
    · dsimp [Inside] at hin_k hin_top
      have hb_lt : memW s (n + 32) + j < 2 ^ 64 := by omega
      by_contra hne
      rcases heff.byte_frame (memW s (n + 32) + j) hb_lt hne with ⟨iv, hiv, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [List.mem_singleton] at hiv; subst hiv; dsimp at h1 h2; omega
      · have hdj := P3MptSet.disj_allocated_freeGap hAs.2 hal_k
        dsimp [freeGap] at hdj h1 h2
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
      · have hdj := P3MptSet.disj_allocated_heapFree hAs.2 hal_k
        dsimp [heapFree] at hdj h1 h2
        rcases hdj with h0 | h0 | hd1 | hd2 <;> omega

private theorem nodeValuesSafe_of_store16_s {F : Type}
    {sp0 : Nat} {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat} {top : Nat}
    (hAs : ArenaReady s) (hN : NodeHeap s Nd)
    (hin_top : Inside (top, 48) (globN s "scratch_ptr") scratchEnd)
    (heff : HeapByteEff s post [(top + 16, 8)] [])
    (hvs : NodeValuesSafe sp0 s Nd) :
    NodeValuesSafe sp0 post Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhl_sc : heapLimit ≤ scratchStart := by decide
  have hfmp_le := hAs.2.2.2.1
  have hsp_ge := hAs.2.2.2.2.1
  have hbuf_eq : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion post gs = bufferRegion s gs := by
    intro gs hgs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl
    · unfold bufferRegion globN; rw [← heff.globals (ofString "keccak_pad") (by decide)]
    · unfold bufferRegion globN; rw [← heff.globals (ofString "keccak_st") (by decide)]
  have hw_nd : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 →
      off + 8 ≤ nodeSize (memW s n) → memW post (n + off) = memW s (n + off) := by
    intro n hn off hoff8 hoff_lt
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
    have hn8 : n % 8 = 0 := hw_n.1
    have hal_off : Allocated s (n + off, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    exact memW_eq_of_heapByteEff_disj hAs heff (by omega) hal_off
      (by have := hin_n.2; dsimp [nodeIvl] at this; omega)
      (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        have := hin_n.2; dsimp [nodeIvl, Inside] at this hin_top ⊢
        exact Or.inr (Or.inr (Or.inl (by omega))))
  have hfg_eq : freeGapTo sp0 post = freeGapTo sp0 s := by simp [freeGapTo, heff.fp_eq]
  have hhf_sub : ∀ b, InIvl b (heapFree post) → InIvl b (heapFree s) := by
    intro b hb; dsimp [InIvl, heapFree] at hb ⊢; have := heff.hp_le; omega
  intro n hn
  have hsz0 := nodeSize_ge32 (memW s n)
  have hk_eq : memW post n = memW s n := by simpa using hw_nd n hn 0 rfl (by omega)
  obtain ⟨h1, h3⟩ := hvs n hn
  refine ⟨?_, ?_⟩
  · intro hk1 hv1 hdom
    have hk1_s : memW s n = 1 := hk_eq ▸ hk1
    have hsz1 : nodeSize (memW s n) = 64 := by simp [nodeSize, hk1_s]
    have h48 := hw_nd n hn 48 (by decide) (by omega)
    have h56 := hw_nd n hn 56 (by decide) (by omega)
    rw [h48] at hdom ⊢; rw [hfg_eq]
    obtain ⟨hnc_no, hkc_no, hfg_no, hhf_no⟩ := h1 hk1_s (h56 ▸ hv1) hdom
    refine ⟨hnc_no, fun gs hgs hpos => by rw [hbuf_eq gs hgs] at hpos ⊢; exact hkc_no gs hgs hpos,
      hfg_no, fun h => hhf_no (hhf_sub _ h)⟩
  · intro hk3 hv1 hdom
    have hk3_s : memW s n = 3 := hk_eq ▸ hk3
    have hsz3 : nodeSize (memW s n) = 176 := by simp [nodeSize, hk3_s]
    have h160 := hw_nd n hn 160 (by decide) (by omega)
    have h168 := hw_nd n hn 168 (by decide) (by omega)
    rw [h160] at hdom ⊢; rw [hfg_eq]
    obtain ⟨hnc_no, hkc_no, hfg_no, hhf_no⟩ := h3 hk3_s (h168 ▸ hv1) hdom
    refine ⟨hnc_no, fun gs hgs hpos => by rw [hbuf_eq gs hgs] at hpos ⊢; exact hkc_no gs hgs hpos,
      hfg_no, fun h => hhf_no (hhf_sub _ h)⟩

private theorem eval_fillSearch_none_s {F : Type}
    {sp0 : Nat} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {topw ndw kw : BitVec 64}
    (hc : s.code = originalRuntimeCode)
    (hAR : ArenaReady s) (hN : NodeHeap s Nd)
    (hKS : KeccakBufsSafe s Nd) (hvs : NodeValuesSafe sp0 s Nd)
    (hsp_le : globN s "scratch_ptr" ≤ sp0) (hsp0_hi : sp0 ≤ scratchEnd)
    (htop_ne : topw.toNat ≠ 0)
    (hv_top : ValidRlpFrame s Nd topw.toNat)
    (hch : ChainOK sp0 Nd s topw.toNat)
    (hnd_eq : memW s (topw.toNat + 8) = ndw.toNat)
    (hkw_eq : memW s ndw.toNat = kw.toNat)
    (hl_top : s.locals.lookup (ofString "top") = some (.val (.word topw)))
    (hl_nd : s.locals.lookup (ofString "nd") = some (.val (.word ndw)))
    (hl_k : s.locals.lookup (ofString "k") = some (.val (.word kw)))
    (hl_c : s.locals.lookup (ofString "child") = some (.val (.word 0)))
    (hl_f : s.locals.lookup (ofString "found") = some (.val (.word 0)))
    (hnone : (evaluateHOLFiniteState s fillSearch).1 = none) :
    let post := (evaluateHOLFiniteState s fillSearch).2
    ∃ (cw fw : BitVec 64),
      post.code = originalRuntimeCode ∧
      ArenaReady post ∧
      post.globals = s.globals ∧
      NodeHeap post Nd ∧
      KeccakBufsSafe post Nd ∧
      NodeValuesSafe sp0 post Nd ∧
      ValidRlpFrame post Nd topw.toNat ∧
      ChainOK sp0 Nd post topw.toNat ∧
      memW post (topw.toNat + 8) = ndw.toNat ∧
      (fw ≠ 0 → cw.toNat ∈ Nd ∧ 1 ≤ memW post cw.toNat ∧ memW post cw.toNat ≤ 3) ∧
      post.locals.lookup (ofString "top") = some (.val (.word topw)) ∧
      post.locals.lookup (ofString "nd") = some (.val (.word ndw)) ∧
      post.locals.lookup (ofString "child") = some (.val (.word cw)) ∧
      post.locals.lookup (ofString "found") = some (.val (.word fw)) := by
  intro post; dsimp only [post]
  have hse_he : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhe_264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhl_264 : heapLimit ≤ 2 ^ 64 := by decide
  have htop8 := hv_top.1
  have hin_top := hv_top.2.1
  have hw_top := hv_top.2.2.1
  have hnd_in_s := hv_top.2.2.2.1
  have hm16_le := hv_top.2.2.2.2.2.2.1
  have hnd_in : ndw.toNat ∈ Nd := hnd_eq ▸ hnd_in_s
  have htop_hi_he : topw.toNat + 48 ≤ heapEnd := by dsimp [Inside] at hin_top; omega
  have htop_sp0 : topw.toNat + 48 ≤ sp0 := by
    rcases chainOK_bound_sp0_s hch with h0 | ⟨_, hle⟩
    · exact absurd h0 htop_ne
    · exact hle
  have hfs_eq : fillSearch =
      .ite (.cmp .equal (.var .local (ofString "k")) (.const 2))
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"), .const 16])) (.const 0))
          (.seq
            (.store (.op .add [.var .local (ofString "top"), .const 16]) (.const 1))
            (.seq
              (.assign .local (ofString "child") (.load .one (.op .add [.var .local (ofString "nd"), .const 48])))
              (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
                [.var .local (ofString "child")])))
          .skip)
        (.ite (.cmp .equal (.var .local (ofString "k")) (.const 3))
          (.dec (ofString "i") .one (.load .one (.op .add [.var .local (ofString "top"), .const 16]))
            (.seq (.while fillScanCond fillScanBody)
              (.store (.op .add [.var .local (ofString "top"), .const 16]) (.var .local (ofString "i")))))
          .skip) := rfl
  rw [hfs_eq] at hnone ⊢
  rw [evaluateHOLFiniteState_ite] at hnone ⊢
  have hcmp2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "k")) (.const 2)) =
      some (.val (.word (if kw = 2 then 1 else 0))) := by
    simp [evalHOLExact, hl_k, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp2] at hnone ⊢; dsimp only at hnone ⊢
  by_cases hkw2 : kw = 2
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_pos hkw2, if_neg h10] at hnone ⊢
    have hk2 : memW s ndw.toNat = 2 := by rw [hkw_eq, hkw2]; rfl
    rw [evaluateHOLFiniteState_ite] at hnone ⊢
    obtain ⟨m16w, hld16, hm16_nat⟩ := eval_load_memW_of_wordsOK (s := s) (base := topw) (off := 16)
      (len := 48) hw_top (by decide) (by decide) (by omega)
      (e := .op .add [.var .local (ofString "top"), .const 16])
      (by simp [evalHOLExact, evalListHOLExact, hl_top, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
    have hcmp16 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"), .const 16])) (.const 0)) =
        some (.val (.word (if m16w = 0 then 1 else 0))) := by
      unfold evalHOLExact; rw [hld16]; simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp16] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hm16_z : m16w = 0
    · rw [if_pos hm16_z, if_neg h10] at hnone ⊢
      obtain ⟨hst_none, hst_loc, hst_glob, hm16_st, _, heff_st⟩ :=
        eval_store_memW_at (s := s) (base := topw) (w := 1) (off := 16) (len := 48)
          (Rl := [(topw.toNat + 16, 8)]) (gw := []) hAR hw_top (by decide) (by decide) htop_hi_he
          ⟨(topw.toNat + 16, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
          (dstExp := .op .add [.var .local (ofString "top"), .const 16]) (valExp := .const 1)
          (by simp [evalHOLExact, evalListHOLExact, hl_top, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
          rfl
      obtain ⟨_, hn_rest, hseq1⟩ := fillSeq_none _ _ _ hnone
      rw [hseq1]; clear hnone hseq1
      set s1 := (evaluateHOLFiniteState s (.store (.op .add [.var .local (ofString "top"), .const 16]) (.const 1))).2
      have hs1_c : s1.code = originalRuntimeCode :=
        (evaluateHOLFiniteState_metadata s (.store (.op .add [.var .local (ofString "top"), .const 16]) (.const 1))).1.trans hc
      obtain ⟨hN_s1, hext_s1⟩ := nodeHeap_of_store16_s hAR hN hin_top heff_st
      have hbuf_s1 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
          bufferRegion s1 gs = bufferRegion s gs :=
        fun gs _ => by unfold bufferRegion globN; rw [hst_glob]
      have hag_s1 : AllocatorGrows s s1 := ⟨heff_st.hp_le, heff_st.sp_le⟩
      have hKS_s1 : KeccakBufsSafe s1 Nd := by
        intro gs hgs; rw [hbuf_s1 gs hgs]
        refine ⟨(hKS gs hgs).1.elim Or.inl (fun h => Or.inr (hag_s1.allocated h)), ?_⟩
        intro o ho; rw [hext_s1] at ho; exact (hKS gs hgs).2 o ho
      have hvs_s1 : NodeValuesSafe sp0 s1 Nd := nodeValuesSafe_of_store16_s hAR hN hin_top heff_st hvs
      have hv_s1 : ValidRlpFrame s1 Nd topw.toNat :=
        validRlpFrame_after_store16_s hAR hN hvs hext_s1 hbuf_s1 heff_st htop_sp0 hsp_le
          (by rw [hm16_st]; decide) hv_top
      have hch_s1 : ChainOK sp0 Nd s1 topw.toNat :=
        chainOK_after_store16_s hAR hN hvs hext_s1 hbuf_s1 heff_st hsp_le htop_ne
          (by rw [hm16_st]; decide) hch
      obtain ⟨_, hal_nd_s1, hin_nd_s1, hw_nd_s1, hch2_s1, _⟩ := hN_s1.1 ndw.toNat hnd_in
      obtain ⟨_, hal_nd_s, hin_nd_s, hw_nd_s, _⟩ := hN.1 ndw.toNat hnd_in
      have hk2_s1 : memW s1 ndw.toNat = 2 := by
        have hsz_s := nodeSize_ge32 (memW s ndw.toNat)
        have hnd_al8 : Allocated s (ndw.toNat + 0, 8) := by
          rcases hal_nd_s with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
          · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
        have hmw_eq : memW s1 (ndw.toNat + 0) = memW s (ndw.toNat + 0) :=
          memW_eq_of_heapByteEff_disj hAR heff_st hw_nd_s.1 hnd_al8
            (by have := hin_nd_s.2; dsimp [nodeIvl] at this; omega)
            (fun iv hiv _ => by
              simp only [List.mem_singleton] at hiv; subst hiv
              have := hin_nd_s.2; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
              have : heapLimit ≤ scratchStart := by decide
              exact Or.inr (Or.inr (Or.inl (by dsimp [nodeIvl, Inside] at *; omega))))
        simpa using hmw_eq.trans hk2
      have hsz2 : nodeSize (memW s1 ndw.toNat) = 56 := by simp [nodeSize, hk2_s1]
      obtain ⟨chw, hld48, hchw_nat⟩ := eval_load_memW_of_wordsOK (s := s1) (base := ndw) (off := 48)
        (len := nodeSize (memW s1 ndw.toNat)) hw_nd_s1 (by decide) (by omega)
        (by have := hin_nd_s1.2; dsimp [nodeIvl] at this; omega)
        (e := .op .add [.var .local (ofString "nd"), .const 48])
        (by
          have hl_nd_s1 : s1.locals.lookup (ofString "nd") = some (.val (.word ndw)) := by
            rw [hst_loc]; exact hl_nd
          simp [evalHOLExact, evalListHOLExact, hl_nd_s1, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
      have hch_root : RootIn Nd chw.toNat := by rw [hchw_nat]; exact hch2_s1 hk2_s1
      have hev_a1 : evaluateHOLFiniteState s1
          (.assign .local (ofString "child") (.load .one (.op .add [.var .local (ofString "nd"), .const 48]))) =
          (none, setVarHOLFinite (ofString "child") (.val (.word chw)) s1) :=
        assign_local_word_eq_sc s1 (ofString "child") _ chw 0 (by rw [hst_loc]; exact hl_c) hld48
      set s2 := setVarHOLFinite (ofString "child") (.val (.word chw)) s1
      have hseq2 : ∀ p3, evaluateHOLFiniteState s1
          (.seq (.assign .local (ofString "child") (.load .one (.op .add [.var .local (ofString "nd"), .const 48]))) p3) =
          evaluateHOLFiniteState s2 p3 := by
        intro p3; rw [evaluateHOLFiniteState_seq_line780, hev_a1]
      rw [hseq2] at hn_rest ⊢
      have hl_c2 : s2.locals.lookup (ofString "child") = some (.val (.word chw)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hl_f2 : s2.locals.lookup (ofString "found") = some (.val (.word 0)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_loc, hl_f,
          show ofString "child" ≠ ofString "found" by decide]
      obtain ⟨fw, hfw_nz, _, hs3_eq⟩ :=
        eval_call_local__node_needs_rlp s2 Nd "found" (.var .local (ofString "child")) chw
          hs1_c hN_s1 ⟨0, hl_f2⟩ hch_root (by simp [evalHOLExact, hl_c2]) hn_rest
      set s3 := (evaluateHOLFiniteState s2
        (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
          [.var .local (ofString "child")])).2
      have hm8_s1 : memW s1 (topw.toNat + 8) = ndw.toNat :=
        (memW_eq_of_heapByteEff_disj hAR heff_st (by omega)
          (Or.inr ⟨by have := hAR.2.2.2.1; have := hAR.2.2.2.2.1; dsimp [Inside] at hin_top ⊢; omega,
                   by dsimp [Inside] at hin_top ⊢; omega⟩)
          (by dsimp [Inside] at hin_top; omega)
          (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))).trans hnd_eq
      have hs3_from_s1 : s3 = { s1 with locals := s3.locals, clock := s3.clock } := by
        have hloc_s3 := congrArg (·.locals) hs3_eq
        dsimp [s2, setVarHOLFinite] at hloc_s3
        exact hs3_eq.trans (by dsimp [s2, setVarHOLFinite]; rw [← hloc_s3])
      have hch_s3 : ChainOK sp0 Nd s3 topw.toNat := by
        rw [hs3_from_s1]; exact chainOK_with_locals_clock s1 s3.locals s3.clock sp0 Nd hch_s1
      refine ⟨chw, fw, by rw [hs3_eq]; exact hs1_c,
        by rw [hs3_from_s1]; exact ⟨guestInv_with_locals_clock s1 _ _ heff_st.arena.1, heff_st.arena.2⟩,
        by rw [hs3_eq]; exact hst_glob,
        by rw [hs3_eq]; exact hN_s1,
        by rw [hs3_eq]; exact hKS_s1,
        by rw [hs3_eq]; exact hvs_s1,
        by rw [hs3_from_s1]; exact hv_s1,
        hch_s3,
        by rw [hs3_eq]; exact hm8_s1,
        fun hnz => by rw [hs3_eq]; exact hfw_nz hnz, ?_, ?_, ?_, ?_⟩
      · rw [hs3_eq]; simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_loc, hl_top,
          show ofString "found" ≠ ofString "top" by decide,
          show ofString "child" ≠ ofString "top" by decide]
      · rw [hs3_eq]; simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_loc, hl_nd,
          show ofString "found" ≠ ofString "nd" by decide,
          show ofString "child" ≠ ofString "nd" by decide]
      · rw [hs3_eq]; simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "found" ≠ ofString "child" by decide]
      · rw [hs3_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [if_neg hm16_z, if_pos rfl, evaluateHOLFiniteState_skip]
      exact ⟨0, 0, hc, hAR, rfl, hN, hKS, hvs, hv_top, hch, hnd_eq,
        fun h => absurd rfl h, hl_top, hl_nd, hl_c, hl_f⟩
  · rw [if_neg hkw2, if_pos rfl] at hnone ⊢
    rw [evaluateHOLFiniteState_ite] at hnone ⊢
    have hcmp3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.var .local (ofString "k")) (.const 3)) =
        some (.val (.word (if kw = 3 then 1 else 0))) := by
      simp [evalHOLExact, hl_k, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp3] at hnone ⊢; dsimp only at hnone ⊢
    by_cases hkw3 : kw = 3
    · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_pos hkw3, if_neg h10] at hnone ⊢
      have hk3 : memW s ndw.toNat = 3 := by rw [hkw_eq, hkw3]; rfl
      obtain ⟨iw, hld16, hiw_nat⟩ := eval_load_memW_of_wordsOK (s := s) (base := topw) (off := 16)
        (len := 48) hw_top (by decide) (by decide) (by omega)
        (e := .op .add [.var .local (ofString "top"), .const 16])
        (by simp [evalHOLExact, evalListHOLExact, hl_top, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
      have hiw_le : iw.toNat ≤ 16 := by rw [hiw_nat]; exact hm16_le
      rw [dec_eval_word_eq_sc s (ofString "i") _ iw _ hld16] at hnone ⊢
      dsimp only at hnone ⊢
      set si := setVarHOLFinite (ofString "i") (.val (.word iw)) s
      obtain ⟨hwh_none, hst_none_in, hseq_wh⟩ := fillSeq_none si _ _ hnone
      rw [hseq_wh]; clear hnone hseq_wh
      obtain ⟨iw', cw', fw', hiw'_le, hfw'_inv, hwh_st⟩ :=
        eval_fillScan_loop_none (16 - iw.toNat) si Nd ndw iw 0 0 hc hN hnd_in hk3 hiw_le rfl
          (fun h => absurd rfl h)
          (by simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_nd, show ofString "i" ≠ ofString "nd" by decide])
          (by simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          (by simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_c, show ofString "i" ≠ ofString "child" by decide])
          (by simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_f, show ofString "i" ≠ ofString "found" by decide])
          hwh_none
      set sw := (evaluateHOLFiniteState si (.while fillScanCond fillScanBody)).2
      have hsw_from_s : sw = { s with locals := sw.locals, clock := sw.clock } := by
        have hloc_sw := congrArg (·.locals) hwh_st
        dsimp [si, setVarHOLFinite] at hloc_sw
        exact hwh_st.trans (by dsimp [si, setVarHOLFinite]; rw [← hloc_sw])
      have hrefl_sw : HeapByteEff s sw [(topw.toNat + 16, 8)] [] := by
        rw [hsw_from_s]
        exact (HeapByteEff.refl hAR [(topw.toNat + 16, 8)] []).locals_clock sw.locals sw.clock
      have hsw_AR : ArenaReady sw := hrefl_sw.arena
      have hsw_W_top : WordsOK sw (topw.toNat, 48) :=
        P3MptSet.wordsOK_transfer hAR.1 hsw_AR.1 hw_top
      have hsw_top : sw.locals.lookup (ofString "top") = some (.val (.word topw)) := by
        rw [hwh_st]
        simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_top,
          show ofString "found" ≠ ofString "top" by decide,
          show ofString "i" ≠ ofString "top" by decide,
          show ofString "child" ≠ ofString "top" by decide]
      have hsw_i : sw.locals.lookup (ofString "i") = some (.val (.word iw')) := by
        rw [hwh_st]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "found" ≠ ofString "i" by decide]
      obtain ⟨hst_none, hst_loc, hst_glob, hm16_st, _, heff_st_raw⟩ :=
        eval_store_memW_at (s := sw) (base := topw) (w := iw') (off := 16) (len := 48)
          (Rl := [(topw.toNat + 16, 8)]) (gw := []) hsw_AR hsw_W_top (by decide) (by decide) htop_hi_he
          ⟨(topw.toNat + 16, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
          (dstExp := .op .add [.var .local (ofString "top"), .const 16]) (valExp := .var .local (ofString "i"))
          (by simp [evalHOLExact, evalListHOLExact, hsw_top, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
          (by simp [evalHOLExact, hsw_i])
      set st := (evaluateHOLFiniteState sw
        (.store (.op .add [.var .local (ofString "top"), .const 16]) (.var .local (ofString "i")))).2
      have heff_s_st : HeapByteEff s st [(topw.toNat + 16, 8)] [] := hrefl_sw.trans heff_st_raw
      set s_fin := { st with locals := HolFiniteMapExact.resVarEq st.locals (ofString "i", s.locals.lookup (ofString "i")) }
      have heff_s_sfin : HeapByteEff s s_fin [(topw.toNat + 16, 8)] [] :=
        heff_s_st.locals_clock s_fin.locals s_fin.clock
      have hsfin_glob : s_fin.globals = s.globals := by
        dsimp [s_fin]; rw [hst_glob, hsw_from_s]
      have hsfin_c : s_fin.code = originalRuntimeCode := by
        dsimp [s_fin]
        exact (evaluateHOLFiniteState_metadata sw _).1.trans (by rw [hsw_from_s]; exact hc)
      obtain ⟨hN_st, hext_st⟩ := nodeHeap_of_store16_s hAR hN hin_top heff_s_sfin
      have hbuf_st : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
          bufferRegion s_fin gs = bufferRegion s gs :=
        fun gs _ => by unfold bufferRegion globN; rw [hsfin_glob]
      have hag_st : AllocatorGrows s s_fin := ⟨heff_s_sfin.hp_le, heff_s_sfin.sp_le⟩
      have hKS_st : KeccakBufsSafe s_fin Nd := by
        intro gs hgs; rw [hbuf_st gs hgs]
        refine ⟨(hKS gs hgs).1.elim Or.inl (fun h => Or.inr (hag_st.allocated h)), ?_⟩
        intro o ho; rw [hext_st] at ho; exact (hKS gs hgs).2 o ho
      have hvs_st : NodeValuesSafe sp0 s_fin Nd := nodeValuesSafe_of_store16_s hAR hN hin_top heff_s_sfin hvs
      have hm16_sfin : memW s_fin (topw.toNat + 16) ≤ 16 := by
        change memW st (topw.toNat + 16) ≤ 16; rw [hm16_st]; exact hiw'_le
      have hv_st : ValidRlpFrame s_fin Nd topw.toNat :=
        validRlpFrame_after_store16_s hAR hN hvs hext_st hbuf_st heff_s_sfin htop_sp0 hsp_le hm16_sfin hv_top
      have hch_st : ChainOK sp0 Nd s_fin topw.toNat :=
        chainOK_after_store16_s hAR hN hvs hext_st hbuf_st heff_s_sfin hsp_le htop_ne hm16_sfin hch
      have hm8_st : memW s_fin (topw.toNat + 8) = ndw.toNat :=
        (memW_eq_of_heapByteEff_disj hAR heff_s_sfin (by omega)
          (Or.inr ⟨by have := hAR.2.2.2.1; have := hAR.2.2.2.2.1; dsimp [Inside] at hin_top ⊢; omega,
                   by dsimp [Inside] at hin_top ⊢; omega⟩)
          (by dsimp [Inside] at hin_top; omega)
          (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))).trans hnd_eq
      have hcw_kind : fw' ≠ 0 → cw'.toNat ∈ Nd ∧ 1 ≤ memW s_fin cw'.toNat ∧ memW s_fin cw'.toNat ≤ 3 := by
        intro hnz
        obtain ⟨hc_in, hc1, hc3⟩ := hfw'_inv hnz
        obtain ⟨_, hal_c, hin_c, hw_c, _⟩ := hN.1 cw'.toNat hc_in
        have hsz_c := nodeSize_ge32 (memW s cw'.toNat)
        have hc_al8 : Allocated s (cw'.toNat + 0, 8) := by
          rcases hal_c with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
          · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
        have hmc' : memW s_fin cw'.toNat = memW s cw'.toNat := by
          simpa using memW_eq_of_heapByteEff_disj (a := cw'.toNat + 0) hAR heff_s_sfin hw_c.1 hc_al8
            (by have := hin_c.2; dsimp [nodeIvl] at this; omega)
            (fun iv hiv _ => by
              simp only [List.mem_singleton] at hiv; subst hiv
              have := hin_c.2; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
              have : heapLimit ≤ scratchStart := by decide
              exact Or.inr (Or.inr (Or.inl (by dsimp [nodeIvl, Inside] at *; omega))))
        rw [hmc']; exact ⟨hc_in, hc1, hc3⟩
      refine ⟨cw', fw', hsfin_c, heff_s_sfin.arena, hsfin_glob, hN_st, hKS_st, hvs_st, hv_st, hch_st,
        hm8_st, hcw_kind, ?_, ?_, ?_, ?_⟩
      · change (HolFiniteMapExact.resVarEq st.locals (ofString "i", s.locals.lookup (ofString "i"))).lookup (ofString "top") = _
        rw [R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide), hst_loc, hsw_top]
      · change (HolFiniteMapExact.resVarEq st.locals (ofString "i", s.locals.lookup (ofString "i"))).lookup (ofString "nd") = _
        rw [R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide), hst_loc, hwh_st]
        simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_nd,
          show ofString "found" ≠ ofString "nd" by decide,
          show ofString "i" ≠ ofString "nd" by decide,
          show ofString "child" ≠ ofString "nd" by decide]
      · change (HolFiniteMapExact.resVarEq st.locals (ofString "i", s.locals.lookup (ofString "i"))).lookup (ofString "child") = _
        rw [R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide), hst_loc, hwh_st]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "found" ≠ ofString "child" by decide,
          show ofString "i" ≠ ofString "child" by decide]
      · change (HolFiniteMapExact.resVarEq st.locals (ofString "i", s.locals.lookup (ofString "i"))).lookup (ofString "found") = _
        rw [R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide), hst_loc, hwh_st]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [if_neg hkw3, if_pos rfl, evaluateHOLFiniteState_skip]
      exact ⟨0, 0, hc, hAR, rfl, hN, hKS, hvs, hv_top, hch, hnd_eq,
        fun h => absurd rfl h, hl_top, hl_nd, hl_c, hl_f⟩



private theorem eval_fillTail_none_s
    (hbeg_spec : ∀ {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (frExp nodeExp : ExpHOL 64) (frw nodew : BitVec 64),
      s.code = originalRuntimeCode → ArenaReady s → NodeHeap s Nd →
      KeccakBufsSafe s Nd → NodeValuesSafe sp0 s Nd →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
        some (.val (.word frw)) →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
        some (.val (.word nodew)) →
      Inside (frw.toNat, 48) (globN s "scratch_ptr") scratchEnd →
      frw.toNat + 48 ≤ sp0 →
      WordsOK s (frw.toNat, 48) →
      (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
        Disj (frw.toNat, 48) (bufferRegion s gs)) →
      nodew.toNat ∈ Nd →
      1 ≤ memW s nodew.toNat →
      memW s (frw.toNat + 8) = nodew.toNat →
      memW s (frw.toNat + 16) ≤ 16 →
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_begin") [frExp, nodeExp])).1 = none →
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
      ValidRlpFrame post Nd frw.toNat)
    (hfin_spec : ∀ {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (frExp nodeExp : ExpHOL 64) (frw nodew : BitVec 64),
      s.code = originalRuntimeCode → ArenaReady s → NodeHeap s Nd →
      KeccakBufsSafe s Nd → NodeValuesSafe sp0 s Nd →
      globN s "scratch_ptr" ≤ sp0 →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
        some (.val (.word frw)) →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
        some (.val (.word nodew)) →
      ValidRlpFrame s Nd frw.toNat →
      memW s (frw.toNat + 8) = nodew.toNat →
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_finish") [frExp, nodeExp])).1 = none →
      let post := (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_finish") [frExp, nodeExp])).2
      post.locals = s.locals ∧
      ∃ totLen : Nat,
        1 ≤ totLen ∧
        globN s "heap_ptr" + totLen ≤ heapLimit ∧
        (∀ o ∈ nodeExtents s Nd, Disj (globN s "heap_ptr", totLen) o) ∧
        HeapByteEff s post
          ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] ∧
        globN s "heap_ptr" < globN post "heap_ptr" ∧
        NodeHeap post Nd ∧
        nodeExtents post Nd = nodeExtents s Nd ∧
        KeccakBufsSafe post Nd ∧
        NodeValuesSafe sp0 post Nd ∧
        memW post (nodew.toNat + 8) = globN s "heap_ptr" ∧
        memW post (nodew.toNat + 16) = totLen ∧
        (∀ n ∈ Nd, n ≠ nodew.toNat → memW post (n + 8) = memW s (n + 8) ∧
          memW post (n + 16) = memW s (n + 16)) ∧
        (∀ n ∈ Nd, memW post n = memW s n ∧
          (1 ≤ memW s n → memW post (n + 40) = memW s (n + 40)) ∧
          (memW s n = 1 → memW post (n + 48) = memW s (n + 48) ∧
            memW post (n + 56) = memW s (n + 56))))
    {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
    (topw ndw cw fw : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hsp_le : globN s "scratch_ptr" ≤ sp0) (hsp0_hi : sp0 ≤ scratchEnd)
    (hN : NodeHeap s Nd) (hKS : KeccakBufsSafe s Nd) (hvs : NodeValuesSafe sp0 s Nd)
    (hkc_sp0 : ∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      0 < (bufferRegion s gs).2 →
      (bufferRegion s gs).1 + (bufferRegion s gs).2 ≤ globN s "heap_ptr" ∨
        sp0 ≤ (bufferRegion s gs).1)
    (hv_top : ValidRlpFrame s Nd topw.toNat)
    (hch : ChainOK sp0 Nd s topw.toNat)
    (htop_ne : topw.toNat ≠ 0)
    (hnd_eq : memW s (topw.toNat + 8) = ndw.toNat)
    (hcw_kind : fw ≠ 0 → cw.toNat ∈ Nd ∧ 1 ≤ memW s cw.toNat ∧ memW s cw.toNat ≤ 3)
    (hl_top : s.locals.lookup (ofString "top") = some (.val (.word topw)))
    (hl_nd : s.locals.lookup (ofString "nd") = some (.val (.word ndw)))
    (hl_c : s.locals.lookup (ofString "child") = some (.val (.word cw)))
    (hl_f : s.locals.lookup (ofString "found") = some (.val (.word fw)))
    (hnone : (evaluateHOLFiniteState s fillTail).1 = none) :
    let post := (evaluateHOLFiniteState s fillTail).2
    ArenaReady post ∧
    AllocatorGrows s post ∧
    (globN s "heap_ptr" < globN post "heap_ptr" ∨
      globN post "scratch_ptr" < globN s "scratch_ptr") ∧
    globN post "scratch_ptr" ≤ sp0 ∧
    NodeHeap post Nd ∧
    KeccakBufsSafe post Nd ∧
    NodeValuesSafe sp0 post Nd ∧
    (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      0 < (bufferRegion post gs).2 →
      (bufferRegion post gs).1 + (bufferRegion post gs).2 ≤ globN post "heap_ptr" ∨
        sp0 ≤ (bufferRegion post gs).1) ∧
    ChainOK sp0 Nd post (locN post "top") ∧
    (∀ x, x ≠ ofString "top" → post.locals.lookup x = s.locals.lookup x) := by
  have h264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hse_he : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhl_sc : heapLimit ≤ scratchStart := by decide
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  intro post; dsimp only [post]
  have hft_eq : fillTail =
      .ite (.cmp .notEqual (.var .local (ofString "found")) (.const 0))
        (.decCall (ofString "cf") .one (ofString "scratch_alloc") [.const 48]
          (.seq
            (.store (.op .add [.var .local (ofString "cf"), .const 0]) (.var .local (ofString "top")))
            (.seq
              (.store (.op .add [.var .local (ofString "cf"), .const 8]) (.var .local (ofString "child")))
              (.seq
                (.store (.op .add [.var .local (ofString "cf"), .const 16]) (.const 0))
                (.seq
                  (.call (some (none, none)) (ofString "_node_rlp_begin")
                    [.var .local (ofString "cf"), .var .local (ofString "child")])
                  (.assign .local (ofString "top") (.var .local (ofString "cf"))))))))
        (.seq
          (.call (some (none, none)) (ofString "_node_rlp_finish")
            [.var .local (ofString "top"), .var .local (ofString "nd")])
          (.assign .local (ofString "top")
            (.load .one (.op .add [.var .local (ofString "top"), .const 0])))) := rfl
  rw [hft_eq] at hnone ⊢
  rw [evaluateHOLFiniteState_ite] at hnone ⊢
  have hev_cond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.var .local (ofString "found")) (.const 0)) =
      some (.val (.word (if fw ≠ 0 then 1 else 0))) := by
    by_cases hfw : fw = 0
    · subst hfw; simp [evalHOLExact, evalListHOLExact, hl_f, Compiler.Encoders.Asm.wordCmpHOL]
    · simp [evalHOLExact, evalListHOLExact, hl_f, Compiler.Encoders.Asm.wordCmpHOL, hfw]
  rw [hev_cond] at hnone ⊢; dsimp only at hnone ⊢
  by_cases hfw : fw ≠ 0
  · simp only [if_pos hfw, show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hnone ⊢
    obtain ⟨hc_in, hc1, hc3⟩ := hcw_kind hfw
    set pushCont : ProgHOL 64 :=
      .seq
        (.store (.op .add [.var .local (ofString "cf"), .const 0]) (.var .local (ofString "top")))
        (.seq
          (.store (.op .add [.var .local (ofString "cf"), .const 8]) (.var .local (ofString "child")))
          (.seq
            (.store (.op .add [.var .local (ofString "cf"), .const 16]) (.const 0))
            (.seq
              (.call (some (none, none)) (ofString "_node_rlp_begin")
                [.var .local (ofString "cf"), .var .local (ofString "child")])
              (.assign .local (ofString "top") (.var .local (ofString "cf"))))))
    obtain ⟨cfw, mid, hmid_c, _, hmid_loc, hmid_glob, heff_mid, hcf8, hcf_lo, hcf_sp,
      hmid_sp, hmid_W, hcont_none, hdec_eq⟩ :=
      eval_decCall_scratch_alloc_48_none_sc s (ofString "cf") pushCont [] ["scratch_ptr"]
        hc hAR (by simp) hnone
    rw [hdec_eq]; dsimp only
    have hl_mid_cf : mid.locals.lookup (ofString "cf") = some (.val (.word cfw)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hl_mid_top : mid.locals.lookup (ofString "top") = some (.val (.word topw)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hl_top,
        show ofString "cf" ≠ ofString "top" by decide]
    have hl_mid_c : mid.locals.lookup (ofString "child") = some (.val (.word cw)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hl_c,
        show ofString "cf" ≠ ofString "child" by decide]
    have hcf_hi_he : cfw.toNat + 48 ≤ heapEnd := by
      have := hAR.2.2.2.2.1; omega
    obtain ⟨hst0_none, hst0_loc, hst0_glob, hm0_st0, hW_st0, heff_st0⟩ :=
      eval_store_memW_at (s := mid) (base := cfw) (w := topw) (off := 0) (len := 48)
        (Rl := [(cfw.toNat + 0, 8)]) (gw := []) heff_mid.arena hmid_W (by decide) (by decide) hcf_hi_he
        ⟨(cfw.toNat + 0, 8), List.mem_singleton.2 rfl, by omega, by omega⟩
        (dstExp := .op .add [.var .local (ofString "cf"), .const 0])
        (valExp := .var .local (ofString "top"))
        (by simp [evalHOLExact, evalListHOLExact, hl_mid_cf, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [evalHOLExact, hl_mid_top])
    set m1 := (evaluateHOLFiniteState mid
      (.store (.op .add [.var .local (ofString "cf"), .const 0]) (.var .local (ofString "top")))).2
    have hseq0 : ∀ p2, evaluateHOLFiniteState mid
        (.seq (.store (.op .add [.var .local (ofString "cf"), .const 0]) (.var .local (ofString "top"))) p2) =
        evaluateHOLFiniteState m1 p2 := by
      intro p2; rw [evaluateHOLFiniteState_seq_line780]
      have hp : evaluateHOLFiniteState mid
          (.store (.op .add [.var .local (ofString "cf"), .const 0]) (.var .local (ofString "top"))) = (none, m1) :=
        Prod.ext hst0_none rfl
      rw [hp]
    dsimp only [pushCont] at hcont_none
    rw [hseq0] at hcont_none ⊢
    have hm1_c : m1.code = originalRuntimeCode :=
      (evaluateHOLFiniteState_metadata mid _).1.trans hmid_c
    have hm1_W : WordsOK m1 (cfw.toNat, 48) :=
      P3MptSet.wordsOK_transfer heff_mid.arena.1 heff_st0.arena.1 hmid_W
    obtain ⟨hst8_none, hst8_loc, hst8_glob, hm8_st8, hW_st8, heff_st8⟩ :=
      eval_store_memW_at (s := m1) (base := cfw) (w := cw) (off := 8) (len := 48)
        (Rl := [(cfw.toNat + 8, 8)]) (gw := []) heff_st0.arena hm1_W (by decide) (by decide) hcf_hi_he
        ⟨(cfw.toNat + 8, 8), List.mem_singleton.2 rfl, by omega, by omega⟩
        (dstExp := .op .add [.var .local (ofString "cf"), .const 8])
        (valExp := .var .local (ofString "child"))
        (by
          have hl1 : m1.locals.lookup (ofString "cf") = some (.val (.word cfw)) := by
            rw [hst0_loc]; exact hl_mid_cf
          simp [evalHOLExact, evalListHOLExact, hl1, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by
          have hl2 : m1.locals.lookup (ofString "child") = some (.val (.word cw)) := by
            rw [hst0_loc]; exact hl_mid_c
          simp [evalHOLExact, hl2])
    set m2 := (evaluateHOLFiniteState m1
      (.store (.op .add [.var .local (ofString "cf"), .const 8]) (.var .local (ofString "child")))).2
    have hseq8 : ∀ p2, evaluateHOLFiniteState m1
        (.seq (.store (.op .add [.var .local (ofString "cf"), .const 8]) (.var .local (ofString "child"))) p2) =
        evaluateHOLFiniteState m2 p2 := by
      intro p2; rw [evaluateHOLFiniteState_seq_line780]
      have hp : evaluateHOLFiniteState m1
          (.store (.op .add [.var .local (ofString "cf"), .const 8]) (.var .local (ofString "child"))) = (none, m2) :=
        Prod.ext hst8_none rfl
      rw [hp]
    rw [hseq8] at hcont_none ⊢
    have hm2_c : m2.code = originalRuntimeCode :=
      (evaluateHOLFiniteState_metadata m1 _).1.trans hm1_c
    have hm2_W : WordsOK m2 (cfw.toNat, 48) :=
      P3MptSet.wordsOK_transfer heff_st0.arena.1 heff_st8.arena.1 hm1_W
    obtain ⟨hst16_none, hst16_loc, hst16_glob, hm16_st16, hW_st16, heff_st16⟩ :=
      eval_store_memW_at (s := m2) (base := cfw) (w := 0) (off := 16) (len := 48)
        (Rl := [(cfw.toNat + 16, 8)]) (gw := []) heff_st8.arena hm2_W (by decide) (by decide) hcf_hi_he
        ⟨(cfw.toNat + 16, 8), List.mem_singleton.2 rfl, by omega, by omega⟩
        (dstExp := .op .add [.var .local (ofString "cf"), .const 16])
        (valExp := .const 0)
        (by
          have hl1 : m2.locals.lookup (ofString "cf") = some (.val (.word cfw)) := by
            rw [hst8_loc, hst0_loc]; exact hl_mid_cf
          simp [evalHOLExact, evalListHOLExact, hl1, wordOpHOL, wordOp, valueIsWord, valueWord])
        rfl
    set m3 := (evaluateHOLFiniteState m2
      (.store (.op .add [.var .local (ofString "cf"), .const 16]) (.const 0))).2
    have hseq16 : ∀ p2, evaluateHOLFiniteState m2
        (.seq (.store (.op .add [.var .local (ofString "cf"), .const 16]) (.const 0)) p2) =
        evaluateHOLFiniteState m3 p2 := by
      intro p2; rw [evaluateHOLFiniteState_seq_line780]
      have hp : evaluateHOLFiniteState m2
          (.store (.op .add [.var .local (ofString "cf"), .const 16]) (.const 0)) = (none, m3) :=
        Prod.ext hst16_none rfl
      rw [hp]
    rw [hseq16] at hcont_none ⊢
    have hm3_c : m3.code = originalRuntimeCode :=
      (evaluateHOLFiniteState_metadata m2 _).1.trans hm2_c
    have hm3_W : WordsOK m3 (cfw.toNat, 48) :=
      P3MptSet.wordsOK_transfer heff_st8.arena.1 heff_st16.arena.1 hm2_W
    have hm3_sp : globN m3 "scratch_ptr" = cfw.toNat := by
      unfold globN; rw [hst16_glob, hst8_glob, hst0_glob]; exact hmid_sp
    have heff_st0_48 : HeapByteEff mid m1 [(cfw.toNat, 48)] [] :=
      heff_st0.mono (fun i hi _ => by simp only [List.mem_singleton] at hi; subst hi; exact Or.inl ⟨(cfw.toNat, 48), List.mem_singleton.2 rfl, by omega, by omega⟩) (by simp)
    have heff_st8_48 : HeapByteEff m1 m2 [(cfw.toNat, 48)] [] :=
      heff_st8.mono (fun i hi _ => by simp only [List.mem_singleton] at hi; subst hi; exact Or.inl ⟨(cfw.toNat, 48), List.mem_singleton.2 rfl, by omega, by omega⟩) (by simp)
    have heff_st16_48 : HeapByteEff m2 m3 [(cfw.toNat, 48)] [] :=
      heff_st16.mono (fun i hi _ => by simp only [List.mem_singleton] at hi; subst hi; exact Or.inl ⟨(cfw.toNat, 48), List.mem_singleton.2 rfl, by omega, by omega⟩) (by simp)
    have heff_mid_m3 : HeapByteEff mid m3 [(cfw.toNat, 48)] [] :=
      (heff_st0_48.trans heff_st8_48).trans heff_st16_48
    have heff_s_m3 : HeapByteEff s m3 [(cfw.toNat, 48)] ["heap_ptr", "scratch_ptr"] :=
      (heff_mid.mono (fun _ h => by simp at h) (by simp)).trans
        (heff_mid_m3.mono
          (fun i hi _ => by simp only [List.mem_singleton] at hi; subst hi; exact Or.inl ⟨(cfw.toNat, 48), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
          (by simp))
    have hcf_disj_ext : ∀ o ∈ nodeExtents s Nd, Disj (cfw.toNat, 48) o := by
      intro o ho
      obtain ⟨m, hm, ho_m⟩ := List.mem_flatMap.1 ho
      obtain ⟨_, _, hin_m, _, _, _, hkey_m, _⟩ := hN.1 m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho_m
      have hcf_lo_ss : scratchStart ≤ cfw.toNat := by have := hAR.2.2.2.1; omega
      rcases ho_m with rfl | rfl
      · dsimp [nodeIvl, Inside] at hin_m; exact Or.inr (Or.inr (Or.inr (by dsimp [nodeIvl]; omega)))
      · dsimp [nodePath]
        split_ifs with hcond
        · rcases hkey_m hcond.1 with hz | ⟨_, _, hin_k, _⟩
          · exact absurd hz hcond.2
          · have := hin_k.2; dsimp at this; exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
        · exact Or.inr (Or.inl rfl)
    obtain ⟨hN_m3, hext_m3⟩ := nodeHeap_of_heapByteEff_disj hAR hN heff_s_m3
      (fun iv hiv _ o ho => by simp only [List.mem_singleton] at hiv; subst hiv; exact hcf_disj_ext o ho)
    have hbuf_m3 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
        bufferRegion m3 gs = bufferRegion s gs := by
      intro gs hgs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
      rcases hgs with rfl | rfl
      · unfold bufferRegion globN; rw [hst16_glob, hst8_glob, hst0_glob, hmid_glob _ (by decide)]
      · unfold bufferRegion globN; rw [hst16_glob, hst8_glob, hst0_glob, hmid_glob _ (by decide)]
    have hKS_m3 : KeccakBufsSafe m3 Nd := by
      intro gs hgs; rw [hbuf_m3 gs hgs]
      have hg_s_m3 : AllocatorGrows s m3 := ⟨heff_s_m3.hp_le, heff_s_m3.sp_le⟩
      exact ⟨(hKS gs hgs).1.elim Or.inl (fun h => Or.inr (hg_s_m3.allocated h)),
        fun o ho => by rw [hext_m3] at ho; exact (hKS gs hgs).2 o ho⟩
    have hvs_m3 : NodeValuesSafe sp0 m3 Nd :=
      nodeValuesSafe_of_heapByteEff (extra := [(cfw.toNat, 48)]) hAR hN hKS (by decide) (by decide)
        (heff_s_m3.mono
          (fun i hi _ => by
            simp only [List.mem_singleton] at hi; subst hi
            exact Or.inl ⟨(cfw.toNat, 48), List.mem_append_right _ (List.mem_singleton.2 rfl), le_rfl, le_rfl⟩)
          (fun _ h => h))
        (fun e he _ o ho => by simp only [List.mem_singleton] at he; subst he; exact hcf_disj_ext o ho)
        hvs
    have hbeg_none : (evaluateHOLFiniteState m3
        (.call (some (none, none)) (ofString "_node_rlp_begin")
          [.var .local (ofString "cf"), .var .local (ofString "child")])).1 = none := by
      rw [evaluateHOLFiniteState_seq_line780] at hcont_none
      rcases hbeg : evaluateHOLFiniteState m3
        (.call (some (none, none)) (ofString "_node_rlp_begin")
          [.var .local (ofString "cf"), .var .local (ofString "child")]) with ⟨rb, mb⟩
      rw [hbeg] at hcont_none
      cases rb with
      | none => rfl
      | some f => cases f <;> simp at hcont_none
    have hl_m3_cf : m3.locals.lookup (ofString "cf") = some (.val (.word cfw)) := by
      rw [hst16_loc, hst8_loc, hst0_loc]; exact hl_mid_cf
    have hl_m3_c : m3.locals.lookup (ofString "child") = some (.val (.word cw)) := by
      rw [hst16_loc, hst8_loc, hst0_loc]; exact hl_mid_c
    have hcw_kind_m3 : memW m3 cw.toNat = memW s cw.toNat := by
      obtain ⟨_, hal_c, hin_c, hw_c, _⟩ := hN.1 cw.toNat hc_in
      have hsz_c := nodeSize_ge32 (memW s cw.toNat)
      have hc_al8 : Allocated s (cw.toNat + 0, 8) := by
        rcases hal_c with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
        · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      simpa using memW_eq_of_heapByteEff_disj (a := cw.toNat + 0) hAR heff_s_m3 hw_c.1 hc_al8
        (by have := hin_c.2; dsimp [nodeIvl] at this; omega)
        (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          have := hin_c.2; have := hAR.2.2.2.1
          exact Or.inr (Or.inr (Or.inl (by dsimp [nodeIvl, Inside] at *; omega))))
    have hm0_m3 : memW m3 cfw.toNat = topw.toNat := by
      have hm1_sp : globN m1 "scratch_ptr" = cfw.toNat := by unfold globN; rw [hst0_glob]; exact hmid_sp
      have hm2_sp : globN m2 "scratch_ptr" = cfw.toNat := by unfold globN; rw [hst8_glob, hst0_glob]; exact hmid_sp
      have hm0_m2 : memW m2 (cfw.toNat + 0) = memW m1 (cfw.toNat + 0) :=
        memW_eq_of_heapByteEff_disj heff_st0.arena heff_st8 hcf8
          (Or.inr ⟨by rw [hm1_sp]; omega, by have := hAR.2.2.2.2.1; omega⟩) (by omega)
          (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))
      have hm0_m3' : memW m3 (cfw.toNat + 0) = memW m2 (cfw.toNat + 0) :=
        memW_eq_of_heapByteEff_disj heff_st8.arena heff_st16 hcf8
          (Or.inr ⟨by rw [hm2_sp]; omega, by have := hAR.2.2.2.2.1; omega⟩) (by omega)
          (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))
      simpa using (hm0_m3'.trans hm0_m2).trans hm0_st0
    have hm8_m3 : memW m3 (cfw.toNat + 8) = cw.toNat := by
      have hm2_sp : globN m2 "scratch_ptr" = cfw.toNat := by unfold globN; rw [hst8_glob, hst0_glob]; exact hmid_sp
      have hm8_m3' : memW m3 (cfw.toNat + 8) = memW m2 (cfw.toNat + 8) :=
        memW_eq_of_heapByteEff_disj heff_st8.arena heff_st16 (by omega)
          (Or.inr ⟨by rw [hm2_sp]; omega, by have := hAR.2.2.2.2.1; omega⟩) (by omega)
          (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))
      exact hm8_m3'.trans hm8_st8
    have hfr_in_m3 : Inside (cfw.toNat, 48) (globN m3 "scratch_ptr") scratchEnd :=
      ⟨by rw [hm3_sp], by have := hAR.2.2.2.2.1; omega⟩
    have hfr_kb_m3 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
        Disj (cfw.toNat, 48) (bufferRegion m3 gs) := by
      intro gs hgs; rw [hbuf_m3 gs hgs]
      exact disj_new_frame_keccak hAR hcf_lo (by omega) hkc_sp0 gs hgs
    obtain ⟨hbeg_loc, heff_beg, hN_m4, hext_m4, hKS_m4, hnc_m4, hm0_m4, hrf_m4⟩ :=
      hbeg_spec sp0 m3 Nd (.var .local (ofString "cf")) (.var .local (ofString "child")) cfw cw
        hm3_c heff_st16.arena hN_m3 hKS_m3 hvs_m3
        (by simp [evalHOLExact, hl_m3_cf]) (by simp [evalHOLExact, hl_m3_c])
        hfr_in_m3 (by omega) hm3_W hfr_kb_m3 hc_in
        (by rw [hcw_kind_m3]; exact hc1) hm8_m3 (by rw [hm16_st16]; decide) hbeg_none
    set m4 := (evaluateHOLFiniteState m3
      (.call (some (none, none)) (ofString "_node_rlp_begin")
        [.var .local (ofString "cf"), .var .local (ofString "child")])).2
    have hseq_beg : evaluateHOLFiniteState m3
        (.seq
          (.call (some (none, none)) (ofString "_node_rlp_begin")
            [.var .local (ofString "cf"), .var .local (ofString "child")])
          (.assign .local (ofString "top") (.var .local (ofString "cf")))) =
        evaluateHOLFiniteState m4
          (.assign .local (ofString "top") (.var .local (ofString "cf"))) := by
      rw [evaluateHOLFiniteState_seq_line780]
      have hp : evaluateHOLFiniteState m3
          (.call (some (none, none)) (ofString "_node_rlp_begin")
            [.var .local (ofString "cf"), .var .local (ofString "child")]) = (none, m4) :=
        Prod.ext hbeg_none rfl
      rw [hp]
    rw [hseq_beg]
    have hev_asgn : evaluateHOLFiniteState m4
        (.assign .local (ofString "top") (.var .local (ofString "cf"))) =
        (none, setVarHOLFinite (ofString "top") (.val (.word cfw)) m4) :=
      assign_local_word_eq_sc m4 (ofString "top") _ cfw topw
        (by rw [hbeg_loc, hst16_loc, hst8_loc, hst0_loc]; exact hl_mid_top)
        (by
          have hcf4 : m4.locals.lookup (ofString "cf") = some (.val (.word cfw)) := by
            rw [hbeg_loc]; exact hl_m3_cf
          simp [evalHOLExact, hcf4])
    rw [hev_asgn]; dsimp only
    set s_post : PanSemStateFiniteExact 64 F :=
      { (setVarHOLFinite (ofString "top") (.val (.word cfw)) m4) with
        locals := HolFiniteMapExact.resVarEq
          (setVarHOLFinite (ofString "top") (.val (.word cfw)) m4).locals
          (ofString "cf", s.locals.lookup (ofString "cf")) }
    have heff_s_m4 : HeapByteEff s m4 [(cfw.toNat, 48)] ["heap_ptr", "scratch_ptr"] :=
      heff_s_m3.trans
        (heff_beg.mono
          (fun i hi _ => by simp only [List.mem_singleton] at hi; subst hi; exact Or.inl ⟨(cfw.toNat, 48), List.mem_singleton.2 rfl, by omega, by omega⟩)
          (by simp))
    have hm4_sp : globN m4 "scratch_ptr" = cfw.toNat := by
      have hsp4 : globN m4 "scratch_ptr" = globN m3 "scratch_ptr" := by
        unfold globN; rw [← heff_beg.globals (ofString "scratch_ptr") (by decide)]
      exact hsp4.trans hm3_sp
    have hbuf_m4 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
        bufferRegion m4 gs = bufferRegion s gs := by
      intro gs hgs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
      rcases hgs with rfl | rfl
      · unfold bufferRegion globN; rw [← heff_s_m4.globals (ofString "keccak_pad") (by decide)]
      · unfold bufferRegion globN; rw [← heff_s_m4.globals (ofString "keccak_st") (by decide)]
    have hvs_m4 : NodeValuesSafe sp0 m4 Nd :=
      nodeValuesSafe_of_heapByteEff (extra := [(cfw.toNat, 48)]) hAR hN hKS (by decide) (by decide)
        (heff_s_m4.mono
          (fun i hi _ => by
            simp only [List.mem_singleton] at hi; subst hi
            exact Or.inl ⟨(cfw.toNat, 48), List.mem_append_right _ (List.mem_singleton.2 rfl), le_rfl, le_rfl⟩)
          (fun _ h => h))
        (fun e he _ o ho => by simp only [List.mem_singleton] at he; subst he; exact hcf_disj_ext o ho)
        hvs
    have hw_nd_m4 : ∀ n ∈ Nd, memW m4 n = memW s n ∧
        (1 ≤ memW s n → memW m4 (n + 40) = memW s (n + 40)) ∧
        (memW s n = 1 → memW m4 (n + 48) = memW s (n + 48) ∧ memW m4 (n + 56) = memW s (n + 56)) := by
      intro n hn
      have hw_m3 : ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
          memW m3 (n + off) = memW s (n + off) := by
        intro off hoff8 hoff_lt
        obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN.1 n hn
        have hn8 : n % 8 = 0 := hw_n.1
        have hal_off : Allocated s (n + off, 8) := by
          rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
          · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
        exact memW_eq_of_heapByteEff_disj hAR heff_s_m3 (by omega) hal_off
          (by have := hin_n.2; dsimp [nodeIvl] at this; omega)
          (fun iv hiv _ => by
            simp only [List.mem_singleton] at hiv; subst hiv
            have := hin_n.2; have := hAR.2.2.2.1
            exact Or.inr (Or.inr (Or.inl (by dsimp [nodeIvl, Inside] at *; omega))))
      have hsz0 := nodeSize_ge32 (memW s n)
      have hk_m3 : memW m3 n = memW s n := by simpa using hw_m3 0 rfl (by omega)
      have hw_m4 : ∀ off, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
          memW m4 (n + off) = memW s (n + off) := by
        intro off hoff8 hoff_lt
        exact (hnc_m4 n hn off hoff8 (by rw [hk_m3]; exact hoff_lt)).trans (hw_m3 off hoff8 hoff_lt)
      refine ⟨by simpa using hw_m4 0 rfl (by omega),
        fun hk1_n => hw_m4 40 (by decide) (by
          have hk3_n := (hN.1 n hn).1
          unfold nodeSize; split_ifs <;> omega),
        fun hk1_n => ⟨hw_m4 48 (by decide) (by simp [nodeSize, hk1_n]),
          hw_m4 56 (by decide) (by simp [nodeSize, hk1_n])⟩⟩
    have hch_top_m4 : ChainOK sp0 Nd m4 topw.toNat := by
      apply chainOK_lift_disj_s hAR hN hvs (hext_m4.trans hext_m3) hbuf_m4 hw_nd_m4 heff_s_m4 hsp_le _ hch
      intro g hvg htop_le_g hg_sp0
      have hg_in := hvg.2.1
      dsimp [Inside] at hg_in
      refine ⟨fun iv hiv _ => ?_, fun iv hiv _ hk12 => ?_, fun hk1_g hv1_g iv hiv _ hin_vp => ?_⟩
      · simp only [List.mem_singleton] at hiv; subst hiv
        exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
      · simp only [List.mem_singleton] at hiv; subst hiv
        obtain ⟨_, _, _, _, _, _, _, _, _, hk1_pay, hk2_pay, _⟩ := hvg
        have hcb_in : Inside (memW s (g + 24), memW s (g + 32)) sourceBase (globN s "heap_ptr") := by
          rcases hk12 with hk1_g | hk2_g
          · exact (hk1_pay hk1_g).2.2.1
          · exact (hk2_pay hk2_g).2.2.1
        have := hAR.2.2.1; have := hAR.2.2.2.1
        exact Or.inr (Or.inr (Or.inr (by dsimp [Inside] at hcb_in ⊢; omega)))
      · simp only [List.mem_singleton] at hiv; subst hiv
        obtain ⟨_, _, _, hg8_in, _, _, _, _, _, hk1_pay, _, _⟩ := hvg
        have hdom_g : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW s (memW s (g + 8) + 48)))) :=
          hAR.1.memaddrs ▸ (hk1_pay hk1_g).2.2.2.2.2.2 (by omega)
        obtain ⟨_, _, hfg_no, _⟩ := (hvs (memW s (g + 8)) hg8_in).1 hk1_g hv1_g hdom_g
        exact hfg_no (by dsimp [freeGapTo, InIvl] at hin_vp ⊢; omega)
    have htop_ge : cfw.toNat + 48 ≤ topw.toNat := by
      have := hv_top.2.1.1; omega
    have hch_m4 : ChainOK sp0 Nd m4 cfw.toNat :=
      ChainOK.chainStep m4 cfw.toNat topw.toNat hrf_m4
        (by simpa using hm0_m4.trans hm0_m3) htop_ge hch_top_m4
    have hloc_top : locN s_post "top" = cfw.toNat := by
      unfold locN
      have hl_post_top : s_post.locals.lookup (ofString "top") = some (.val (.word cfw)) := by
        change (HolFiniteMapExact.resVarEq
          (setVarHOLFinite (ofString "top") (.val (.word cfw)) m4).locals
          (ofString "cf", s.locals.lookup (ofString "cf"))).lookup (ofString "top") = _
        rw [R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide)]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      simp [hl_post_top]
    have hAR_post : ArenaReady s_post :=
      ⟨guestInv_with_locals_clock m4 s_post.locals m4.clock heff_beg.arena.1, heff_beg.arena.2⟩
    refine ⟨hAR_post, ⟨heff_s_m4.hp_le, heff_s_m4.sp_le⟩,
      Or.inr (by change globN m4 "scratch_ptr" < _; rw [hm4_sp]; omega),
      by change globN m4 "scratch_ptr" ≤ sp0; rw [hm4_sp]; omega,
      hN_m4, hKS_m4, hvs_m4,
      fun gs hgs hpos => by
        change 0 < (bufferRegion m4 gs).2 at hpos
        change (bufferRegion m4 gs).1 + (bufferRegion m4 gs).2 ≤ globN m4 "heap_ptr" ∨
          sp0 ≤ (bufferRegion m4 gs).1
        rw [hbuf_m4 gs hgs] at hpos ⊢
        rcases hkc_sp0 gs hgs hpos with hhi | hlo
        · exact Or.inl (hhi.trans heff_s_m4.hp_le)
        · exact Or.inr hlo,
      by rw [hloc_top]; exact chainOK_with_locals_clock m4 s_post.locals m4.clock sp0 Nd hch_m4,
      fun x hxt => ?_⟩
    by_cases hxc : x = ofString "cf"
    · subst hxc
      change (HolFiniteMapExact.resVarEq _ _).lookup (ofString "cf") = _
      rw [InitECandidate.Solver.PanRunBounded.resVarEq_lookup]; simp
    · change (HolFiniteMapExact.resVarEq _ _).lookup x = _
      rw [R16Shards.resVarEq_lookup_ne _ _ _ _ hxc]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxt,
        hbeg_loc, hst16_loc, hst8_loc, hst0_loc, hmid_loc, Ne.symm hxc]
  · have hfw0 : fw = 0 := Classical.not_not.1 hfw
    simp only [if_neg hfw, ↓reduceIte] at hnone ⊢
    have hfin_none : (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_finish")
          [.var .local (ofString "top"), .var .local (ofString "nd")])).1 = none := by
      rw [evaluateHOLFiniteState_seq_line780] at hnone
      rcases hfin : evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_finish")
          [.var .local (ofString "top"), .var .local (ofString "nd")]) with ⟨rf, mf⟩
      rw [hfin] at hnone
      cases rf with
      | none => rfl
      | some f => cases f <;> simp at hnone
    obtain ⟨hfin_loc, totLen, htot1, htot_hi, htot_ext, heff_fin, hhp_lt,
      hN_sf, hext_sf, hKS_sf, hvs_sf, _, _, _, hw_nd_sf⟩ :=
      hfin_spec sp0 s Nd (.var .local (ofString "top")) (.var .local (ofString "nd")) topw ndw
        hc hAR hN hKS hvs hsp_le
        (by simp [evalHOLExact, hl_top]) (by simp [evalHOLExact, hl_nd])
        hv_top hnd_eq hfin_none
    set sf := (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "_node_rlp_finish")
        [.var .local (ofString "top"), .var .local (ofString "nd")])).2
    have hseq_fin : evaluateHOLFiniteState s
        (.seq
          (.call (some (none, none)) (ofString "_node_rlp_finish")
            [.var .local (ofString "top"), .var .local (ofString "nd")])
          (.assign .local (ofString "top")
            (.load .one (.op .add [.var .local (ofString "top"), .const 0])))) =
        evaluateHOLFiniteState sf
          (.assign .local (ofString "top")
            (.load .one (.op .add [.var .local (ofString "top"), .const 0]))) := by
      rw [evaluateHOLFiniteState_seq_line780]
      have hp : evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "_node_rlp_finish")
            [.var .local (ofString "top"), .var .local (ofString "nd")]) = (none, sf) :=
        Prod.ext hfin_none rfl
      rw [hp]
    rw [hseq_fin]
    have hin_top := hv_top.2.1
    have hw_top := hv_top.2.2.1
    have hsf_W_top : WordsOK sf (topw.toNat, 48) :=
      P3MptSet.wordsOK_transfer hAR.1 heff_fin.arena.1 hw_top
    obtain ⟨prevw, hld0, hprev_nat⟩ := eval_load_memW_of_wordsOK (s := sf) (base := topw) (off := 0)
      (len := 48) hsf_W_top (by decide) (by decide)
      (by have := hin_top.2; dsimp [Inside] at this; omega)
      (e := .op .add [.var .local (ofString "top"), .const 0])
      (by
        have hlt : sf.locals.lookup (ofString "top") = some (.val (.word topw)) := by
          rw [hfin_loc]; exact hl_top
        simp [evalHOLExact, evalListHOLExact, hlt, wordOpHOL, wordOp, valueIsWord, valueWord])
    have hbuf_sf : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
        bufferRegion sf gs = bufferRegion s gs := by
      intro gs hgs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
      rcases hgs with rfl | rfl
      · unfold bufferRegion globN; rw [← heff_fin.globals (ofString "keccak_pad") (by decide)]
      · unfold bufferRegion globN; rw [← heff_fin.globals (ofString "keccak_st") (by decide)]
    have hfin_disj_scratch : ∀ g, globN s "scratch_ptr" ≤ g → g + 48 ≤ sp0 →
        ∀ iv ∈ (globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s),
          0 < iv.2 → Disj iv (g, 48) := by
      intro g hg_lo hg_sp0 iv hiv hpos
      rcases List.mem_cons.1 hiv with rfl | hiv_rest
      · have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
        exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
      · rcases List.mem_append.1 hiv_rest with hnc_iv | hkc_iv
        · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hnc_iv
          obtain ⟨_, _, hin_m, _⟩ := hN.1 m hm
          have hsz_m := nodeSize_ge32 (memW s m)
          have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
          exact Or.inr (Or.inr (Or.inl (by dsimp [nodeIvl, Inside] at *; omega)))
        · simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hkc_iv
          rcases hkc_iv with rfl | rfl
          · rcases hkc_sp0 ("keccak_pad", 136) (by decide) hpos with hhi | hlo
            · have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
              exact Or.inr (Or.inr (Or.inl (by dsimp at *; omega)))
            · exact Or.inr (Or.inr (Or.inr (by dsimp at *; omega)))
          · rcases hkc_sp0 ("keccak_st", 200) (by decide) hpos with hhi | hlo
            · have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
              exact Or.inr (Or.inr (Or.inl (by dsimp at *; omega)))
            · exact Or.inr (Or.inr (Or.inr (by dsimp at *; omega)))
    have htop_sp0 : topw.toNat + 48 ≤ sp0 := by
      rcases chainOK_bound_sp0_s hch with h0 | ⟨_, hle⟩
      · exact absurd h0 htop_ne
      · exact hle
    have hm0_top_sf : memW sf topw.toNat = memW s topw.toNat := by
      simpa using memW_eq_of_heapByteEff_disj (a := topw.toNat + 0) hAR heff_fin hv_top.1
        (Or.inr ⟨by have := hAR.2.2.2.1; have := hAR.2.2.2.2.1; dsimp [Inside] at hin_top ⊢; omega,
          by have := hin_top.2; dsimp [Inside] at this ⊢; omega⟩)
        (by have := hin_top.2; dsimp [Inside] at this; omega)
        (fun iv hiv hpos => by
          have hdj := hfin_disj_scratch topw.toNat hin_top.1 htop_sp0 iv hiv hpos
          dsimp [Disj] at hdj ⊢
          rcases hdj with h0 | h0 | h1 | h2 <;> omega)
    have hev_pop : evaluateHOLFiniteState sf
        (.assign .local (ofString "top")
          (.load .one (.op .add [.var .local (ofString "top"), .const 0]))) =
        (none, setVarHOLFinite (ofString "top") (.val (.word prevw)) sf) :=
      assign_local_word_eq_sc sf (ofString "top") _ prevw topw
        (by rw [hfin_loc]; exact hl_top) hld0
    rw [hev_pop]; dsimp only
    set spop := setVarHOLFinite (ofString "top") (.val (.word prevw)) sf
    have hsf_sp : globN sf "scratch_ptr" = globN s "scratch_ptr" := by
      unfold globN; rw [← heff_fin.globals (ofString "scratch_ptr") (by decide)]
    have hch_sf : ChainOK sp0 Nd sf prevw.toNat := by
      have hprev_eq : prevw.toNat = memW s topw.toNat := by
        simpa using hprev_nat.trans hm0_top_sf
      rw [hprev_eq]
      generalize ht_eq : topw.toNat = t at hch htop_ne
      cases hch with
      | chainNil => exact absurd rfl htop_ne
      | chainDone _ _ _ hm0 =>
        subst ht_eq
        have hz : memW s topw.toNat = 0 := by simpa using hm0
        rw [hz]; exact ChainOK.chainNil sf
      | chainStep _ p _ hm0 htp htail =>
        subst ht_eq
        have hp_eq : memW s topw.toNat = p := by simpa using hm0
        rw [hp_eq]
        apply chainOK_lift_disj_s hAR hN hvs hext_sf hbuf_sf hw_nd_sf heff_fin hsp_le _ htail
        intro g hvg hp_le_g hg_sp0
        obtain ⟨_, hg_in, _, hg8_in, _, _, _, _, _, hk1_pay, hk2_pay, _⟩ := hvg
        refine ⟨fun iv hiv hpos => hfin_disj_scratch g hg_in.1 hg_sp0 iv hiv hpos,
          fun iv hiv hpos hk12 => ?_, fun hk1_g hv1_g iv hiv hpos hin_vp => ?_⟩
        · have hcb_info : Inside (memW s (g + 24), memW s (g + 32)) sourceBase (globN s "heap_ptr") ∧
              (∀ o ∈ nodeExtents s Nd, Disj (memW s (g + 24), memW s (g + 32)) o) ∧
              (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
                Disj (memW s (g + 24), memW s (g + 32)) (bufferRegion s gs)) := by
            rcases hk12 with hk1_g | hk2_g
            · obtain ⟨_, _, hc1, hc2, hc3, _⟩ := hk1_pay hk1_g
              exact ⟨hc1, hc2, hc3⟩
            · obtain ⟨_, _, hc1, hc2, hc3, _⟩ := hk2_pay hk2_g
              exact ⟨hc1, hc2, hc3⟩
          rcases List.mem_cons.1 hiv with rfl | hiv_rest
          · exact Or.inr (Or.inr (Or.inr (by dsimp [Inside] at hcb_info ⊢; omega)))
          · rcases List.mem_append.1 hiv_rest with hnc_iv | hkc_iv
            · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hnc_iv
              have ho_mem : nodeIvl s m ∈ nodeExtents s Nd := by
                unfold nodeExtents; exact List.mem_flatMap.2 ⟨m, hm, List.mem_cons_self⟩
              have hdj := disj_comm (hcb_info.2.1 (nodeIvl s m) ho_mem)
              have hsz_m := nodeSize_ge32 (memW s m)
              dsimp [Disj, nodeIvl] at hdj ⊢
              rcases hdj with h0 | h0 | hd1 | hd2 <;> omega
            · simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hkc_iv
              rcases hkc_iv with rfl | rfl
              · exact disj_comm (hcb_info.2.2 ("keccak_pad", 136) (by decide))
              · exact disj_comm (hcb_info.2.2 ("keccak_st", 200) (by decide))
        · have hdom_g : ordinaryDomain (panByteAlignHOL (BitVec.ofNat 64 (memW s (memW s (g + 8) + 48)))) :=
            hAR.1.memaddrs ▸ (hk1_pay hk1_g).2.2.2.2.2.2 (by omega)
          obtain ⟨hnc_no, hkc_no, _, hhf_no⟩ := (hvs (memW s (g + 8)) hg8_in).1 hk1_g hv1_g hdom_g
          rcases List.mem_cons.1 hiv with rfl | hiv_rest
          · exact hhf_no (by dsimp [heapFree, InIvl] at hin_vp ⊢; omega)
          · rcases List.mem_append.1 hiv_rest with hnc_iv | hkc_iv
            · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hnc_iv
              exact hnc_no m hm hin_vp
            · simp only [keccakBufIvls, List.mem_cons, List.not_mem_nil, or_false] at hkc_iv
              rcases hkc_iv with rfl | rfl
              · exact hkc_no ("keccak_pad", 136) (by decide) hpos hin_vp
              · exact hkc_no ("keccak_st", 200) (by decide) hpos hin_vp
    have hloc_top : locN spop "top" = prevw.toNat := by
      simp [spop, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hAR_spop : ArenaReady spop :=
      ⟨guestInv_setVar _ _ _ heff_fin.arena.1, heff_fin.arena.2⟩
    refine ⟨hAR_spop, ⟨heff_fin.hp_le, heff_fin.sp_le⟩,
      Or.inl hhp_lt, by change globN sf "scratch_ptr" ≤ sp0; rw [hsf_sp]; exact hsp_le,
      hN_sf, hKS_sf, hvs_sf,
      fun gs hgs hpos => by
        change 0 < (bufferRegion sf gs).2 at hpos
        change (bufferRegion sf gs).1 + (bufferRegion sf gs).2 ≤ globN sf "heap_ptr" ∨
          sp0 ≤ (bufferRegion sf gs).1
        rw [hbuf_sf gs hgs] at hpos ⊢
        rcases hkc_sp0 gs hgs hpos with hhi | hlo
        · exact Or.inl (hhi.trans heff_fin.hp_le)
        · exact Or.inr hlo,
      by rw [hloc_top]; exact chainOK_with_locals_clock sf spop.locals spop.clock sp0 Nd hch_sf,
      fun x hxt => ?_⟩
    simp [spop, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxt, hfin_loc]



private theorem chainOK_head_valid_s {F : Type} {sp0 : Nat} {Nd : List Nat}
    {s : PanSemStateFiniteExact 64 F} {fr : Nat}
    (hch : ChainOK sp0 Nd s fr) (hne : fr ≠ 0) :
    ValidRlpFrame s Nd fr := by
  cases hch with
  | chainNil => exact absurd rfl hne
  | chainDone _ hv _ _ => exact hv
  | chainStep _ _ hv _ _ _ => exact hv

private theorem fillBody_active_scanEntry_s {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hinv : FillLoopInv s)
    (hact : LoopActive (.cmp .notEqual (.var .local (ofString "top")) (.const 0)) s) :
    GuestInv s ∧ memW s (locN s "top" + 16) ≤ 16 := by
  obtain ⟨hAR, sp0, Nd, _, _, _, _, _, _, hch⟩ := hinv
  obtain ⟨topw, _, htopw_nz, htop_nat⟩ := loopActive_top_word hact
  have htop_ne : locN s "top" ≠ 0 := by
    rw [← htop_nat]
    intro hz; exact htopw_nz (BitVec.eq_of_toNat_eq (by simpa using hz))
  have hv := chainOK_head_valid_s hch htop_ne
  exact ⟨hAR.1, hv.2.2.2.2.2.2.1⟩

private theorem fillBodytep_s
    (hbeg_spec : ∀ {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (frExp nodeExp : ExpHOL 64) (frw nodew : BitVec 64),
      s.code = originalRuntimeCode → ArenaReady s → NodeHeap s Nd →
      KeccakBufsSafe s Nd → NodeValuesSafe sp0 s Nd →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
        some (.val (.word frw)) →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
        some (.val (.word nodew)) →
      Inside (frw.toNat, 48) (globN s "scratch_ptr") scratchEnd →
      frw.toNat + 48 ≤ sp0 →
      WordsOK s (frw.toNat, 48) →
      (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
        Disj (frw.toNat, 48) (bufferRegion s gs)) →
      nodew.toNat ∈ Nd →
      1 ≤ memW s nodew.toNat →
      memW s (frw.toNat + 8) = nodew.toNat →
      memW s (frw.toNat + 16) ≤ 16 →
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_begin") [frExp, nodeExp])).1 = none →
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
      ValidRlpFrame post Nd frw.toNat)
    (hfin_spec : ∀ {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (frExp nodeExp : ExpHOL 64) (frw nodew : BitVec 64),
      s.code = originalRuntimeCode → ArenaReady s → NodeHeap s Nd →
      KeccakBufsSafe s Nd → NodeValuesSafe sp0 s Nd →
      globN s "scratch_ptr" ≤ sp0 →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
        some (.val (.word frw)) →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
        some (.val (.word nodew)) →
      ValidRlpFrame s Nd frw.toNat →
      memW s (frw.toNat + 8) = nodew.toNat →
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_finish") [frExp, nodeExp])).1 = none →
      let post := (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_finish") [frExp, nodeExp])).2
      post.locals = s.locals ∧
      ∃ totLen : Nat,
        1 ≤ totLen ∧
        globN s "heap_ptr" + totLen ≤ heapLimit ∧
        (∀ o ∈ nodeExtents s Nd, Disj (globN s "heap_ptr", totLen) o) ∧
        HeapByteEff s post
          ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] ∧
        globN s "heap_ptr" < globN post "heap_ptr" ∧
        NodeHeap post Nd ∧
        nodeExtents post Nd = nodeExtents s Nd ∧
        KeccakBufsSafe post Nd ∧
        NodeValuesSafe sp0 post Nd ∧
        memW post (nodew.toNat + 8) = globN s "heap_ptr" ∧
        memW post (nodew.toNat + 16) = totLen ∧
        (∀ n ∈ Nd, n ≠ nodew.toNat → memW post (n + 8) = memW s (n + 8) ∧
          memW post (n + 16) = memW s (n + 16)) ∧
        (∀ n ∈ Nd, memW post n = memW s n ∧
          (1 ≤ memW s n → memW post (n + 40) = memW s (n + 40)) ∧
          (memW s n = 1 → memW post (n + 48) = memW s (n + 48) ∧
            memW post (n + 56) = memW s (n + 56))))
    {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hinv : FillLoopInv s)
    (hact : LoopActive (.cmp .notEqual (.var .local (ofString "top")) (.const 0)) s)
    (hflow : (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).1 = some .continue) :
    FillLoopInv (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).2 ∧
      fillMeasure (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).2 < fillMeasure s := by
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).1 = none := by
    rcases hflow with hn | hcont
    · exact hn
    · exact absurd hcont (evaluate_noTopContinue fillBody (by decide) (decClockHOLFinite s))
  have hse_he : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhe_264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhl_264 : heapLimit ≤ 2 ^ 64 := by decide
  set s0 := decClockHOLFinite s
  have hs0_inv : FillLoopInv s0 := fillLoopInv_locals.decClock s hinv
  obtain ⟨hAR, sp0, Nd, hsp_le, hsp0_hi, hN, hKS, hvs, hkc_sp0, hch⟩ := hs0_inv
  obtain ⟨topw, hl_top_s, htopw_nz, htop_nat_s⟩ := loopActive_top_word hact
  have hl_top : s0.locals.lookup (ofString "top") = some (.val (.word topw)) := hl_top_s
  have htop_nat : topw.toNat = locN s0 "top" := htop_nat_s
  have htop_ne : topw.toNat ≠ 0 := fun hz =>
    htopw_nz (BitVec.eq_of_toNat_eq (by simpa using hz))
  rw [← htop_nat] at hch
  have hv_top : ValidRlpFrame s0 Nd topw.toNat := chainOK_head_valid_s hch htop_ne
  have hin_top := hv_top.2.1
  have hw_top := hv_top.2.2.1
  have hnd_in_s := hv_top.2.2.2.1
  have hs0_c : s0.code = originalRuntimeCode := hc
  have hfb_eq : fillBody =
      .dec (ofString "nd") .one (.load .one (.op .add [.var .local (ofString "top"), .const 8]))
        (.dec (ofString "k") .one (.load .one (.op .add [.var .local (ofString "nd"), .const 0]))
          (.dec (ofString "child") .one (.const 0)
            (.dec (ofString "found") .one (.const 0)
              (.seq fillSearch fillTail)))) := rfl
  rw [hfb_eq] at hnone ⊢
  obtain ⟨ndw, hld_nd, hnd_nat⟩ := eval_load_memW_of_wordsOK (s := s0) (base := topw) (off := 8)
    (len := 48) hw_top (by decide) (by decide)
    (by have := hin_top.2; dsimp [Inside] at this; omega)
    (e := .op .add [.var .local (ofString "top"), .const 8])
    (by simp [evalHOLExact, evalListHOLExact, hl_top, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
  rw [dec_eval_word_eq_sc s0 (ofString "nd") _ ndw _ hld_nd] at hnone ⊢
  dsimp only at hnone ⊢
  set d1 := setVarHOLFinite (ofString "nd") (.val (.word ndw)) s0
  have hd1_nd_in : ndw.toNat ∈ Nd := hnd_nat ▸ hnd_in_s
  obtain ⟨_, _, hin_nd, hw_nd, _⟩ := hN.1 ndw.toNat hd1_nd_in
  have hl_d1_nd : d1.locals.lookup (ofString "nd") = some (.val (.word ndw)) := by
    simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨kw, hld_k, hkw_nat⟩ := eval_load_memW_of_wordsOK (s := d1) (base := ndw) (off := 0)
    (len := nodeSize (memW s0 ndw.toNat)) hw_nd (by decide)
    (by have := nodeSize_ge32 (memW s0 ndw.toNat); omega)
    (by have := hin_nd.2; dsimp [nodeIvl] at this; omega)
    (e := .op .add [.var .local (ofString "nd"), .const 0])
    (by simp [evalHOLExact, evalListHOLExact, hl_d1_nd, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
  rw [dec_eval_word_eq_sc d1 (ofString "k") _ kw _ hld_k] at hnone ⊢
  dsimp only at hnone ⊢
  set d2 := setVarHOLFinite (ofString "k") (.val (.word kw)) d1
  rw [dec_eval_word_eq_sc d2 (ofString "child") (.const 0) 0 _ rfl] at hnone ⊢
  dsimp only at hnone ⊢
  set d3 := setVarHOLFinite (ofString "child") (.val (.word 0)) d2
  rw [dec_eval_word_eq_sc d3 (ofString "found") (.const 0) 0 _ rfl] at hnone ⊢
  dsimp only at hnone ⊢
  set d4 := setVarHOLFinite (ofString "found") (.val (.word 0)) d3
  obtain ⟨hsrch_none, htail_none, hseq_eq⟩ := fillSeq_none d4 fillSearch fillTail hnone
  rw [hseq_eq]
  have hd4_eq : d4 = { s0 with locals := d4.locals, clock := s0.clock } := rfl
  have hd4_AR : ArenaReady d4 :=
    ⟨guestInv_with_locals_clock s0 d4.locals s0.clock hAR.1, hAR.2⟩
  have hd4_ch : ChainOK sp0 Nd d4 topw.toNat :=
    chainOK_with_locals_clock s0 d4.locals s0.clock sp0 Nd hch
  have hl_d4_top : d4.locals.lookup (ofString "top") = some (.val (.word topw)) := by
    simp [d4, d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_top,
      show ofString "found" ≠ ofString "top" by decide,
      show ofString "child" ≠ ofString "top" by decide,
      show ofString "k" ≠ ofString "top" by decide,
      show ofString "nd" ≠ ofString "top" by decide]
  have hl_d4_nd : d4.locals.lookup (ofString "nd") = some (.val (.word ndw)) := by
    simp [d4, d3, d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "found" ≠ ofString "nd" by decide,
      show ofString "child" ≠ ofString "nd" by decide,
      show ofString "k" ≠ ofString "nd" by decide]
  have hl_d4_k : d4.locals.lookup (ofString "k") = some (.val (.word kw)) := by
    simp [d4, d3, d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "found" ≠ ofString "k" by decide,
      show ofString "child" ≠ ofString "k" by decide]
  have hl_d4_c : d4.locals.lookup (ofString "child") = some (.val (.word 0)) := by
    simp [d4, d3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "found" ≠ ofString "child" by decide]
  have hl_d4_f : d4.locals.lookup (ofString "found") = some (.val (.word 0)) := by
    simp [d4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨cw, fw, hsr_c, hsr_AR, hsr_glob, hsr_N, hsr_KS, hsr_vs,
      hsr_vtop, hsr_ch, hsr_m8, hsr_cw, hsr_ltop, hsr_lnd, hsr_lc, hsr_lf⟩ :=
    eval_fillSearch_none_s (s := d4) hs0_c hd4_AR hN hKS hvs hsp_le hsp0_hi htop_ne
      hv_top hd4_ch hnd_nat.symm hkw_nat.symm hl_d4_top hl_d4_nd hl_d4_k hl_d4_c hl_d4_f hsrch_none
  set sr := (evaluateHOLFiniteState d4 fillSearch).2
  have hd4_glob : d4.globals = s0.globals := rfl
  have hsr_sp : globN sr "scratch_ptr" = globN s0 "scratch_ptr" := by
    unfold globN; rw [hsr_glob, hd4_glob]
  have hsr_hp : globN sr "heap_ptr" = globN s0 "heap_ptr" := by
    unfold globN; rw [hsr_glob, hd4_glob]
  have hsr_kc_sp0 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      0 < (bufferRegion sr gs).2 →
      (bufferRegion sr gs).1 + (bufferRegion sr gs).2 ≤ globN sr "heap_ptr" ∨
        sp0 ≤ (bufferRegion sr gs).1 := by
    intro gs hgs hpos
    have hbuf_sr : bufferRegion sr gs = bufferRegion s0 gs := by
      unfold bufferRegion globN; rw [hsr_glob, hd4_glob]
    rw [hbuf_sr] at hpos ⊢
    rw [hsr_hp]
    exact hkc_sp0 gs hgs hpos
  obtain ⟨htl_AR, htl_grows, htl_strict, htl_sp_sp0, htl_N, htl_KS, htl_vs,
      htl_kc_sp0, htl_ch, htl_loc_keep⟩ :=
    eval_fillTail_none_s hbeg_spec hfin_spec sp0 sr Nd topw ndw cw fw hsr_c hsr_AR
      (by rw [hsr_sp]; exact hsp_le) hsp0_hi hsr_N hsr_KS hsr_vs hsr_kc_sp0
      hsr_vtop hsr_ch htop_ne hsr_m8 hsr_cw hsr_ltop hsr_lnd hsr_lc hsr_lf htail_none
  set tl := (evaluateHOLFiniteState sr fillTail).2
  let resLocals : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq tl.locals (ofString "found", d3.locals.lookup (ofString "found")))
          (ofString "child", d2.locals.lookup (ofString "child")))
        (ofString "k", d1.locals.lookup (ofString "k")))
      (ofString "nd", s0.locals.lookup (ofString "nd"))
  have htl_inv : FillLoopInv tl :=
    ⟨htl_AR, sp0, Nd, htl_sp_sp0, hsp0_hi, htl_N, htl_KS, htl_vs, htl_kc_sp0, htl_ch⟩
  have hres_top : resLocals.lookup (ofString "top") = tl.locals.lookup (ofString "top") := by
    dsimp only [resLocals]
    rw [R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide),
      R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide),
      R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide),
      R16Shards.resVarEq_lookup_ne _ _ _ _ (by decide)]
  have hpost_inv : FillLoopInv { tl with locals := resLocals, clock := tl.clock } :=
    fillLoopInv_locals tl resLocals tl.clock (fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hres_top) htl_inv
  have hgrows_s : AllocatorGrows s tl :=
    ⟨by change globN s0 "heap_ptr" ≤ _; rw [← hsr_hp]; exact htl_grows.1,
     by change _ ≤ globN s0 "scratch_ptr"; rw [← hsr_sp]; exact htl_grows.2⟩
  have hstrict_s : globN s "heap_ptr" < globN tl "heap_ptr" ∨
      globN tl "scratch_ptr" < globN s "scratch_ptr" := by
    change globN s0 "heap_ptr" < _ ∨ _ < globN s0 "scratch_ptr"
    rw [← hsr_hp, ← hsr_sp]; exact htl_strict
  have hmeas : fillMeasure { tl with locals := resLocals, clock := tl.clock } < fillMeasure s :=
    fillMeasure_decreases s tl htl_AR hgrows_s hstrict_s
  exact ⟨hpost_inv, hmeas⟩



private def FillAllocReady_s : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ (sp0 : Nat) (Nd : List Nat) (frw nodew : BitVec 64),
    sp0 ≤ scratchEnd ∧
    frw.toNat % 8 = 0 ∧
    globN s "frame_mem_ptr" ≤ frw.toNat ∧
    frw.toNat + 48 = sp0 ∧
    globN s "scratch_ptr" = frw.toNat ∧
    WordsOK s (frw.toNat, 48) ∧
    NodeHeap s Nd ∧ KeccakBufsSafe s Nd ∧ NodeValuesSafe sp0 s Nd ∧
    (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      0 < (bufferRegion s gs).2 →
      (bufferRegion s gs).1 + (bufferRegion s gs).2 ≤ globN s "heap_ptr" ∨
        sp0 ≤ (bufferRegion s gs).1) ∧
    nodew.toNat ∈ Nd ∧ 1 ≤ memW s nodew.toNat ∧ memW s nodew.toNat ≤ 3 ∧
    s.locals.lookup (ofString "fr") = some (.val (.word frw)) ∧
    s.locals.lookup (ofString "node") = some (.val (.word nodew))

private def FillBeginReady_s : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ (sp0 : Nat) (Nd : List Nat) (frw : BitVec 64),
    globN s "scratch_ptr" ≤ sp0 ∧ sp0 ≤ scratchEnd ∧
    frw.toNat + 48 ≤ sp0 ∧
    memW s (frw.toNat + 0) = 0 ∧
    NodeHeap s Nd ∧ KeccakBufsSafe s Nd ∧ NodeValuesSafe sp0 s Nd ∧
    (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
      0 < (bufferRegion s gs).2 →
      (bufferRegion s gs).1 + (bufferRegion s gs).2 ≤ globN s "heap_ptr" ∨
        sp0 ≤ (bufferRegion s gs).1) ∧
    ValidRlpFrame s Nd frw.toNat ∧
    s.locals.lookup (ofString "fr") = some (.val (.word frw))

private theorem resume_scratch_mark_s :
    DecCallResumeOn NodeRlpReadyStrong NodeRlpReadyStrong (ofString "mark")
      (ofString "scratch_mark") [] := by
  intro F state values body callee retShape value post hcode hP hargs hlook hrun
  have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "scratch_mark") values =
      some (sourceFnBody Guest.Software.guestFn_scratch_mark, FEMPTY, .one) := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp only [evalListHOLExact] at hargs
    injection hargs with hv; subst hv
    simp only [lookupCodeHOLExact, lookup_scratch_mark, List.length_nil, List.zip_nil_left, List.all_nil]
    rfl
  have hb_eq : body = sourceFnBody Guest.Software.guestFn_scratch_mark := by
    rw [hcode] at hlook
    exact lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ retShape values callee
      lookup_scratch_mark hlook
  subst hb_eq
  obtain ⟨sp, rfl, _, hres_eq⟩ := scratch_mark_returned_sc state (ofString "mark") callee value post hP.1.1 hrun
  rw [hres_eq]
  exact localsOnlyStrong state (state.locals.update (ofString "mark", .val (.word sp))) post.clock
    (fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "mark" ≠ ofString "node" by decide]) hP

private theorem resume_scratch_alloc_48_s :
    DecCallResumeOn NodeRlpReadyStrong FillAllocReady_s (ofString "fr")
      (ofString "scratch_alloc") [.const 48] := by
  intro F state values body callee retShape value post hcode hP hargs hlook hrun
  have hargs48 : values = [.val (.word 48)] := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simpa only [evalListHOLExact, evalHOLExact, Option.some.injEq] using hargs.symm
  subst hargs48
  have hlk48 := pan_one_word_lookup state.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_scratch_alloc) 48 (by rw [hcode]; exact lookup_scratch_alloc)
  rw [hlk48] at hlook
  have heq := Option.some.inj hlook
  rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
  rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
  have hcn : (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (HolWordLab.word (48 : BitVec 64)))).lookup
      (ofString "n") = some (ValueHOL.val (HolWordLab.word 48)) := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨frw, rfl, _, _, hmid_loc, hmid_glob, heff_mid, hfr8, hfp_fr, hfr_sp, hmid_sp, hwok⟩ :=
    scratch_alloc_48_returned_sc state (ofString "fr") _ value post [] ["scratch_ptr"]
      hcode hP.1.1 (by simp) hcn hrun
  set mid := setVarHOLFinite (ofString "fr") (.val (.word frw)) { post with locals := state.locals }
  obtain ⟨⟨hAR_s, Nd, hN_s, hroot_s, hKS_s, hvp_s⟩, hnode_ne, hkind_ne⟩ := hP
  obtain ⟨nodew, hl_node_s, hnode_nat⟩ := word_of_locN_ne_zero hnode_ne
  have hnode_in : nodew.toNat ∈ Nd := hnode_nat ▸ (hroot_s.resolve_left hnode_ne)
  have hk_le3 : memW state nodew.toNat ≤ 3 := (hN_s.1 _ hnode_in).1
  have hk_ge1 : 1 ≤ memW state nodew.toNat := by
    rw [hnode_nat]; exact Nat.pos_of_ne_zero hkind_ne
  set sp0 := globN state "scratch_ptr"
  have hsp0_hi : sp0 ≤ scratchEnd := hAR_s.2.2.2.2.2.1
  obtain ⟨hN_mid, hext_mid⟩ := nodeHeap_of_heapByteEff_disj hAR_s hN_s heff_mid
    (fun _ hiv => absurd hiv List.not_mem_nil)
  have hbuf_mid : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion mid gs = bufferRegion state gs := by
    intro gs hgs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl
    · unfold bufferRegion globN; rw [hmid_glob _ (by decide)]
    · unfold bufferRegion globN; rw [hmid_glob _ (by decide)]
  have hKS_mid : KeccakBufsSafe mid Nd := by
    intro gs hgs; rw [hbuf_mid gs hgs]
    have hg : AllocatorGrows state mid := ⟨heff_mid.hp_le, heff_mid.sp_le⟩
    exact ⟨(hKS_s gs hgs).1.elim Or.inl (fun h => Or.inr (hg.allocated h)),
      fun o ho => by rw [hext_mid] at ho; exact (hKS_s gs hgs).2 o ho⟩
  have heff_mid_ext : HeapByteEff state mid (nodeCacheIvls Nd ++ keccakBufIvls state ++ []) ["scratch_ptr"] :=
    heff_mid.mono (fun _ h => absurd h List.not_mem_nil) (fun _ h => h)
  have hvs_mid : NodeValuesSafe sp0 mid Nd :=
    nodeValuesSafe_of_heapByteEff hAR_s hN_s hKS_s (by decide) (by decide) heff_mid_ext
      (fun _ h => absurd h List.not_mem_nil) hvp_s
  have hkc_sp0_s := keccak_sp0_of_safe hAR_s hKS_s
  have hkc_sp0_mid : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      0 < (bufferRegion mid gs).2 →
      (bufferRegion mid gs).1 + (bufferRegion mid gs).2 ≤ globN mid "heap_ptr" ∨
        sp0 ≤ (bufferRegion mid gs).1 := by
    intro gs hgs hpos
    change 0 < (bufferRegion mid gs).2 at hpos
    change (bufferRegion mid gs).1 + (bufferRegion mid gs).2 ≤ globN mid "heap_ptr" ∨
      sp0 ≤ (bufferRegion mid gs).1
    rw [hbuf_mid gs hgs] at hpos ⊢
    rcases hkc_sp0_s gs hgs hpos with hhi | hlo
    · exact Or.inl (hhi.trans heff_mid.hp_le)
    · exact Or.inr hlo
  have hkind_mid : memW mid nodew.toNat = memW state nodew.toNat := by
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN_s.1 nodew.toNat hnode_in
    have hsz := nodeSize_ge32 (memW state nodew.toNat)
    have hal0 : Allocated state (nodew.toNat + 0, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    simpa using memW_eq_of_heapByteEff_disj (a := nodew.toNat + 0) hAR_s heff_mid hw_n.1 hal0
      (by have := hin_n.2; dsimp [nodeIvl] at this; omega)
      (fun _ hiv => absurd hiv List.not_mem_nil)
  refine ⟨heff_mid.arena, sp0, Nd, frw, nodew, hsp0_hi, hfr8,
    by rw [heff_mid.fp_eq]; exact hfp_fr, hfr_sp, hmid_sp, hwok,
    hN_mid, hKS_mid, hvs_mid, hkc_sp0_mid, hnode_in,
    by rw [hkind_mid]; exact hk_ge1, by rw [hkind_mid]; exact hk_le3,
    by rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE],
    by rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hl_node_s,
      show ofString "fr" ≠ ofString "node" by decide]⟩

private theorem hoare_prologue_stores_begin_s
    (hbeg_spec : ∀ {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (frExp nodeExp : ExpHOL 64) (frw nodew : BitVec 64),
      s.code = originalRuntimeCode → ArenaReady s → NodeHeap s Nd →
      KeccakBufsSafe s Nd → NodeValuesSafe sp0 s Nd →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
        some (.val (.word frw)) →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
        some (.val (.word nodew)) →
      Inside (frw.toNat, 48) (globN s "scratch_ptr") scratchEnd →
      frw.toNat + 48 ≤ sp0 →
      WordsOK s (frw.toNat, 48) →
      (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
        Disj (frw.toNat, 48) (bufferRegion s gs)) →
      nodew.toNat ∈ Nd →
      1 ≤ memW s nodew.toNat →
      memW s (frw.toNat + 8) = nodew.toNat →
      memW s (frw.toNat + 16) ≤ 16 →
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_begin") [frExp, nodeExp])).1 = none →
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
      ValidRlpFrame post Nd frw.toNat) :
    Hoare FillAllocReady_s
      (.seq (.store (.op .add [.var .local (ofString "fr"), .const 0]) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "fr"), .const 8]) (.var .local (ofString "node")))
          (.seq (.store (.op .add [.var .local (ofString "fr"), .const 16]) (.const 0))
            (.call (some (none, none)) (ofString "_node_rlp_begin")
              [.var .local (ofString "fr"), .var .local (ofString "node")]))))
      (fun r t => r = none → FillBeginReady_s t) := by
  refine ⟨fun {F} mid hc hP _ hnone => ?_⟩
  have h264 : heapEnd < 2 ^ 64 := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hse_he : scratchEnd ≤ heapEnd := by rw [R16Shards.WkBlockTxEnc.heapEnd_val]; decide
  have hhl_sc : heapLimit ≤ scratchStart := by decide
  obtain ⟨hAR_mid, sp0, Nd, frw, nodew, hsp0_hi, hfr8, hfp_fr, hfr_sp0, hmid_sp, hmid_W,
      hN_mid, hKS_mid, hvs_mid, hkc_sp0_mid, hnode_in, hk1, hk3, hl_mid_fr, hl_mid_node⟩ := hP
  have hfr_hi_he : frw.toNat + 48 ≤ heapEnd := by omega
  obtain ⟨hst0_none, hst0_loc, hst0_glob, hm0_st0, _, heff_st0⟩ :=
    eval_store_memW_at (s := mid) (base := frw) (w := 0) (off := 0) (len := 48)
      (Rl := [(frw.toNat, 8)]) (gw := []) hAR_mid hmid_W (by decide) (by decide) hfr_hi_he
      ⟨(frw.toNat, 8), List.mem_singleton.2 rfl, by omega, by omega⟩
      (dstExp := .op .add [.var .local (ofString "fr"), .const 0]) (valExp := .const 0)
      (by simp [evalHOLExact, evalListHOLExact, hl_mid_fr, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero])
      rfl
  set m1 := (evaluateHOLFiniteState mid
    (.store (.op .add [.var .local (ofString "fr"), .const 0]) (.const 0))).2
  obtain ⟨_, hn_rest1, hseq1⟩ := fillSeq_none mid _ _ hnone
  rw [hseq1]
  have hm1_c : m1.code = originalRuntimeCode := (evaluateHOLFiniteState_metadata mid _).1.trans hc
  have hm1_W : WordsOK m1 (frw.toNat, 48) :=
    P3MptSet.wordsOK_transfer hAR_mid.1 heff_st0.arena.1 hmid_W
  obtain ⟨hst8_none, hst8_loc, hst8_glob, hm8_st8, _, heff_st8⟩ :=
    eval_store_memW_at (s := m1) (base := frw) (w := nodew) (off := 8) (len := 48)
      (Rl := [(frw.toNat + 8, 8)]) (gw := []) heff_st0.arena hm1_W (by decide) (by decide) hfr_hi_he
      ⟨(frw.toNat + 8, 8), List.mem_singleton.2 rfl, by omega, by omega⟩
      (dstExp := .op .add [.var .local (ofString "fr"), .const 8])
      (valExp := .var .local (ofString "node"))
      (by
        have hl1 : m1.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
          rw [hst0_loc]; exact hl_mid_fr
        simp [evalHOLExact, evalListHOLExact, hl1, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by
        have hl2 : m1.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
          rw [hst0_loc]; exact hl_mid_node
        simp [evalHOLExact, hl2])
  set m2 := (evaluateHOLFiniteState m1
    (.store (.op .add [.var .local (ofString "fr"), .const 8]) (.var .local (ofString "node")))).2
  obtain ⟨_, hn_rest2, hseq2⟩ := fillSeq_none m1 _ _ hn_rest1
  rw [hseq2]
  have hm2_c : m2.code = originalRuntimeCode := (evaluateHOLFiniteState_metadata m1 _).1.trans hm1_c
  have hm2_W : WordsOK m2 (frw.toNat, 48) :=
    P3MptSet.wordsOK_transfer heff_st0.arena.1 heff_st8.arena.1 hm1_W
  obtain ⟨hst16_none, hst16_loc, hst16_glob, hm16_st16, _, heff_st16⟩ :=
    eval_store_memW_at (s := m2) (base := frw) (w := 0) (off := 16) (len := 48)
      (Rl := [(frw.toNat + 16, 8)]) (gw := []) heff_st8.arena hm2_W (by decide) (by decide) hfr_hi_he
      ⟨(frw.toNat + 16, 8), List.mem_singleton.2 rfl, by omega, by omega⟩
      (dstExp := .op .add [.var .local (ofString "fr"), .const 16]) (valExp := .const 0)
      (by
        have hl1 : m2.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
          rw [hst8_loc, hst0_loc]; exact hl_mid_fr
        simp [evalHOLExact, evalListHOLExact, hl1, wordOpHOL, wordOp, valueIsWord, valueWord])
      rfl
  set m3 := (evaluateHOLFiniteState m2
    (.store (.op .add [.var .local (ofString "fr"), .const 16]) (.const 0))).2
  obtain ⟨_, hbeg_none, hseq3⟩ := fillSeq_none m2 _ _ hn_rest2
  rw [hseq3]
  have hm3_c : m3.code = originalRuntimeCode := (evaluateHOLFiniteState_metadata m2 _).1.trans hm2_c
  have hm3_W : WordsOK m3 (frw.toNat, 48) :=
    P3MptSet.wordsOK_transfer heff_st8.arena.1 heff_st16.arena.1 hm2_W
  have hm3_sp : globN m3 "scratch_ptr" = frw.toNat := by
    unfold globN; rw [hst16_glob, hst8_glob, hst0_glob]; exact hmid_sp
  have hl_m3_fr : m3.locals.lookup (ofString "fr") = some (.val (.word frw)) := by
    rw [hst16_loc, hst8_loc, hst0_loc]; exact hl_mid_fr
  have hl_m3_node : m3.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
    rw [hst16_loc, hst8_loc, hst0_loc]; exact hl_mid_node
  have heff_mid_m3 : HeapByteEff mid m3 [(frw.toNat, 24)] [] := by
    have h0 : HeapByteEff mid m1 [(frw.toNat, 24)] [] :=
      heff_st0.mono (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        exact Or.inl ⟨(frw.toNat, 24), List.mem_singleton.2 rfl, le_rfl, by omega⟩) (by simp)
    have h8 : HeapByteEff m1 m2 [(frw.toNat, 24)] [] :=
      heff_st8.mono (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        exact Or.inl ⟨(frw.toNat, 24), List.mem_singleton.2 rfl, by omega, by omega⟩) (by simp)
    have h16 : HeapByteEff m2 m3 [(frw.toNat, 24)] [] :=
      heff_st16.mono (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        exact Or.inl ⟨(frw.toNat, 24), List.mem_singleton.2 rfl, by omega, by omega⟩) (by simp)
    exact (h0.trans h8).trans h16
  have hfr24_disj_ext : ∀ o ∈ nodeExtents mid Nd, Disj (frw.toNat, 24) o := by
    intro o ho
    obtain ⟨n, hn, ho_n⟩ := List.mem_flatMap.1 ho
    obtain ⟨_, _, hin_n, _, _, _, hkey_n, _⟩ := hN_mid.1 n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho_n
    have hfr_lo_ss : scratchStart ≤ frw.toNat := by have := hAR_mid.2.2.2.1; omega
    rcases ho_n with rfl | rfl
    · dsimp [nodeIvl, Inside] at hin_n; exact Or.inr (Or.inr (Or.inr (by dsimp [nodeIvl]; omega)))
    · dsimp [nodePath]
      split_ifs with hcond
      · rcases hkey_n hcond.1 with hz | ⟨_, _, hin_k, _⟩
        · exact absurd hz hcond.2
        · have := hin_k.2; dsimp at this; exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
      · exact Or.inr (Or.inl rfl)
  obtain ⟨hN_m3, hext_m3⟩ := nodeHeap_of_heapByteEff_disj hAR_mid hN_mid heff_mid_m3
    (fun iv hiv _ o ho => by simp only [List.mem_singleton] at hiv; subst hiv; exact hfr24_disj_ext o ho)
  have hbuf_m3 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion m3 gs = bufferRegion mid gs := by
    intro gs hgs; unfold bufferRegion globN; rw [hst16_glob, hst8_glob, hst0_glob]
  have hKS_m3 : KeccakBufsSafe m3 Nd := by
    intro gs hgs; rw [hbuf_m3 gs hgs]
    have hg : AllocatorGrows mid m3 := ⟨heff_mid_m3.hp_le, heff_mid_m3.sp_le⟩
    exact ⟨(hKS_mid gs hgs).1.elim Or.inl (fun h => Or.inr (hg.allocated h)),
      fun o ho => by rw [hext_m3] at ho; exact (hKS_mid gs hgs).2 o ho⟩
  have heff_m3_ext : HeapByteEff mid m3 (nodeCacheIvls Nd ++ keccakBufIvls mid ++ [(frw.toNat, 24)]) [] :=
    heff_mid_m3.mono
      (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        exact Or.inl ⟨(frw.toNat, 24), List.mem_append_right _ (List.mem_singleton.2 rfl), le_rfl, le_rfl⟩)
      (fun _ h => h)
  have hvs_m3 : NodeValuesSafe sp0 m3 Nd :=
    nodeValuesSafe_of_heapByteEff hAR_mid hN_mid hKS_mid (by decide) (by decide) heff_m3_ext
      (fun e he _ o ho => by simp only [List.mem_singleton] at he; subst he; exact hfr24_disj_ext o ho) hvs_mid
  have hnode_kind_m3 : memW m3 nodew.toNat = memW mid nodew.toNat := by
    obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hN_mid.1 nodew.toNat hnode_in
    have hsz := nodeSize_ge32 (memW mid nodew.toNat)
    have hal0 : Allocated mid (nodew.toNat + 0, 8) := by
      rcases hal_n with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
      · exact Or.inr ⟨by dsimp [nodeIvl] at h1; omega, by dsimp [nodeIvl] at h2; omega⟩
    simpa using memW_eq_of_heapByteEff_disj (a := nodew.toNat + 0) hAR_mid heff_mid_m3 hw_n.1 hal0
      (by have := hin_n.2; dsimp [nodeIvl] at this; omega)
      (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        have := hin_n.2; have := hAR_mid.2.2.2.1; have := hhl_sc; have := nodeSize_ge32 (memW mid nodew.toNat)
        exact Or.inr (Or.inr (Or.inl (by dsimp [nodeIvl, Inside] at *; omega))))
  have hm0_m3 : memW m3 frw.toNat = 0 := by
    have hm1_sp : globN m1 "scratch_ptr" = frw.toNat := by unfold globN; rw [hst0_glob]; exact hmid_sp
    have hm2_sp : globN m2 "scratch_ptr" = frw.toNat := by unfold globN; rw [hst8_glob, hst0_glob]; exact hmid_sp
    have hm0_m2 : memW m2 (frw.toNat + 0) = memW m1 (frw.toNat + 0) :=
      memW_eq_of_heapByteEff_disj heff_st0.arena heff_st8 hfr8
        (Or.inr ⟨by rw [hm1_sp]; omega, by omega⟩) (by omega)
        (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))
    have hm0_m3' : memW m3 (frw.toNat + 0) = memW m2 (frw.toNat + 0) :=
      memW_eq_of_heapByteEff_disj heff_st8.arena heff_st16 hfr8
        (Or.inr ⟨by rw [hm2_sp]; omega, by omega⟩) (by omega)
        (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))
    simpa using (hm0_m3'.trans hm0_m2).trans hm0_st0
  have hm8_m3 : memW m3 (frw.toNat + 8) = nodew.toNat := by
    have hm2_sp : globN m2 "scratch_ptr" = frw.toNat := by unfold globN; rw [hst8_glob, hst0_glob]; exact hmid_sp
    have hm8_m3' : memW m3 (frw.toNat + 8) = memW m2 (frw.toNat + 8) :=
      memW_eq_of_heapByteEff_disj heff_st8.arena heff_st16 (by omega)
        (Or.inr ⟨by rw [hm2_sp]; omega, by omega⟩) (by omega)
        (fun iv hiv _ => by simp only [List.mem_singleton] at hiv; subst hiv; exact Or.inr (Or.inr (Or.inl (by dsimp; omega))))
    exact hm8_m3'.trans hm8_st8
  have hfr_in_m3 : Inside (frw.toNat, 48) (globN m3 "scratch_ptr") scratchEnd :=
    ⟨by rw [hm3_sp], by omega⟩
  have hfr_kb_m3 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      Disj (frw.toNat, 48) (bufferRegion m3 gs) := by
    intro gs hgs; rw [hbuf_m3 gs hgs]
    exact disj_new_frame_keccak hAR_mid hfp_fr (by omega) hkc_sp0_mid gs hgs
  obtain ⟨hbeg_loc, heff_beg, hN_m4, hext_m4, hKS_m4, _, hm0_m4, hrf_m4⟩ :=
    hbeg_spec sp0 m3 Nd (.var .local (ofString "fr")) (.var .local (ofString "node")) frw nodew
      hm3_c heff_st16.arena hN_m3 hKS_m3 hvs_m3
      (by simp [evalHOLExact, hl_m3_fr]) (by simp [evalHOLExact, hl_m3_node])
      hfr_in_m3 (by omega) hm3_W hfr_kb_m3 hnode_in
      (by rw [hnode_kind_m3]; exact hk1) hm8_m3 (by rw [hm16_st16]; decide) hbeg_none
  set m4 := (evaluateHOLFiniteState m3
    (.call (some (none, none)) (ofString "_node_rlp_begin")
      [.var .local (ofString "fr"), .var .local (ofString "node")])).2
  have hm4_sp : globN m4 "scratch_ptr" = frw.toNat := by
    unfold globN; rw [← heff_beg.globals (ofString "scratch_ptr") (by decide)]; exact hm3_sp
  have hfr24_disj_m3 : ∀ o ∈ nodeExtents m3 Nd, Disj (frw.toNat + 24, 24) o := by
    rw [hext_m3]; intro o ho
    obtain ⟨n, hn, ho_n⟩ := List.mem_flatMap.1 ho
    obtain ⟨_, _, hin_n, _, _, _, hkey_n, _⟩ := hN_mid.1 n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho_n
    have hfr_lo_ss : scratchStart ≤ frw.toNat := by have := hAR_mid.2.2.2.1; omega
    rcases ho_n with rfl | rfl
    · dsimp [nodeIvl, Inside] at hin_n; exact Or.inr (Or.inr (Or.inr (by dsimp [nodeIvl]; omega)))
    · dsimp [nodePath]
      split_ifs with hcond
      · rcases hkey_n hcond.1 with hz | ⟨_, _, hin_k, _⟩
        · exact absurd hz hcond.2
        · have := hin_k.2; dsimp at this; exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
      · exact Or.inr (Or.inl rfl)
  have heff_beg_ext : HeapByteEff m3 m4 (nodeCacheIvls Nd ++ keccakBufIvls m3 ++ [(frw.toNat + 24, 24)]) ["heap_ptr"] :=
    heff_beg.mono
      (fun iv hiv _ => by
        simp only [List.mem_singleton] at hiv; subst hiv
        exact Or.inl ⟨(frw.toNat + 24, 24), List.mem_append_right _ (List.mem_singleton.2 rfl), le_rfl, le_rfl⟩)
      (fun _ h => h)
  have hvs_m4 : NodeValuesSafe sp0 m4 Nd :=
    nodeValuesSafe_of_heapByteEff heff_st16.arena hN_m3 hKS_m3 (by decide) (by decide) heff_beg_ext
      (fun e he _ o ho => by simp only [List.mem_singleton] at he; subst he; exact hfr24_disj_m3 o ho) hvs_m3
  have hbuf_m4 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion m4 gs = bufferRegion mid gs := by
    intro gs hgs
    have hbm3 := hbuf_m3 gs hgs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl
    · rw [← hbm3]; unfold bufferRegion globN; rw [← heff_beg.globals (ofString "keccak_pad") (by decide)]
    · rw [← hbm3]; unfold bufferRegion globN; rw [← heff_beg.globals (ofString "keccak_st") (by decide)]
  have hkc_sp0_m4 : ∀ gs ∈ ([("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      0 < (bufferRegion m4 gs).2 →
      (bufferRegion m4 gs).1 + (bufferRegion m4 gs).2 ≤ globN m4 "heap_ptr" ∨
        sp0 ≤ (bufferRegion m4 gs).1 := by
    intro gs hgs hpos
    change 0 < (bufferRegion m4 gs).2 at hpos
    change (bufferRegion m4 gs).1 + (bufferRegion m4 gs).2 ≤ globN m4 "heap_ptr" ∨
      sp0 ≤ (bufferRegion m4 gs).1
    rw [hbuf_m4 gs hgs] at hpos ⊢
    rcases hkc_sp0_mid gs hgs hpos with hhi | hlo
    · have hhp_mid_m3 : globN mid "heap_ptr" = globN m3 "heap_ptr" := by
        unfold globN; rw [hst16_glob, hst8_glob, hst0_glob]
      exact Or.inl ((hhi.trans (le_of_eq hhp_mid_m3)).trans heff_beg.hp_le)
    · exact Or.inr hlo
  exact ⟨heff_beg.arena, sp0, Nd, frw, by rw [hm4_sp]; omega, hsp0_hi, by omega,
    by simpa using hm0_m4.trans hm0_m3,
    hN_m4, hKS_m4, hvs_m4, hkc_sp0_m4, hrf_m4, by rw [hbeg_loc]; exact hl_m3_fr⟩

private theorem dec_top_init_s {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hP : FillBeginReady_s s)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "fr")) = some v) :
    FillLoopInv (setVarHOLFinite (ofString "top") v s) := by
  obtain ⟨hAR, sp0, Nd, frw, hsp_le, hsp0_hi, hfr_sp0, hm0_z, hN, hKS, hvs, hkc_sp0, hrf, hl_fr⟩ := hP
  simp only [evalHOLExact, hl_fr] at hv
  injection hv with hv'; subst hv'
  set s' := setVarHOLFinite (ofString "top") (.val (.word frw)) s
  have hloc_top : locN s' "top" = frw.toNat := by
    simp [s', locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨⟨guestInv_setVar _ _ _ hAR.1, hAR.2⟩, sp0, Nd, hsp_le, hsp0_hi, hN, hKS, hvs, hkc_sp0, ?_⟩
  rw [hloc_top]
  exact chainOK_with_locals_clock s s'.locals s'.clock sp0 Nd
    (ChainOK.chainDone s frw.toNat hrf hfr_sp0 hm0_z)



private theorem gbody__node_rlp_fill_strong_of_s
    (hbeg_spec : ∀ {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (frExp nodeExp : ExpHOL 64) (frw nodew : BitVec 64),
      s.code = originalRuntimeCode → ArenaReady s → NodeHeap s Nd →
      KeccakBufsSafe s Nd → NodeValuesSafe sp0 s Nd →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
        some (.val (.word frw)) →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
        some (.val (.word nodew)) →
      Inside (frw.toNat, 48) (globN s "scratch_ptr") scratchEnd →
      frw.toNat + 48 ≤ sp0 →
      WordsOK s (frw.toNat, 48) →
      (∀ gs ∈ [("keccak_pad", 136), ("keccak_st", 200)],
        Disj (frw.toNat, 48) (bufferRegion s gs)) →
      nodew.toNat ∈ Nd →
      1 ≤ memW s nodew.toNat →
      memW s (frw.toNat + 8) = nodew.toNat →
      memW s (frw.toNat + 16) ≤ 16 →
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_begin") [frExp, nodeExp])).1 = none →
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
      ValidRlpFrame post Nd frw.toNat)
    (hfin_spec : ∀ {F : Type} (sp0 : Nat) (s : PanSemStateFiniteExact 64 F) (Nd : List Nat)
      (frExp nodeExp : ExpHOL 64) (frw nodew : BitVec 64),
      s.code = originalRuntimeCode → ArenaReady s → NodeHeap s Nd →
      KeccakBufsSafe s Nd → NodeValuesSafe sp0 s Nd →
      globN s "scratch_ptr" ≤ sp0 →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) frExp =
        some (.val (.word frw)) →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nodeExp =
        some (.val (.word nodew)) →
      ValidRlpFrame s Nd frw.toNat →
      memW s (frw.toNat + 8) = nodew.toNat →
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_finish") [frExp, nodeExp])).1 = none →
      let post := (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "_node_rlp_finish") [frExp, nodeExp])).2
      post.locals = s.locals ∧
      ∃ totLen : Nat,
        1 ≤ totLen ∧
        globN s "heap_ptr" + totLen ≤ heapLimit ∧
        (∀ o ∈ nodeExtents s Nd, Disj (globN s "heap_ptr", totLen) o) ∧
        HeapByteEff s post
          ((globN s "heap_ptr", totLen) :: (nodeCacheIvls Nd ++ keccakBufIvls s)) ["heap_ptr"] ∧
        globN s "heap_ptr" < globN post "heap_ptr" ∧
        NodeHeap post Nd ∧
        nodeExtents post Nd = nodeExtents s Nd ∧
        KeccakBufsSafe post Nd ∧
        NodeValuesSafe sp0 post Nd ∧
        memW post (nodew.toNat + 8) = globN s "heap_ptr" ∧
        memW post (nodew.toNat + 16) = totLen ∧
        (∀ n ∈ Nd, n ≠ nodew.toNat → memW post (n + 8) = memW s (n + 8) ∧
          memW post (n + 16) = memW s (n + 16)) ∧
        (∀ n ∈ Nd, memW post n = memW s n ∧
          (1 ≤ memW s n → memW post (n + 40) = memW s (n + 40)) ∧
          (memW s n = 1 → memW post (n + 48) = memW s (n + 48) ∧
            memW post (n + 56) = memW s (n + 56))))
    (hbody_bound : TerminatingProgBoundedOn
      (fun s => GuestInv s ∧ memW s (locN s "top" + 16) ≤ 16) fillBody fillBodyCost)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hm : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark»)
    (hrel : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») :
    TerminatingFunBoundedOn NodeRlpReadyStrong (ofString "_node_rlp_fill") K.«_node_rlp_fill» := by
  refine ⟨_, _, _, lookup_fill, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn__node_rlp_fill,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  have hprologue_bound : TerminatingProgBoundedOn FillAllocReady_s
      (.seq (.store (.op .add [.var .local (ofString "fr"), .const 0]) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "fr"), .const 8]) (.var .local (ofString "node")))
          (.seq (.store (.op .add [.var .local (ofString "fr"), .const 16]) (.const 0))
            (.call (some (none, none)) (ofString "_node_rlp_begin")
              [.var .local (ofString "fr"), .var .local (ofString "node")]))))
      (0 + (0 + (0 + (K.«_node_rlp_begin» + 1)))) :=
    weakenGuard
      (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
        (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
          (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
            (TerminatingProgBoundedOn.call_guestInv hb _ _))))
      (fun s h => h.1.1)
  have hwhile : TerminatingProgBoundedOn FillLoopInv
      (.while (.cmp .notEqual (.var .local (ofString "top")) (.const 0)) fillBody)
      ((2 ^ 62 + 1) * (fillBodyCost + 1)) :=
    TerminatingProgBoundedOn.while_rank_active (N := 2 ^ 62) fillMeasure
      fillLoopInv_locals.decClock
      (weakenGuard (P := fun s => FillLoopInv s ∧
          LoopActive (.cmp .notEqual (.var .local (ofString "top")) (.const 0)) s)
        hbody_bound (fun s h => fillBody_active_scanEntry_s s h.1 h.2))
      (fun s _ hP _ => fillMeasure_le s hP.1)
      (fun s hc hP hact hflow => fillBodytep_s hbeg_spec hfin_spec s hc hP hact hflow)
  have hafter_top : TerminatingProgBoundedOn FillBeginReady_s
      (.dec (ofString "top") .one (.var .local (ofString "fr"))
        (.seq (.while (.cmp .notEqual (.var .local (ofString "top")) (.const 0)) fillBody)
          (.seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
            (.return (.const 0)))))
      ((2 ^ 62 + 1) * (fillBodyCost + 1) + ((K.«scratch_release» + 1) + 0)) :=
    dec_guard _ _ _ dec_top_init_s
      (TerminatingProgBoundedOn.seq_guestInv_after hwhile (fun s h => h.1.1)
        (TerminatingProgBoundedOn.seq_guestInv
          (TerminatingProgBoundedOn.call_guestInv hrel _ _)
          (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))
  have hreassoc : ∀ {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
      (p1 p2 p3 p4 p5 : ProgHOL 64) {k : Nat},
      TerminatingProgBoundedOn P (.seq (.seq p1 (.seq p2 (.seq p3 p4))) p5) k →
      TerminatingProgBoundedOn P (.seq p1 (.seq p2 (.seq p3 (.seq p4 p5)))) k := by
    intro P p1 p2 p3 p4 p5 k h F s hc hP
    have heq : evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 (.seq p4 p5)))) =
        evaluateHOLFiniteState s (.seq (.seq p1 (.seq p2 (.seq p3 p4))) p5) := by
      simp only [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
      cases r1 with
      | none =>
        rcases evaluateHOLFiniteState s1 p2 with ⟨r2, s2⟩
        cases r2 with
        | none =>
          rcases evaluateHOLFiniteState s2 p3 with ⟨r3, s3⟩
          cases r3 with
          | none => rfl
          | some _ => rfl
        | some _ => rfl
      | some _ => rfl
    unfold TerminatingRunBounded; dsimp only
    rw [heq]
    exact h s hc hP
  change TerminatingProgBoundedOn NodeRlpReadyStrong
    (.decCall (ofString "mark") .one (ofString "scratch_mark") []
      (.decCall (ofString "fr") .one (ofString "scratch_alloc") [.const 48]
        (.seq (.store (.op .add [.var .local (ofString "fr"), .const 0]) (.const 0))
          (.seq (.store (.op .add [.var .local (ofString "fr"), .const 8]) (.var .local (ofString "node")))
            (.seq (.store (.op .add [.var .local (ofString "fr"), .const 16]) (.const 0))
              (.seq (.call (some (none, none)) (ofString "_node_rlp_begin")
                  [.var .local (ofString "fr"), .var .local (ofString "node")])
                (.dec (ofString "top") .one (.var .local (ofString "fr"))
                  (.seq (.while (.cmp .notEqual (.var .local (ofString "top")) (.const 0)) fillBody)
                    (.seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
                      (.return (.const 0)))))))))))
    K.«_node_rlp_fill»
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hm _ .one _
      (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1.1.1) _ _)
      resume_scratch_mark_s
      (TerminatingProgBoundedOn.decCall_on ha _ .one _
        (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1.1.1) _ _)
        resume_scratch_alloc_48_s
        (hreassoc _ _ _ _ _
          (seq_hoare_to hprologue_bound (hoare_prologue_stores_begin_s hbeg_spec) hafter_top))))
    ?_
  unfold K.«_node_rlp_fill»
  change K.«scratch_mark» +
      (K.«scratch_alloc» +
        ((0 + (0 + (0 + (K.«_node_rlp_begin» + 1)))) +
          ((2 ^ 62 + 1) * (fillBodyCost + 1) + ((K.«scratch_release» + 1) + 0))) + 1) + 1 ≤
    (K.«scratch_mark» + 1) + (K.«scratch_alloc» + 1) + (K.«_node_rlp_begin» + 1) +
      (2 ^ 62 + 1) * (fillBodyCost + 1) + (K.«scratch_release» + 1)
  omega


end NodeRlpFillProof

/-- Strengthened `_node_rlp_fill`: terminates within `K.«_node_rlp_fill»` from every
`NodeRlpReadyStrong` entry state, using only the 6 callee termination bounds. -/
theorem gbody__node_rlp_fill_strong_of
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish»)
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hm : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark»)
    (hrel : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») :
    TerminatingFunBoundedOn NodeRlpReadyStrong (ofString "_node_rlp_fill") K.«_node_rlp_fill» :=
  NodeRlpFillProof.gbody__node_rlp_fill_strong_of_s
    (@NodeRlpFillProof.eval_call__node_rlp_begin_none)
    (@NodeRlpFillProof.eval_call__node_rlp_finish_none)
    (NodeRlpFillProof.fillBody_bound hn ha hb hf)
    hb ha hm hrel

/-- Strengthened `GBody.«_node_rlp_fill»` shape with `NodeRlpReadyStrong` conclusion. -/
def GBody.«_node_rlp_fill_strong» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») →
  (TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin») →
  (TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (ReadOnlyFn (ofString "_node_needs_rlp")) →
  (KeepsOn ArenaReady ArenaReady (ofString "_node_rlp_begin")) →
  (KeepsOn ArenaReady ArenaReady (ofString "_node_rlp_finish")) →
  (WritesWithin (fun _ => []) ["scratch_ptr"] (ofString "scratch_alloc")) →
  (Returns ArenaReady (fun s post p => FreshScratch s post p (locN s "n") ∧
      globN post "scratch_ptr" = p)
    (ofString "scratch_alloc")) →
  (ReadOnlyFn (ofString "scratch_mark")) →
  TerminatingFunBoundedOn NodeRlpReadyStrong (ofString "_node_rlp_fill") K.«_node_rlp_fill»

theorem «gbody__node_rlp_fill_strong» : GBody.«_node_rlp_fill_strong» :=
  fun hn hb hf ha hm hrel _ _ _ _ _ _ =>
    gbody__node_rlp_fill_strong_of hn hb hf ha hm hrel

/-- Conditional `GBody.«_node_rlp_fill»` bridge from `NodeRlpReady` to `NodeRlpReadyStrong`. -/
theorem gbody__node_rlp_fill_of_entry
    (hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      NodeRlpReady s → NodeRlpReadyStrong s) :
    InitECandidate.Solver.Wave8GuestInv.GBody.«_node_rlp_fill» :=
  fun hn hb hf ha hm hrel _ _ _ _ _ _ =>
    let ⟨ps, body, rt, hl, hprog⟩ := gbody__node_rlp_fill_strong_of hn hb hf ha hm hrel
    ⟨ps, body, rt, hl, fun s hc hP => hprog s hc (hentry s hP)⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
