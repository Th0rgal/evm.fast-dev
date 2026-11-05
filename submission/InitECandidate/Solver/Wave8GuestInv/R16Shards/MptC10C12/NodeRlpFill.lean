import InitECandidate.Solver.Wave8GuestInv.ContractParts.C10
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexed

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
