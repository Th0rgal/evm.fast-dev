import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet_Params

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.style.nameCheck false
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.P3MptSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def IvlUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  ∀ a : BitVec 64, a.toNat % 8 = 0 → CellHits a.toNat i → post.memory a = s.memory a

theorem ivlUnhit_of_frameOutside {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk : ∀ j ∈ keep, (j.1 % 8 = 0 ∧ j.2 % 8 = 0 ∧ Disj i j) ∨ j.1 + j.2 + 8 ≤ i.1)
    (hf_al : fresh.1 % 8 = 0 ∧ fresh.2 % 8 = 0)
    (hf : Disj i fresh) (hi : i.2 ≠ 0) :
    IvlUnhit s post i := by
  intro a ha8 hhit
  obtain ⟨hi1, hi2⟩ := hhit
  apply hfr a
  · intro j hj hcj
    obtain ⟨hc1, hc2⟩ := hcj
    rcases hk j hj with ⟨hj1, hj2, hdisj⟩ | hfar
    · rcases hdisj with hd | hd | hd | hd <;> omega
    · omega
  · intro hcf
    obtain ⟨hf1, hf2⟩ := hf_al
    obtain ⟨hc1, hc2⟩ := hcf
    rcases hf with hd | hd | hd | hd <;> omega

theorem memW_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) {a : Nat}
    (ha8 : a % 8 = 0) (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) :
    memW post a = memW s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  have hmem := hu (BitVec.ofNat 64 a)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; exact ha8)
    (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]; omega)
  unfold memW
  rw [hmem]

theorem memB_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {i : Ivl} (hu : IvlUnhit s post i) (hbe : post.be = s.be)
    {a : Nat} (hhi : i.1 + i.2 ≤ 2 ^ 64) (hin : i.1 ≤ a ∧ a < i.1 + i.2) :
    memB post a = memB s a := by
  have ha_lt : a < 2 ^ 64 := by omega
  let c := panByteAlignHOL (BitVec.ofNat 64 a)
  have hc_nat : c.toNat = a / 8 * 8 := by
    have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
    change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
      2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
    rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha_lt)]
  have hmem := hu c (by rw [hc_nat]; omega) (by unfold CellHits; rw [hc_nat]; omega)
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v post.be).toNat) =
         (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat)
  rw [hmem, hbe]

theorem wordsOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hgP.memaddrs, ← hgS.memaddrs]
  exact hdom

theorem nodeHeap_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) (hbe : post.be = s.be)
    (hag : AllocatorGrows s post)
    {Nd : List Nat} (hN : NodeHeap s Nd)
    (hu : ∀ o ∈ nodeExtents s Nd, o.2 ≠ 0 → IvlUnhit s post o) :
    NodeHeap post Nd := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hn_props : ∀ n ∈ Nd,
      memW post n = memW s n ∧
      nodeIvl post n = nodeIvl s n ∧
      (∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k)) ∧
      ((memW s n = 1 ∨ memW s n = 2) → KeyIn post Nd (memW post (n + 32)) (memW post (n + 40))) := by
    intro n hn
    obtain ⟨hk3, hal_n, hin_n, hw_n, _, _, hkey_n, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
      have := hin_n.2; dsimp [nodeIvl] at this; omega
    have hn8 : n % 8 = 0 := hw_n.1
    have hsz_ge32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) :=
      hu _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩) (by dsimp only; omega)
    have hw_k : ∀ k, k < nodeSize (memW s n) / 8 → memW post (n + 8 * k) = memW s (n + 8 * k) := by
      intro k hk
      have hsz8 : nodeSize (memW s n) % 8 = 0 := by unfold nodeSize; split_ifs <;> omega
      exact memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
    have hw0 : memW post n = memW s n := by simpa using hw_k 0 (by omega)
    have hivl_eq : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hw0]
    exact ⟨hw0, hivl_eq, hw_k, fun h12 => by
      have hsz_ge56 : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize
        rcases h12 with h1 | h2
        · simp [h1]
        · simp [h2]
      have hw32 : memW post (n + 32) = memW s (n + 32) := hw_k 4 (by omega)
      have hw40 : memW post (n + 40) = memW s (n + 40) := hw_k 5 (by omega)
      rw [hw32, hw40]
      by_cases hlen0 : memW s (n + 40) = 0
      · exact Or.inl hlen0
      · rcases hkey_n h12 with h0 | ⟨hnib, hal_p, hin_p, hdisj_p⟩
        · exact Or.inl h0
        · right
          have hu_p : IvlUnhit s post (memW s (n + 32), memW s (n + 40)) :=
            hu _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩) hlen0
          refine ⟨fun k hk => ?_, hag.allocated hal_p, hin_p, ?_⟩
          · rw [memB_eq_of_ivlUnhit hu_p hbe (by have := hin_p.2; omega) ⟨by omega, by omega⟩]
            exact hnib k hk
          · intro m hm
            have hhm_hi : m + nodeSize (memW s m) ≤ 2 ^ 64 := by
              have := (hN.1 m hm).2.2.1.2; dsimp [nodeIvl] at this; omega
            have hm8 : m % 8 = 0 := (hN.1 m hm).2.2.2.1.1
            have hsz_m : 32 ≤ nodeSize (memW s m) := by unfold nodeSize; split_ifs <;> omega
            have hu_m : IvlUnhit s post (m, nodeSize (memW s m)) :=
              hu _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨m, hm, by simp [nodeIvl]⟩) (by dsimp only; omega)
            have hwm : memW post m = memW s m :=
              memW_eq_of_ivlUnhit hu_m hm8 hhm_hi ⟨by omega, by omega⟩
            simp [nodeIvl, hwm]
            exact hdisj_p m hm⟩
  refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
  · obtain ⟨hk3, hal_n, hin_n, hw_n, hext, hbr, _, hcache, hleaf, hbranch⟩ := hN.1 n hn
    obtain ⟨hw0, hivl_eq, hw_k, hkey_post⟩ := hn_props n hn
    rw [hw0, hivl_eq]
    refine ⟨hk3, hag.allocated hal_n, hin_n, wordsOK_transfer hgS hgP hw_n, ?_, ?_, hkey_post, ?_, ?_, ?_⟩
    · intro h2
      have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
      have hw48 := hw_k 6 (by omega)
      simpa only [Nat.mul_succ, Nat.mul_zero] using (by rw [hw48]; exact hext h2 : RootIn Nd (memW post (n + 48)))
    · intro h3 i hi
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have hw_ch := hw_k (4 + i) (by omega)
      have hadd : n + 8 * (4 + i) = n + 32 + 8 * i := by omega
      rw [← hadd, hw_ch, hadd]
      exact hbr h3 i hi
    · have hsz : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have he := hw_k 2 (by omega)
      simpa only [Nat.reduceMul, he] using hcache
    · intro h1
      have hsz : nodeSize (memW s n) = 64 := by simp [nodeSize, h1]
      have he := hw_k 7 (by omega)
      simpa only [Nat.reduceMul, he] using hleaf h1
    · intro h3
      have hsz : nodeSize (memW s n) = 176 := by simp [nodeSize, h3]
      have he := hw_k 21 (by omega)
      simpa only [Nat.reduceMul, he] using hbranch h3
  · rw [(hn_props n hn).2.1, (hn_props m hm).2.1]
    exact hN.2 n hn m hm hne

theorem disj_allocated_heapFree {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) {i : Ivl} (hi : Allocated s i) :
    Disj i (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
  apply Or.inr ∘ Or.inr
  rcases hi with hi | hi
  · exact Or.inl hi.2
  · have hsep : heapLimit ≤ scratchStart := by decide
    have := hs.1; have := hs.2.1; have := hs.2.2.1; have := hs.2.2.2.1; have := hi.1
    exact Or.inr (by dsimp only; omega)

theorem disj_allocated_freeGap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : ArenaOK s) {i : Ivl} (hi : Allocated s i) :
    Disj i (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr") := by
  apply Or.inr ∘ Or.inr
  rcases hi with hi | hi
  · have hsep : heapLimit ≤ scratchStart := by decide
    have := hs.2.1; have := hs.2.2.1; have := hi.2
    exact Or.inl (by dsimp only; omega)
  · have := hs.2.2.2.1; have := hi.1
    exact Or.inr (by dsimp only; omega)

theorem ivl_allocated_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hal : Allocated s i) :
    i.1 + i.2 ≤ 2 ^ 64 := by
  have h1 : heapLimit ≤ heapEnd := by decide
  have h2 : scratchEnd ≤ heapEnd := by decide
  have h3 : heapEnd < 2 ^ 64 := by decide
  rcases hal with ⟨_, hi⟩ | ⟨_, hi⟩
  · have := hA.2.1; omega
  · have := hA.2.2.2.2.1; omega

theorem buf_in_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (sz : Nat) (hmem : (name, sz) ∈ globalBuffers) (hnz : globN s name ≠ 0) :
    (globN s name, sz) ∈ fixedObjects s := by
  have hbuf : (globN s name, sz) ∈
      globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) := by
    refine List.mem_map.mpr ⟨(name, sz), hmem, ?_⟩
    simp [hnz]
  simp only [fixedObjects, List.mem_append]
  exact Or.inl (Or.inl (Or.inl hbuf))

theorem buf_keep_cond {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) {i : Ivl} (hlo : sourceBase ≤ i.1) (hdisj : ∀ j ∈ fixedObjects s, Disj i j)
    (name : String) (sz : Nat) (hmem : (name, sz) ∈ globalBuffers)
    (hsz8 : sz % 8 = 0) (hsz0 : sz ≠ 0) (hsz_le : sz + 8 ≤ sourceBase) :
    (globN s name % 8 = 0 ∧ sz % 8 = 0 ∧ Disj i (globN s name, sz)) ∨
      globN s name + sz + 8 ≤ i.1 := by
  by_cases hnz : globN s name = 0
  · right; rw [hnz]; omega
  · left
    have hfix := buf_in_fixedObjects s name sz hmem hnz
    rcases hF.1 _ hfix with hz | ⟨_, hw⟩
    · exact absurd hz hsz0
    · exact ⟨hw.1, hsz8, hdisj _ hfix⟩

end InitECandidate.Solver.Wave8GuestInv.P3MptSet
