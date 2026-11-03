import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCuts

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem mpt_nodeSize_bounds (k : Nat) : 32 ≤ nodeSize k ∧ nodeSize k ≤ 176 := by
  unfold nodeSize
  split_ifs <;> omega

theorem mpt_byteAlign_bounds (a : Nat) (ha : a < 2 ^ 64) :
    (panByteAlignHOL (BitVec.ofNat 64 a)).toNat ≤ a ∧
      a < (panByteAlignHOL (BitVec.ofNat 64 a)).toNat + 8 := by
  have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha)]
  omega

theorem mpt_clearCache_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : Nat) (hn : n + 24 < 2 ^ 64) (a : BitVec 64)
    (h8 : a.toNat ≠ n + 8) (h16 : a.toNat ≠ n + 16) (h24 : a.toNat ≠ n + 24) :
    (clearCache s n).memory a = s.memory a := by
  have hne (k : Nat) (hk : k ≤ 24) (h : a.toNat ≠ n + k) :
      a ≠ BitVec.ofNat 64 (n + k) := by
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n + k < 2 ^ 64 by omega)] at this
    exact h this
  simp only [clearCache, if_neg (show ¬ (a = BitVec.ofNat 64 (n + 8) ∨
    a = BitVec.ofNat 64 (n + 16) ∨ a = BitVec.ofNat 64 (n + 24)) from
      not_or.mpr ⟨hne 8 (by omega) h8, not_or.mpr ⟨hne 16 (by omega) h16,
        hne 24 (by omega) h24⟩⟩)]

theorem mpt_clearCache_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : Nat) (hn : n + 24 < 2 ^ 64) (a : Nat) (ha : a < 2 ^ 64)
    (h8 : a ≠ n + 8) (h16 : a ≠ n + 16) (h24 : a ≠ n + 24) :
    memW (clearCache s n) a = memW s a := by
  unfold memW
  rw [mpt_clearCache_memory s n hn _]
  all_goals simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-- Invalidating cache fields preserves all kinds and non-cache node fields. -/
theorem mpt_clearCache_fields {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (hN : NodeHeap s Nd) (n : Nat) (hn : n ∈ Nd) :
    ∀ m ∈ Nd, ∀ off, (off = 0 ∨ 32 ≤ off) → off < nodeSize (memW s m) →
      memW (clearCache s n) (m + off) = memW s (m + off) := by
  intro m hm off hoff hsz
  have hb := (hN.1 n hn).2.2.1
  have hmB := (hN.1 m hm).2.2.1
  have hsn := mpt_nodeSize_bounds (memW s n)
  have hsm := mpt_nodeSize_bounds (memW s m)
  have hlim : heapLimit < 2 ^ 64 := by decide
  dsimp only [Inside, nodeIvl] at hb hmB
  apply mpt_clearCache_word s n (by omega) (m + off) (by omega)
  all_goals
    by_cases he : m = n
    · subst m; rcases hoff with rfl | hoff <;> omega
    · have hd := hN.2 m hm n hn he
      dsimp only [Disj, nodeIvl] at hd
      omega

/-- Nibble arrays disjoint from node records survive cache invalidation. -/
theorem mpt_clearCache_key {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (hN : NodeHeap s Nd) (n : Nat) (hn : n ∈ Nd)
    (p len : Nat) (hK : KeyIn s Nd p len) : KeyIn (clearCache s n) Nd p len := by
  have hkinds : ∀ m ∈ Nd, memW (clearCache s n) m = memW s m := by
    intro m hm
    simpa only [Nat.add_zero] using
      mpt_clearCache_fields s Nd hN n hn m hm 0 (Or.inl rfl)
        (by have := mpt_nodeSize_bounds (memW s m); omega)
  rcases hK with h0 | ⟨hnib, hal, hin, hd⟩
  · exact Or.inl h0
  · refine Or.inr ⟨?_, hal, hin, ?_⟩
    · intro k hk
      have hb := (hN.1 n hn).2.2.1
      have hs := mpt_nodeSize_bounds (memW s n)
      have hlim : heapLimit < 2 ^ 64 := by decide
      have hdis := hd n hn
      dsimp only [Inside, nodeIvl, Disj] at hb hin hdis
      have ha : p + k < 2 ^ 64 := by omega
      have hcell := mpt_byteAlign_bounds (p + k) ha
      have hm := mpt_clearCache_memory s n (by omega)
        (panByteAlignHOL (BitVec.ofNat 64 (p + k))) (by omega) (by omega) (by omega)
      simpa only [memB, hm, show (clearCache s n).be = s.be from rfl] using hnib k hk
    · intro m hm
      simpa only [nodeIvl, hkinds m hm] using hd m hm

theorem mpt_clearCache_heap {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (hN : NodeHeap s Nd) (n : Nat) (hn : n ∈ Nd) :
    NodeHeap (clearCache s n) Nd := by
  have hf := mpt_clearCache_fields s Nd hN n hn
  have hk : ∀ m ∈ Nd, memW (clearCache s n) m = memW s m := by
    intro m hm
    simpa only [Nat.add_zero] using hf m hm 0 (Or.inl rfl)
      (by have := mpt_nodeSize_bounds (memW s m); omega)
  have hi : ∀ m ∈ Nd, nodeIvl (clearCache s n) m = nodeIvl s m := by
    intro m hm; simp only [nodeIvl, hk m hm]
  refine ⟨?_, ?_⟩
  · intro m hm
    obtain ⟨h3, ha, hin, hw, he, hb, hp⟩ := hN.1 m hm
    rw [hk m hm, hi m hm]
    refine ⟨h3, ha, hin, ?_, ?_, ?_, ?_⟩
    · obtain ⟨h1, h2, hwords⟩ := hw
      refine ⟨h1, h2, fun k hk => ?_⟩
      obtain ⟨_, hdom, _⟩ := hwords k hk
      cases hc : (clearCache s n).memory (BitVec.ofNat 64 ((nodeIvl s m).1 + 8 * k)) with
      | word w => exact ⟨w, hdom, hc⟩
    · intro hm2
      rw [hf m hm 48 (Or.inr (by omega)) (by simp [nodeSize, hm2])]
      exact he hm2
    · intro hm3 i hi
      have heq : m + 32 + 8 * i = m + (32 + 8 * i) := by omega
      rw [heq, hf m hm (32 + 8 * i) (Or.inr (by omega))
        (by simp only [nodeSize, hm3]; norm_num; omega), ← heq]
      exact hb hm3 i hi
    · intro hm12
      have hs : 56 ≤ nodeSize (memW s m) := by
        rcases hm12 with hm1 | hm2 <;> simp [nodeSize, *]
      rw [hf m hm 32 (Or.inr (by omega)) (by omega),
        hf m hm 40 (Or.inr (by omega)) (by omega)]
      exact mpt_clearCache_key s Nd hN n hn _ _ (hp hm12)
  · intro m hm p hp hne
    rw [hi m hm, hi p hp]
    exact hN.2 m hm p hp hne

/-- A suffix of a nibble key remains a key for the same node heap. -/
theorem mpt_key_suffix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (p len d : Nat) (hd : d ≤ len) (hK : KeyIn s Nd p len) :
    KeyIn s Nd (p + d) (len - d) := by
  by_cases hz : len - d = 0
  · exact Or.inl hz
  · rcases hK with h0 | ⟨hn, ha, hi, hdis⟩
    · omega
    · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
      · intro k hk
        have h := hn (d + k) (by omega)
        simpa only [Nat.add_assoc] using h
      · rcases ha with ha | ha
        · exact Or.inl ⟨by have := ha.1; omega, by have := ha.2; omega⟩
        · exact Or.inr ⟨by have := ha.1; omega, by have := ha.2; omega⟩
      · exact ⟨by have := hi.1; omega, by have := hi.2; omega⟩
      · intro n hn
        rcases hdis n hn with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)

theorem mpt_clearCache_slot {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (hN : NodeHeap s Nd) (n : Nat) (hn : n ∈ Nd)
    (hS : MptSlotOK s Nd) : MptSlotOK (clearCache s n) Nd := by
  rcases hS with h0 | ⟨p, hp, hslot, hvalue⟩
  · exact Or.inl h0
  · refine Or.inr ⟨p, hp, ?_, ?_⟩
    · have hk := mpt_clearCache_fields s Nd hN n hn p hp 0 (Or.inl rfl)
        (by have := mpt_nodeSize_bounds (memW s p); omega)
      simp only [Nat.add_zero] at hk
      change (memW (clearCache s n) p = 2 ∧ locN s "slot" = p + 48) ∨
        (memW (clearCache s n) p = 3 ∧ ∃ i, i < 16 ∧ locN s "slot" = p + 32 + 8 * i)
      rw [hk]
      exact hslot
    · change memW (clearCache s n) (locN s "slot") = locN s "node"
      rw [← hvalue]
      rcases hslot with ⟨hk, hs⟩ | ⟨hk, i, hi, hs⟩
      · rw [hs]
        exact mpt_clearCache_fields s Nd hN n hn p hp 48 (Or.inr (by omega))
          (by simp [nodeSize, hk])
      · have hs' : locN s "slot" = p + (32 + 8 * i) := by omega
        rw [hs']
        exact mpt_clearCache_fields s Nd hN n hn p hp (32 + 8 * i) (Or.inr (by omega))
          (by simp [nodeSize, hk]; omega)

theorem mpt_nodeHeap_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) (Nd : List Nat) :
    NodeHeap {s with locals := locals, clock := clock} Nd ↔ NodeHeap s Nd := Iff.rfl

theorem mpt_keyIn_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) (Nd : List Nat) (p len : Nat) :
    KeyIn {s with locals := locals, clock := clock} Nd p len ↔ KeyIn s Nd p len := Iff.rfl

theorem mpt_locN_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) :
    locN s name < 2 ^ 64 := by
  unfold locN
  split
  · exact BitVec.isLt _
  · omega

theorem mpt_local_word {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
    (h : locN s name ≠ 0) : ∃ w : BitVec 64,
      s.locals.lookup (ofString name) = some (.val (.word w)) ∧ locN s name = w.toNat := by
  unfold locN at h ⊢
  split at h
  · rename_i w hw
    exact ⟨w, hw, by simp only [hw]⟩
  · contradiction

theorem mpt_node_field_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (hN : NodeHeap s Nd) (n : Nat) (hn : n ∈ Nd)
    (off : Nat) (hal : off % 8 = 0) (hoff : off < nodeSize (memW s n)) :
    s.memaddrs (BitVec.ofNat 64 (n + off)) := by
  have hw := (hN.1 n hn).2.2.2.1
  have hk : off / 8 < (nodeIvl s n).2 / 8 := by
    change off / 8 < nodeSize (memW s n) / 8
    have := hw.2.1
    change nodeSize (memW s n) % 8 = 0 at this
    omega
  have hd := (hw.2.2 (off / 8) hk).choose_spec.1
  have heq : (nodeIvl s n).1 + 8 * (off / 8) = n + off := by
    dsimp only [nodeIvl]; omega
  simpa only [heq] using hd

theorem mpt_memW_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a : Nat) (w : BitVec 64) (h : memW s a = w.toNat) :
    s.memory (BitVec.ofNat 64 a) = .word w := by
  cases hm : s.memory (BitVec.ofNat 64 a) with
  | word v =>
    have hv : v = w := by
      apply BitVec.eq_of_toNat_eq
      simpa only [memW, hm] using h
    simpa only [hv]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
