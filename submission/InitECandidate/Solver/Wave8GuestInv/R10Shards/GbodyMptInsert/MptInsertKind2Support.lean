import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptCuts

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem kind2_nodeSize_ne_zero (k : Nat) : nodeSize k ≠ 0 := by
  unfold nodeSize
  split_ifs <;> decide

/-- Clock accounting for a whole insertion iteration, independently of its node kind. -/
theorem mptInsert_body_bound (h : MptInsertCallees) :
    TerminatingProgBoundedOn GuestInv mptInsertBody mptInsertCost := by
  simp only [mptInsertBody, mptInsertTail, mptInsertCode, mptDecBody, mptLeft,
    mptWhileBody, sourceFunctionEntry, Guest.Software.guestFn__mpt_insert_node,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  apply RunFramesRace.TerminatingProgBoundedOn.mono_bound
  · repeat' first
      | apply TerminatingProgBoundedOn.seq_guestInv
      | apply TerminatingProgBoundedOn.ite_on
      | apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
      | apply TerminatingProgBoundedOn.decCall_guestInv h.fb_common_prefix_length
      | apply TerminatingProgBoundedOn.decCall_guestInv h.fb__split_extension
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_new_leaf _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_mpt_fail _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_invalidate _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb__insert_into_leaf _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_common_prefix_length _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb__split_extension _ _
      | exact TerminatingProgBoundedOn.call_guestInv h.fb_node_new_ext _ _
      | exact fun s hc _ => TerminatingProgBounded.straight _ rfl s hc
  · simp only [mptInsertCost, Nat.zero_add, Nat.add_zero, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.max_self, Nat.le_refl]

theorem keyIn_subrange {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {p len off size : Nat} (hk : KeyIn s Nd p len)
    (hr : off + size ≤ len) : KeyIn s Nd (p + off) size := by
  by_cases hz : size = 0
  · exact Or.inl hz
  rcases hk with hzero | ⟨hn, ha, hi, hd⟩
  · omega
  right
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    simpa only [Nat.add_assoc] using hn (off + k) (by omega)
  · rcases ha with ha | ha
    · exact Or.inl ⟨by have := ha.1; omega, by have := ha.2; omega⟩
    · exact Or.inr ⟨by have := ha.1; omega, by have := ha.2; omega⟩
  · exact ⟨by have := hi.1; omega, by have := hi.2; omega⟩
  · intro n hn
    rcases hd n hn with hd | hd
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- A non-null parent pointer is in the child-pointer part of a node record. -/
theorem mptSlot_interval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : MptSlotOK s Nd) (hz : locN s "slot" ≠ 0) :
    ∃ p ∈ Nd, p + 32 ≤ locN s "slot" ∧
      locN s "slot" + 8 ≤ p + nodeSize (memW s p) ∧
      memW s (locN s "slot") = locN s "node" := by
  obtain ⟨p, hp, hk, hv⟩ := hs.resolve_left hz
  refine ⟨p, hp, ?_, ?_, hv⟩
  · rcases hk with ⟨_, he⟩ | ⟨_, i, _, he⟩ <;> omega
  · rcases hk with ⟨ht, he⟩ | ⟨ht, i, hi, he⟩
    · simp [ht, nodeSize, he] <;> omega
    · simp [ht, nodeSize, he] <;> omega

/-- The parent pointer is disjoint from the three cache cells, including self-links. -/
theorem mptSlot_ne_cache {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hn : NodeHeap s Nd) (hc : locN s "node" ∈ Nd)
    (ht : memW s (locN s "node") = 2) (hs : MptSlotOK s Nd)
    (hz : locN s "slot" ≠ 0) :
    locN s "slot" ≠ locN s "node" + 8 ∧
    locN s "slot" ≠ locN s "node" + 16 ∧
    locN s "slot" ≠ locN s "node" + 24 := by
  obtain ⟨p, hp, hlo, hhi, _⟩ := mptSlot_interval hs hz
  by_cases he : p = locN s "node"
  · subst p
    omega
  · have hd := hn.2 p hp (locN s "node") hc he
    simp only [Disj, nodeIvl, kind2_nodeSize_ne_zero, false_or] at hd
    change p + nodeSize (memW s p) ≤ locN s "node" ∨
      locN s "node" + nodeSize (memW s (locN s "node")) ≤ p at hd
    rw [ht] at hd
    change p + nodeSize (memW s p) ≤ locN s "node" ∨ locN s "node" + 56 ≤ p at hd
    rcases hd with hd | hd <;> omega

theorem clearCache_memory_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nd a : Nat) (ha : a < 2 ^ 64) (hn : nd + 24 < 2 ^ 64)
    (h8 : a ≠ nd + 8) (h16 : a ≠ nd + 16) (h24 : a ≠ nd + 24) :
    (clearCache s nd).memory (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a) := by
  have hne (k : Nat) (hk : k ≤ 24) (hne : a ≠ nd + k) :
      BitVec.ofNat 64 a ≠ BitVec.ofNat 64 (nd + k) := by
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (show nd + k < 2 ^ 64 by omega)] at he'
    exact hne he'
  simp only [clearCache, hne 8 (by omega) h8, hne 16 (by omega) h16,
    hne 24 (by omega) h24, or_self, if_false]

/-- The store performed after extension descent writes the pointer already in the parent. -/
theorem mptSlot_store_redundant {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hn : NodeHeap s Nd) (hc : locN s "node" ∈ Nd)
    (ht : memW s (locN s "node") = 2) (hs : MptSlotOK s Nd)
    (hz : locN s "slot" ≠ 0) :
    clearCacheAndStore s (locN s "node") (locN s "slot") =
      clearCache s (locN s "node") := by
  obtain ⟨p, hp, _, hslot, hvalue⟩ := mptSlot_interval hs hz
  have hlimit : heapLimit < 2 ^ 64 := by decide
  have hpbound := (hn.1 p hp).2.2.1.2
  have hnbound := (hn.1 (locN s "node") hc).2.2.1.2
  change locN s "node" + nodeSize (memW s (locN s "node")) ≤ heapLimit at hnbound
  rw [ht] at hnbound
  change locN s "node" + 56 ≤ heapLimit at hnbound
  change p + nodeSize (memW s p) ≤ heapLimit at hpbound
  obtain ⟨h8, h16, h24⟩ := mptSlot_ne_cache hn hc ht hs hz
  have hmem := clearCache_memory_eq s (locN s "node") (locN s "slot")
    (by omega) (by omega) h8 h16 h24
  have hword : s.memory (BitVec.ofNat 64 (locN s "slot")) =
      HolWordLab.word (BitVec.ofNat 64 (locN s "node")) := by
    cases he : s.memory (BitVec.ofNat 64 (locN s "slot")) with
    | word w =>
      change (match s.memory (BitVec.ofNat 64 (locN s "slot")) with
        | .word w => w.toNat) = locN s "node" at hvalue
      rw [he] at hvalue
      congr 1
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show locN s "node" < 2 ^ 64 by omega)]
        using hvalue
  dsimp only [clearCacheAndStore]
  suffices hm : (fun a => if a = BitVec.ofNat 64 (locN s "slot")
      then HolWordLab.word (BitVec.ofNat 64 (locN s "node"))
      else (clearCache s (locN s "node")).memory a) = (clearCache s (locN s "node")).memory by
    rw [hm]
  funext a
  split
  · rename_i he
    subst a
    exact (hmem.trans hword).symm
  · rfl

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
