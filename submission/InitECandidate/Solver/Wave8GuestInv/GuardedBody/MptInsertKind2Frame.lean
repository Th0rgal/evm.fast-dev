import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2Support

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem nodeSize_aligned (k : Nat) : nodeSize k % 8 = 0 := by
  unfold nodeSize
  split_ifs <;> decide

theorem byteCell_toNat {a : Nat} (ha : a < 2 ^ 64) :
    (panByteAlignHOL (BitVec.ofNat 64 a)).toNat = a / 8 * 8 := by
  have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
  change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
    2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
  rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha)]

/-- Nonempty MPT keys are allocated in the bump heap, below its aligned frontier. -/
theorem keyIn_heap {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {p len : Nat} (ha : ArenaReady s) (hk : KeyIn s Nd p len) (hz : len ≠ 0) :
    p + len ≤ globN s "heap_ptr" := by
  obtain ⟨_, hal, hi, _⟩ := hk.resolve_left hz
  rcases hal with hal | hal
  · exact hal.2
  · have hframe := ha.2.2.2.1
    have hscratch := ha.2.2.2.2.1
    have hheap := hi.2
    have hlo := hal.1
    change heapLimit ≤ globN s "frame_mem_ptr" at hframe
    omega

/-- Node functions preserve caller keys: old records are disjoint, and new records are fresh. -/
theorem keyIn_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {p len : Nat}
    (ha : ArenaReady s) (hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hn : NodeHeap s Nd)
    (hkinds : ∀ n ∈ Nd, memW post n = memW s n)
    (hfresh : ∀ n ∈ Nd', n ∈ Nd ∨
      Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr"))
    (hframe : FrameOutside s post
      ((Nd.map fun n => nodeIvl s n) ++
        [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    (hbe : post.be = s.be) (hk : KeyIn s Nd p len) : KeyIn post Nd' p len := by
  by_cases hz : len = 0
  · exact Or.inl hz
  have hheap := keyIn_heap ha hk hz
  obtain ⟨hnib, _, hi, hd⟩ := hk.resolve_left hz
  right
  refine ⟨?_, Or.inl ⟨hi.1, by omega⟩, hi, ?_⟩
  · intro k hkl
    have ha64 : p + k < 2 ^ 64 := by
      have hh := hi.2
      have : heapLimit < 2 ^ 64 := by decide
      omega
    let c := panByteAlignHOL (BitVec.ofNat 64 (p + k))
    have hc : c.toNat = (p + k) / 8 * 8 := byteCell_toNat ha64
    have hptr8 := ha.2.2.2.2.2.2.1
    have hfr8 := ha.2.2.2.2.2.2.2.1
    have hfrlo := ha.2.2.2.1
    have hheaphi := ha.2.2.1
    change heapLimit ≤ globN s "frame_mem_ptr" at hfrlo
    have hmem : post.memory c = s.memory c := by
      apply hframe c
      · intro i him hcHit
        rcases List.mem_append.1 him with him | him
        · obtain ⟨n, hnm, rfl⟩ := List.mem_map.1 him
          have hn8 := (hn.1 n hnm).2.2.2.1.1
          have hsz8 := nodeSize_aligned (memW s n)
          have hdisj := hd n hnm
          change n % 8 = 0 at hn8
          change n < c.toNat + 8 ∧ c.toNat < n + nodeSize (memW s n) at hcHit
          change p + len ≤ n ∨ n + nodeSize (memW s n) ≤ p at hdisj
          rw [hc] at hcHit
          rcases hdisj with hdisj | hdisj <;> omega
        · simp only [List.mem_singleton] at him
          subst i
          change globN s "frame_mem_ptr" < c.toNat + 8 ∧ _ at hcHit
          rw [hc] at hcHit
          omega
      · intro hcHit
        change globN s "heap_ptr" < c.toNat + 8 ∧ _ at hcHit
        rw [hc] at hcHit
        omega
    have hb : memB post (p + k) = memB s (p + k) := by
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL _ v post.be).toNat) =
        (match s.memory c with | .word v => (panGetByteHOL _ v s.be).toNat)
      rw [hmem, hbe]
    rw [hb]
    exact hnib k hkl
  · intro n hnm
    rcases hfresh n hnm with hold | hnew
    · simpa only [nodeIvl, hkinds n hold] using hd n hold
    · exact Or.inl (by have := hnew.1; omega)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
