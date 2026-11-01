import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Flow

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptKeyIn_sub {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {p len q size : Nat} (hk : KeyIn s Nd p len)
    (hpq : p ≤ q) (hhi : q + size ≤ p + len) : KeyIn s Nd q size := by
  by_cases hz : size = 0
  · exact Or.inl hz
  · rcases hk with hl | ⟨hnib, hal, hi, hd⟩
    · omega
    · right
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk
        have heq : q + k = p + (q - p + k) := by omega
        rw [heq]
        exact hnib _ (by omega)
      · rcases hal with hal | hal <;> [left; right] <;> constructor <;> dsimp [Inside] at * <;> omega
      · constructor <;> dsimp [Inside] at * <;> omega
      · intro n hn
        have hh := hd n hn
        unfold Disj at hh ⊢
        dsimp only at hh ⊢
        rcases hh with hh | hh
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)

theorem mptStack_addresses {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} : ∀ fs p, MptStack s Nd p fs →
      ∀ q ∈ fs, globN s "scratch_ptr" ≤ q := by
  intro fs
  induction fs with
  | nil => simp
  | cons f fs ih =>
    intro p hs q hq
    obtain ⟨rfl, _, hf, _, ht⟩ := hs
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hf.1.1
    · exact ih _ ht q hq

theorem mptFreeFrame_stack {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hs : ArenaReady s) (ht : ArenaReady t) (hbe : t.be = s.be)
    (hg : AllocatorGrows s t) (hN : NodeHeap s Nd)
    (hfr : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    ∀ fs p, MptStack s Nd p fs → MptStack t Nd p fs := by
  obtain ⟨_, hkeys, hkind⟩ := mptFreeFrame_heap hs ht hbe hg hN hfr
  apply mptStack_transfer hs.1 ht.1 hg (fun _ hn => hn) hkind hkeys
  intro a hlo hhi _
  apply mptScratch_nodeFrame hs hN (a := a) ?_ hlo hhi
  intro a hk hf
  exact hfr a (fun i hi => hk i (List.mem_append_right _ hi)) hf

theorem mptFreeFrame_write {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {a : Nat} (w : BitVec 64)
    (ha : globN s "frame_mem_ptr" ≤ a ∧ a + 8 ≤ globN s "scratch_ptr")
    (ha64 : a < 2 ^ 64)
    (hf : FrameOutside s t
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    FrameOutside s (mptWordWrite t a w)
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
  intro b hk hheap
  have hne : b ≠ BitVec.ofNat 64 a := by
    intro heq
    subst b
    have hn : (BitVec.ofNat 64 a).toNat = a := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]
    have hh := hk _ (List.mem_singleton_self _)
    rw [hn] at hh
    apply hh
    change globN s "frame_mem_ptr" < a + 8 ∧
      a < globN s "frame_mem_ptr" + (globN s "scratch_ptr" - globN s "frame_mem_ptr")
    constructor <;> omega
  simpa only [mptWordWrite, hne, if_false] using hf b hk hheap

theorem mptWordWrite_same {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a : Nat) (w : BitVec 64) : memW (mptWordWrite s a w) a = w.toNat := by
  simp [mptWordWrite, memW]

theorem mptLocal_word {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    {v : BitVec 64} (h : s.locals.lookup (ofString n) = some (.val (.word v))) :
    locN s n = v.toNat := by simp only [locN, h]

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
