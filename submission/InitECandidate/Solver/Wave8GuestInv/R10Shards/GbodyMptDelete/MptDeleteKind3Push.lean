import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Alloc

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
def mptBranchFrame {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat)
    (top node idx : BitVec 64) : PanSemStateFiniteExact 64 F :=
  mptWordWrite (mptWordWrite (mptWordWrite (mptWordWrite s p top) (p + 8) node)
    (p + 16) 3) (p + 32) idx

theorem mptBranchFrame_reads {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat)
    (top node idx : BitVec 64) (hp : p + 40 < 2 ^ 64) :
    memW (mptBranchFrame s p top node idx) p = top.toNat ∧
    memW (mptBranchFrame s p top node idx) (p + 8) = node.toNat ∧
    memW (mptBranchFrame s p top node idx) (p + 16) = 3 ∧
    memW (mptBranchFrame s p top node idx) (p + 32) = idx.toNat := by
  unfold mptBranchFrame
  constructor
  · rw [mptWordWrite_memW_ne _ idx (by omega) (by omega) (by omega),
      mptWordWrite_memW_ne _ 3 (by omega) (by omega) (by omega),
      mptWordWrite_memW_ne _ node (by omega) (by omega) (by omega), mptWordWrite_same]
  constructor
  · rw [mptWordWrite_memW_ne _ idx (by omega) (by omega) (by omega),
      mptWordWrite_memW_ne _ 3 (by omega) (by omega) (by omega), mptWordWrite_same]
  constructor
  · rw [mptWordWrite_memW_ne _ idx (by omega) (by omega) (by omega), mptWordWrite_same]
    rfl
  · exact mptWordWrite_same _ _ _

theorem mptBranchFrame_push {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {Nd fs : List Nat} {oldtop p : Nat} {top node idx : BitVec 64}
    (hs : ArenaReady s) (hu : ArenaReady u) (hbe : u.be = s.be)
    (hg : AllocatorGrows s u) (hfresh : FreshScratch s u p 40)
    (hn : NodeHeap s Nd) (hst : MptStack s Nd oldtop fs)
    (htop : top.toNat = oldtop) (hnode : node.toNat ∈ Nd) (hkind : memW s node.toNat = 3)
    (hi : idx.toNat < 16)
    (hfr : FrameOutside s u
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr")) :
    let d := mptBranchFrame u p top node idx
    ArenaReady d ∧ NodeHeap d Nd ∧ MptStack d Nd p (p :: fs) ∧
      (∀ q len, KeyIn s Nd q len → KeyIn d Nd q len) ∧
      (∀ n ∈ Nd, memW d n = memW s n) := by
  dsimp only
  let d := mptBranchFrame u p top node idx
  obtain ⟨hp8, hpframe, hpinside, hpwords⟩ := hfresh
  change globN u "scratch_ptr" ≤ p ∧ p + 40 ≤ globN s "scratch_ptr" at hpinside
  change WordsOK u (p, 40) at hpwords
  have hlim : scratchEnd < 2 ^ 64 := by decide
  have hp64 : p + 40 < 2 ^ 64 := by have := hs.2.2.2.2.2.1; omega
  have hfd : FrameOutside s d
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
    apply mptFreeFrame_write idx ⟨by omega, by omega⟩ (by omega)
    apply mptFreeFrame_write 3 ⟨by omega, by omega⟩ (by omega)
    apply mptFreeFrame_write node ⟨by omega, by omega⟩ (by omega)
    exact mptFreeFrame_write top ⟨hpframe, by omega⟩ (by omega) hfr
  have hd : ArenaReady d := ⟨guestInv_congr (s := u) rfl rfl rfl rfl hu.1, hu.2⟩
  obtain ⟨hnd, hkeys, htags⟩ := mptFreeFrame_heap hs hd hbe hg hn hfd
  have hold := mptFreeFrame_stack hs hd hbe hg hn hfd fs oldtop hst
  have hreads := mptBranchFrame_reads u p top node idx hp64
  have hstack : MptStack d Nd p (p :: fs) := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · have hb : 0 < scratchStart := by decide
      have hf := hs.2.2.2.1
      omega
    · refine ⟨⟨hpinside.1, ?_⟩,
        InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.Memory.wordsOK_transfer hu.1 hd.1 hpwords, ?_⟩
      · exact Nat.le_trans hpinside.2 hs.2.2.2.2.2.1
      · dsimp only
        rw [hreads.2.1, hreads.2.2.1, hreads.2.2.2, htags _ hnode]
        exact ⟨hnode, Or.inr ⟨rfl, hkind, hi⟩⟩
    · intro r hr
      exact Nat.le_trans hpinside.2 (mptStack_addresses fs oldtop hst r hr)
    · rw [hreads.1, htop]
      exact hold
  exact ⟨hd, hnd, hstack, hkeys, htags⟩

def mptBranchCont : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "fr2"), .const 0]) (.var .local (ofString "top")))
    (.seq (.store (.op .add [.var .local (ofString "fr2"), .const 8]) (.var .local (ofString "node")))
    (.seq (.store (.op .add [.var .local (ofString "fr2"), .const 16]) (.const 3))
    (.seq (.store (.op .add [.var .local (ofString "fr2"), .const 32]) (.var .local (ofString "idx")))
    (.seq (.assign .local (ofString "top") (.var .local (ofString "fr2")))
    (.seq (.assign .local (ofString "node") (.load .one (.op .add
      [.var .local (ofString "node"), .const 32, .panop .mul [.var .local (ofString "idx"), .const 8]])))
    (.seq (.assign .local (ofString "level") (.op .add [.var .local (ofString "level"), .const 1]))
      (.assign .local (ofString "go") (.const 1))))))))

theorem mptChildAddr_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n i : BitVec 64}
    (hn : s.locals.lookup (ofString "node") = some (.val (.word n)))
    (hi : s.locals.lookup (ofString "idx") = some (.val (.word i))) :
    evalAt s (.op .add [.var .local (ofString "node"), .const 32,
      .panop .mul [.var .local (ofString "idx"), .const 8]]) =
      some (.val (.word (BitVec.ofNat 64 (n.toNat + 32 + 8 * i.toNat)))) := by
  have heq : n + (32 + i * 8) = BitVec.ofNat 64 (n.toNat + 32 + 8 * i.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod, Nat.mul_comm,
      Nat.add_assoc]
  simp [evalAt, evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord,
    wordOpHOL, wordOp, panOpHOL]
  exact heq

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
