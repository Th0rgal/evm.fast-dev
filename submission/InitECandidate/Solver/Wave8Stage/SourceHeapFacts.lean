import InitE.SourceMainFacts
import InitE.SourceSemantics
import InitECandidate.Proofs.HeaderInstallation
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.SourceHeapFacts
open InitE Flapjack Flapjack.Compiler.Backend

/-! Heap allocation and installed-memory facts with only the source name,
shape and parameter facts in their dependency closure. These proofs reuse the
fixed AllocationFacts/SourceMemoryInstallation arguments without importing
the unrelated whole-source `pancakeGoodCodeHOL` computation. -/

private theorem address_toNat (base index : Nat) (h : base + index * 8 < 2 ^ 64) :
    (BitVec.ofNat 64 base + BitVec.ofNat 64 index * StackRemove.bytesInWord 64).toNat =
      base + index * 8 := by
  change (BitVec.ofNat 64 base + BitVec.ofNat 64 index * BitVec.ofNat 64 8).toNat = _
  rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]

theorem ordinaryDomain_below_top (address : BitVec 64) (h : ordinaryDomain address) :
    address.toNat < heapEnd := by
  obtain ⟨i, hi, rfl⟩ := (StackRemove.mem_addresses _ _ _).mp h
  have hbound : sourceBase + i * 8 < 2 ^ 64 := by
    norm_num [stackStart, ramEnd, ramStart, ramSize, stackSize, sourceBase, globalsWords] at hi ⊢
    omega
  rw [address_toNat sourceBase i hbound]
  norm_num [stackStart, ramEnd, ramStart, ramSize, stackSize, sourceBase, globalsWords, heapEnd] at hi ⊢
  omega

theorem source_globals_allocatable (input : Guest.InputBlob) :
    globalsAllocatableHOL (sourceInitialState input) sourceDeclarations := by
  unfold globalsAllocatableHOL
  dsimp only
  rw [sourceGlobalsSize, sourceStructContext]
  change (some ([] : Pancake.PanLang.StructContextExact) ≠ none) ∧
    (∀ a, ¬ (ordinaryDomain a ∧ StackRemove.addresses (BitVec.ofNat 64 heapEnd) 67 a)) ∧
    ¬ ordinaryDomain (BitVec.ofNat 64 heapEnd + StackRemove.bytesInWord 64 * BitVec.ofNat 64 67) ∧
    67 * (StackRemove.bytesInWord 64).toNat < 2 ^ 64
  refine ⟨by simp, ?_, ?_, by decide⟩
  · intro address ⟨ha, hg⟩
    have hlt := ordinaryDomain_below_top address ha
    obtain ⟨i, hi, heq⟩ := (StackRemove.mem_addresses _ _ _).mp hg
    have hb : heapEnd + i * 8 < 2 ^ 64 := by
      norm_num [heapEnd, stackStart, ramEnd, ramStart, ramSize, stackSize, globalsWords] at hi ⊢
      omega
    rw [heq, address_toNat heapEnd i hb] at hlt
    omega
  · intro ha
    have hlt := ordinaryDomain_below_top _ ha
    have hb : heapEnd + 67 * 8 < 2 ^ 64 := by decide
    rw [BitVec.mul_comm, address_toNat heapEnd 67 hb] at hlt
    omega

theorem installedMemory_zero_after_headers (a : BitVec 64)
    (ha : sourceBase+40 ≤ a.toNat) : installedMemory a = 0 := by
  have hs : ¬ (sourceBase ≤ a.toNat ∧ a.toNat < sourceBase+40) := by omega
  have hd : ¬ (initDataRam ≤ a.toNat ∧ a.toNat < initDataRam+24) := by
    simp only [sourceBase,initDataRam] at ha ⊢; omega
  have hb : ¬ (initDataRam+24 ≤ a.toNat ∧ a.toNat < initDataEnd) := by
    simp only [sourceBase,initDataEnd] at ha ⊢; omega
  rw [installedMemory, if_neg hs, if_neg hd, if_neg hb]
  apply initial_ram_zero
  simp only [ramStart,sourceBase] at ha ⊢; omega

private theorem source_index_bound (i : Nat)
    (hi : i < (stackStart-sourceBase)/8-globalsWords) : sourceBase+8*i+8 < 2^64 := by
  norm_num [stackStart,ramEnd,ramStart,ramSize,stackSize,sourceBase,globalsWords] at hi ⊢
  omega

private theorem cell_toNat (i : Nat) (hi : sourceBase+8*i < 2^64) :
    (BitVec.ofNat 64 (sourceBase+8*i)).toNat = sourceBase+8*i := by
  exact Nat.mod_eq_of_lt hi

private theorem sourceMemory_cell (i : Nat)
    (hi : sourceBase+8*i < 2^64) :
    sourceMemory (BitVec.ofNat 64 (sourceBase+8*i)) =
      .word (Guest.startupHeaders[i]?.getD 0) := by
  have hval := cell_toNat i hi
  have hidx : (sourceBase + 8*i - sourceBase) / 8 = i := by omega
  by_cases hsmall : i < 5
  · have hregion : sourceBase ≤ sourceBase + 8*i ∧ sourceBase + 8*i < sourceBase + 40 := by omega
    simp only [sourceMemory, hval, hidx, if_pos hregion]
  · have hregion : ¬ (sourceBase ≤ sourceBase + 8*i ∧ sourceBase + 8*i < sourceBase + 40) := by omega
    have hnone : Guest.startupHeaders[i]? = none := by
      apply List.getElem?_eq_none
      simp [Guest.startupHeaders]
      omega
    simp only [sourceMemory, hval, if_neg hregion, hnone, Option.getD_none]

theorem installed_ordinary_word (a : BitVec 64) (ha : ordinaryDomain a) :
    packedWordMemory installedMemory a = wlabWlocExact (sourceMemory a) := by
  obtain ⟨i,hi,heq⟩ := (StackRemove.mem_addresses _ _ _).mp ha
  have hbound := source_index_bound i hi
  have haddr : a = BitVec.ofNat 64 (sourceBase+8*i) := by
    rw [heq]
    change BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 i * BitVec.ofNat 64 8 = _
    rw [BitVec.ofNat_mul_ofNat,BitVec.ofNat_add_ofNat,Nat.mul_comm]
  rw [haddr,sourceMemory_cell i (by omega)]
  change WordLocW.word (packedMemoryWord installedMemory (BitVec.ofNat 64 (sourceBase+8*i))) =
    WordLocW.word (Guest.startupHeaders[i]?.getD 0)
  apply congrArg WordLocW.word
  by_cases hsmall : i < 5
  · have hlen : i < Guest.startupHeaders.length := hsmall
    rw [List.getElem?_eq_getElem hlen]
    exact baseline_source_headers ⟨i,hsmall⟩
  · have hnone : Guest.startupHeaders[i]? = none := by
      apply List.getElem?_eq_none
      change 5 ≤ i
      omega
    rw [hnone]
    apply packedMemoryWord_of_bytes
    · unfold holByteAligned
      rw [holLOG2_eq_log2 (by decide)]
      apply (holAligned_iff _ _).mpr
      simp [cell_toNat i (by omega),sourceBase,Nat.add_mod,Nat.mul_mod_right]
    · intro j
      rw [installedMemory_zero_after_headers]
      · simp [HolByte.getByte]
      · rw [BitVec.ofNat_add_ofNat,BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have hj := j.isLt; omega : sourceBase+8*i+j.val < 2^64)]
        omega


end InitECandidate.Solver.Wave8Stage.SourceHeapFacts
