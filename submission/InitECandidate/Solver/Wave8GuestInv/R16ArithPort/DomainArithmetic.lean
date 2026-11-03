import InitECandidate.Solver.Wave8GuestInv.Expressions

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 800000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitE Flapjack.Compiler.Backend

/-- Ordinary-domain cells lie in the fixed, non-wrapping source interval. -/
theorem ordinaryDomain_interval (a : BitVec 64) (h : ordinaryDomain a) :
    sourceBase ≤ a.toNat ∧ a.toNat + 8 ≤ heapEnd := by
  unfold ordinaryDomain at h
  rw [StackRemove.mem_addresses] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp only [StackRemove.bytesInWord, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  norm_num [sourceBase, heapEnd, stackStart, ramEnd, ramStart, ramSize, stackSize, globalsWords] at hi ⊢
  omega

theorem byteAlign_toNat (a : BitVec 64) :
    (panByteAlignHOL a).toNat = a.toNat / 8 * 8 := by
  have ha := a.isLt
  change (a.toNat / 8 * 8) % 2 ^ 64 = a.toNat / 8 * 8
  omega

theorem ordinaryDomain_byte_interval (a : BitVec 64) (h : ordinaryDomain (panByteAlignHOL a)) :
    sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
  have hi := ordinaryDomain_interval _ h
  rw [byteAlign_toNat] at hi
  norm_num [sourceBase] at hi ⊢
  omega

/-- Remaining byte distance, with zero assigned to addresses outside the source interval. -/
def domainRank (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd then heapEnd - a.toNat else 0

theorem domainRank_bound (a : BitVec 64) : domainRank a ≤ domainBytes + 1 := by
  unfold domainRank domainBytes
  split_ifs <;> omega

theorem domainRank_add_lt (a : BitVec 64) (step : Nat)
    (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd)
    (hstep : 0 < step) (hsmall : step ≤ 256) :
    domainRank (a + BitVec.ofNat 64 step) < domainRank a := by
  have hend : heapEnd + 256 < 2 ^ 64 := by decide
  have hadd : (a + BitVec.ofNat 64 step).toNat = a.toNat + step := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold domainRank
  rw [if_pos ha, hadd]
  split_ifs <;> omega
end InitECandidate.Solver.Wave8GuestInv.Arith
