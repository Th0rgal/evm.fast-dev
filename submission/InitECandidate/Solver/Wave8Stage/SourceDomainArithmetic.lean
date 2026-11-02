import InitECandidate.Solver.Wave8Stage.SourceHeapFacts

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.SourceDomainArithmetic
open InitE Flapjack Flapjack.Compiler.Backend

/-- Arithmetic membership test for the fixed source heap, without an
existential search over the address set. -/
theorem ordinary_iff (a : BitVec 64) :
    ordinaryDomain a ↔ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd ∧ a.toNat % 8 = 0 := by
  constructor
  · intro ha
    have upper := SourceHeapFacts.ordinaryDomain_below_top a ha
    obtain ⟨i, hi, rfl⟩ := (StackRemove.mem_addresses _ _ _).mp ha
    have small : sourceBase + i * 8 < 2^64 := by
      norm_num [stackStart, ramEnd, ramStart, ramSize, stackSize, sourceBase, globalsWords] at hi ⊢
      omega
    have addr : (BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 i *
        StackRemove.bytesInWord 64).toNat = sourceBase + i*8 := by
      change (BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 i * BitVec.ofNat 64 8).toNat = _
      rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt small]
    rw [addr] at upper ⊢
    refine ⟨by omega, ?_, ?_⟩
    · exact upper
    · norm_num [sourceBase, Nat.add_mod]
  · rintro ⟨lower, upper, aligned⟩
    apply (StackRemove.mem_addresses _ _ _).mpr
    refine ⟨(a.toNat-sourceBase)/8, ?_, ?_⟩
    · norm_num [heapEnd, stackStart, ramEnd, ramStart, ramSize, stackSize,
        sourceBase, globalsWords] at lower upper ⊢
      omega
    · apply BitVec.eq_of_toNat_eq
      change a.toNat = (BitVec.ofNat 64 sourceBase +
        BitVec.ofNat 64 ((a.toNat-sourceBase)/8) * BitVec.ofNat 64 8).toNat
      rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
      have baseAligned : sourceBase % 8 = 0 := by decide
      have small := a.isLt
      omega

/-- The source shared domain also has a direct arithmetic membership test. -/
theorem shared_iff (a : BitVec 64) :
    sharedDomain a ↔ a.toNat % 8 = 0 ∧
      ((inputStart ≤ a.toNat ∧ a.toNat < inputEnd) ∨
        (outputStart ≤ a.toNat ∧ a.toNat < outputEnd)) := by
  unfold sharedDomain
  have aligned : holByteAligned a = true ↔ a.toNat % 8 = 0 := by
    unfold holByteAligned
    rw [holLOG2_eq_log2 (by decide)]
    exact holAligned_iff _ _
  rw [aligned]

#print axioms ordinary_iff
#print axioms shared_iff
end InitECandidate.Solver.Wave8Stage.SourceDomainArithmetic
