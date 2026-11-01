import InitECandidate.Proofs.BootstrapMemory

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
open InitE Flapjack

theorem wordByte_getByte (word : BitVec 64) (offset : Nat) (ho : offset < 8) :
    wordByte word offset = HolByte.getByte (BitVec.ofNat 64 offset) word false := by
  apply BitVec.eq_of_toNat_eq
  simp only [wordByte, HolByte.getByte, HolByte.byteIndex, Bool.false_eq_true, ↓reduceIte,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : offset < 2^64),Nat.mod_eq_of_lt ho]

#print axioms wordByte_getByte

end InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
