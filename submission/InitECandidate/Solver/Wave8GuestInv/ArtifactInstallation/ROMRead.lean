import InitECandidate.Proofs.BootstrapMemory
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
open InitE Flapjack

theorem read_rom_byte (bytes : List (BitVec 8)) (pc address : Nat)
    (lower : pc ≤ address) (upper : address < pc + bytes.length)
    (limit : address < 2^64) :
    (if pc ≤ (BitVec.ofNat 64 address).toNat ∧
        (BitVec.ofNat 64 address).toNat < pc + bytes.length then
      bytes[(BitVec.ofNat 64 address).toNat - pc]?.getD 0 else 0) =
      bytes[address-pc]?.getD 0 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt limit, if_pos ⟨lower,upper⟩]

#print axioms read_rom_byte

theorem initial_memory_byte (address : Nat)
    (lower : initialPc ≤ address) (upper : address < initialPc + 1028080)
    (limit : address < 2^64) :
    initialMemory (BitVec.ofNat 64 address) =
      InitECandidate.code[address-initialPc]?.getD 0 := by
  exact read_rom_byte InitECandidate.code initialPc address lower
    (by rw [InitECandidate.Proofs.LiteralFacts.code_length]; exact upper) limit

#print axioms initial_memory_byte

end InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
