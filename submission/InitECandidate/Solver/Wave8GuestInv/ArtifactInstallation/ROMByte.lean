import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.CopyByte
import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.ROMRead
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
open InitE Flapjack

theorem installed_memory_bitmap_rom_byte (index byte : Nat)
    (hi : index < 4603) (hj : byte < 8) :
    installedMemory (BitVec.ofNat 64 (initDataRam+24+8*index) + BitVec.ofNat 64 byte) =
      InitECandidate.code[initDataRom-initialPc+24+(8*index+byte)]?.getD 0 := by
  rw [installed_memory_bitmap_copy index byte hi hj]
  rw [initial_memory_byte (initDataRom+24+8*index+byte)
    (by simp only [initialPc,initDataRom]; omega)
    (by simp only [initialPc,initDataRom]; omega)
    (by simp only [initDataRom]; omega)]
  have hoff : initDataRom+24+8*index+byte-initialPc =
      initDataRom-initialPc+24+(8*index+byte) := by
    simp only [initDataRom,initialPc]; omega
  rw [hoff]

#print axioms installed_memory_bitmap_rom_byte

end InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
