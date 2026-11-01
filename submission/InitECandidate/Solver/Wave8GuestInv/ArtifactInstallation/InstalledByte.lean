import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.ImageByte
import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.WordByte
import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.ROMByte
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
open InitE Flapjack

theorem installed_bitmap_byte (i : Fin InitECandidate.bitmaps.length) (j : Fin 8) :
    installedMemory (BitVec.ofNat 64 (initDataRam+24+8*i.val) + BitVec.ofNat 64 j.val) =
      HolByte.getByte (BitVec.ofNat 64 j.val) InitECandidate.bitmaps[i] false := by
  have hi : i.val < 4603 := by simpa only [bitmap_count] using i.isLt
  have hj := j.isLt
  have bound : 8*i.val+j.val < 8*InitECandidate.bitmaps.length := by
    have small := i.isLt
    omega
  have hdiv : (8*i.val+j.val)/8 = i.val := by omega
  have hmod : (8*i.val+j.val)%8 = j.val := by omega
  calc
    _ = InitECandidate.code[initDataRom-initialPc+24+(8*i.val+j.val)]?.getD 0 :=
      installed_memory_bitmap_rom_byte i.val j.val hi j.isLt
    _ = wordByte (InitECandidate.bitmaps[(8*i.val+j.val)/8]?.getD 0)
        ((8*i.val+j.val)%8) := bitmap_image_byte ⟨_,bound⟩
    _ = wordByte InitECandidate.bitmaps[i] j.val := by
      rw [hdiv,hmod,List.getElem?_eq_getElem i.isLt]
      rfl
    _ = _ := wordByte_getByte _ _ j.isLt

#print axioms installed_bitmap_byte
end InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
