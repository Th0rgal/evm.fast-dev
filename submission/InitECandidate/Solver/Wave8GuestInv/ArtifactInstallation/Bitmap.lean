import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.InstalledByte

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
open InitE Flapjack

theorem installed_bitmap_word (i : Fin InitECandidate.bitmaps.length) :
    packedMemoryWord installedMemory (BitVec.ofNat 64 (initDataRam+24+8*i.val)) =
      InitECandidate.bitmaps[i] := by
  apply packedMemoryWord_of_bytes
  · unfold holByteAligned
    rw [holLOG2_eq_log2 (by decide)]
    change holAligned 3 (BitVec.ofNat 64 (initDataRam+24+8*i.val)) = true
    apply (holAligned_iff _ _).mpr
    change (BitVec.ofNat 64 (initDataRam+24+8*i.val)).toNat % 8 = 0
    have hi : i.val < 4603 := by simpa only [bitmap_count] using i.isLt
    simp only [BitVec.toNat_ofNat]
    have hbase : initDataRam+24+8*i.val < 2^64 := by
      simp only [initDataRam]; omega
    rw [Nat.mod_eq_of_lt hbase]
    simp [initDataRam,Nat.add_mod,Nat.mul_mod_right]
  · exact installed_bitmap_byte i


end InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
