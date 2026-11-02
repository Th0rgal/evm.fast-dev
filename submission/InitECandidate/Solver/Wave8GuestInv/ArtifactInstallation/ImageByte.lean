import InitECandidate.Proofs.BitmapImageFacts
import InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation.ByteImage

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
open InitE Flapjack

theorem bitmap_image_byte (offset : Fin (8*InitECandidate.bitmaps.length)) :
    InitECandidate.code[initDataRom-initialPc+24+offset.val]?.getD 0 =
      wordByte (InitECandidate.bitmaps[offset.val/8]?.getD 0) (offset.val%8) := by
  exact byte_of_image InitECandidate.code InitECandidate.bitmaps
    (initDataRom-initialPc+24) offset.val offset.isLt bitmap_image_bytes



end InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
