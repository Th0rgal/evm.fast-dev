import InitECandidate.Proofs.BootstrapMemory

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
open InitE Flapjack

/-- Project one image byte before specializing to the large concrete ROM. -/
theorem byte_of_image (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (start offset : Nat) (bound : offset < 8 * words.length)
    (image : (bytes.drop start).take (8 * words.length) =
      (List.range (8 * words.length)).map (fun k =>
        wordByte (words[k / 8]?.getD 0) (k % 8))) :
    bytes[start + offset]?.getD 0 =
      wordByte (words[offset / 8]?.getD 0) (offset % 8) := by
  have h := congrArg (fun image : List (BitVec 8) => image[offset]?.getD 0) image
  simpa [List.getElem?_take, bound, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range, Nat.add_comm] using h

#print axioms byte_of_image


end InitECandidate.Solver.Wave8GuestInv.ArtifactInstallation
