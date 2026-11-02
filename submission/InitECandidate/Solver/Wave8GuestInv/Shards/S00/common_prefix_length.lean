import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Loops

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_common_prefix_length
    (h_min : TerminatingFunBoundedOn GuestInv (ofString "min") K.«min») :
    TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length» := by
  fb_unfold 251 Guest.Software.guestFn_common_prefix_length
  apply TerminatingProgBoundedOn.weaken'
  · s00_auto
  · fb_arith K.«common_prefix_length»


end InitECandidate.Solver.Wave8Leaves.S00
