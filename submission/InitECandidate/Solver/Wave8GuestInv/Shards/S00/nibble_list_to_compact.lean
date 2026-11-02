import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Loops

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_nibble_list_to_compact :
    TerminatingFunBoundedOn GuestInv (ofString "nibble_list_to_compact") K.«nibble_list_to_compact» := by
  fb_unfold 250 Guest.Software.guestFn_nibble_list_to_compact
  apply TerminatingProgBoundedOn.weaken'
  · s00_auto
  · fb_arith K.«nibble_list_to_compact»


end InitECandidate.Solver.Wave8Leaves.S00
