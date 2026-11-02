import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_node_new_ext
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») :
    TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext» := by
  fb_prove 257 Guest.Software.guestFn_node_new_ext K.«node_new_ext»


end InitECandidate.Solver.Wave8Leaves.S00
