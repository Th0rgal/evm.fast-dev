import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_node_new_hashed
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») :
    TerminatingFunBoundedOn GuestInv (ofString "node_new_hashed") K.«node_new_hashed» := by
  fb_prove 255 Guest.Software.guestFn_node_new_hashed K.«node_new_hashed»


end InitECandidate.Solver.Wave8Leaves.S00
