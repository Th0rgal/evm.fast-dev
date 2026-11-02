import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb_node_ref_len
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») :
    TerminatingFunBoundedOn GuestInv (ofString "node_ref_len") K.«node_ref_len» := by
  fb_prove 287 Guest.Software.guestFn_node_ref_len K.«node_ref_len»


end InitECandidate.Solver.Wave8Leaves.S00
