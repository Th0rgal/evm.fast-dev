import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb__split_extension
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (h_node_new_branch : TerminatingFunBoundedOn GuestInv (ofString "node_new_branch") K.«node_new_branch»)
    (h_node_new_ext : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext»)
    (h_node_new_leaf : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf») :
    TerminatingFunBoundedOn GuestInv (ofString "_split_extension") K.«_split_extension» := by
  fb_prove 274 Guest.Software.guestFn__split_extension K.«_split_extension»


end InitECandidate.Solver.Wave8Leaves.S00
