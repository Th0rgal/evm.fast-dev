import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb__insert_into_leaf
    (h__create_branch_from_two_leaves : TerminatingFunBoundedOn GuestInv (ofString "_create_branch_from_two_leaves") K.«_create_branch_from_two_leaves»)
    (h_common_prefix_length : TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_node_new_ext : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext») :
    TerminatingFunBoundedOn GuestInv (ofString "_insert_into_leaf") K.«_insert_into_leaf» := by
  fb_prove 273 Guest.Software.guestFn__insert_into_leaf K.«_insert_into_leaf»


end InitECandidate.Solver.Wave8Leaves.S00
