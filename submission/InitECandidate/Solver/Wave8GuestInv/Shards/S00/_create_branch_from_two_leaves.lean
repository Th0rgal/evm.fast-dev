import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb__create_branch_from_two_leaves
    (h_node_new_branch : TerminatingFunBoundedOn GuestInv (ofString "node_new_branch") K.«node_new_branch»)
    (h_node_new_leaf : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf») :
    TerminatingFunBoundedOn GuestInv (ofString "_create_branch_from_two_leaves") K.«_create_branch_from_two_leaves» := by
  fb_prove 272 Guest.Software.guestFn__create_branch_from_two_leaves K.«_create_branch_from_two_leaves»


end InitECandidate.Solver.Wave8Leaves.S00
