import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb__delete_ext_finish
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (h_nibbles_concat : TerminatingFunBoundedOn GuestInv (ofString "nibbles_concat") K.«nibbles_concat»)
    (h_node_new_ext : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext»)
    (h_node_new_leaf : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf») :
    TerminatingFunBoundedOn GuestInv (ofString "_delete_ext_finish") K.«_delete_ext_finish» := by
  fb_prove 277 Guest.Software.guestFn__delete_ext_finish K.«_delete_ext_finish»


end InitECandidate.Solver.Wave8Leaves.S00
