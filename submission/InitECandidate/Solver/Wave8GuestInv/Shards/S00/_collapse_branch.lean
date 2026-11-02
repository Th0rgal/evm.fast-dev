import InitECandidate.Solver.Wave8GuestInv.Shards.S00.CounterTactics

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb__collapse_branch
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (h_nibbles_concat : TerminatingFunBoundedOn GuestInv (ofString "nibbles_concat") K.«nibbles_concat»)
    (h_node_new_ext : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext»)
    (h_node_new_leaf : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf») :
    TerminatingFunBoundedOn GuestInv (ofString "_collapse_branch") K.«_collapse_branch» := by
  fb_unfold 276 Guest.Software.guestFn__collapse_branch
  apply TerminatingProgBoundedOn.weaken'
  · fb_counter_auto
  · fb_arith K.«_collapse_branch»


end InitECandidate.Solver.Wave8Leaves.S00
