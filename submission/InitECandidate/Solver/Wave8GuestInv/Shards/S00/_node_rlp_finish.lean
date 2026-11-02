import InitECandidate.Solver.Wave8GuestInv.Shards.S00.CounterTactics

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

theorem fb__node_rlp_finish
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_node_ref_len : TerminatingFunBoundedOn GuestInv (ofString "node_ref_len") K.«node_ref_len»)
    (h_node_write_ref : TerminatingFunBoundedOn GuestInv (ofString "node_write_ref") K.«node_write_ref»)
    (h_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    (h_rlp_encode_list_header : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.«rlp_encode_list_header»)
    (h_rlp_list_header_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len»)
    (h_rlp_value_encoded_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_value_encoded_len") K.«rlp_value_encoded_len») :
    TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish» := by
  fb_unfold 282 Guest.Software.guestFn__node_rlp_finish
  apply TerminatingProgBoundedOn.weaken'
  · fb_counter_auto
  · fb_arith K.«_node_rlp_finish»


end InitECandidate.Solver.Wave8Leaves.S00
