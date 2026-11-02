import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S00Spec

private theorem node_rlp_begin_bounds (a b c d : Nat)
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") a)
    (h_nibble_list_to_compact : TerminatingFunBoundedOn GuestInv (ofString "nibble_list_to_compact") b)
    (h_rlp_bytes_encoded_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_bytes_encoded_len") c)
    (h_rlp_value_encoded_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_value_encoded_len") d) :
    TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") (Nat.max ((a + 1) + (b + 1) + (c + 1) + Nat.max (d + 1) 0) 0) := by
  fb_unfold 281 Guest.Software.guestFn__node_rlp_begin
  refine TerminatingProgBoundedOn.weaken' (by fb_auto) ?_
  simp only [nat_max_eq]
  omega

theorem fb__node_rlp_begin
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_nibble_list_to_compact : TerminatingFunBoundedOn GuestInv (ofString "nibble_list_to_compact") K.«nibble_list_to_compact»)
    (h_rlp_bytes_encoded_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_bytes_encoded_len") K.«rlp_bytes_encoded_len»)
    (h_rlp_value_encoded_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_value_encoded_len") K.«rlp_value_encoded_len») :
    TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin» := by
  exact node_rlp_begin_bounds _ _ _ _ h_alloc h_nibble_list_to_compact
    h_rlp_bytes_encoded_len h_rlp_value_encoded_len


end InitECandidate.Solver.Wave8Leaves.S00
