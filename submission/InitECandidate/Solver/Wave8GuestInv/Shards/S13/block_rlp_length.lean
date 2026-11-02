import InitECandidate.Solver.Wave8GuestInv.Shards.S13.CounterAuto

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S13

attribute [local irreducible] InitECandidate.Solver.PanTerminatingBounded.TerminatingProgBoundedOn
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]

open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup

theorem fb_block_rlp_length
    (h_encode_header : TerminatingFunBoundedOn GuestInv (ofString "encode_header") K.«encode_header»)
    (h_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (h_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release»)
    (h_rlp_bytes_encoded_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_bytes_encoded_len") K.«rlp_bytes_encoded_len»)
    (h_rlp_list_header_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len»)
    (h_withdrawal_rlp_len : TerminatingFunBoundedOn GuestInv (ofString "withdrawal_rlp_len") K.«withdrawal_rlp_len») :
    TerminatingFunBoundedOn GuestInv (ofString "block_rlp_length") K.«block_rlp_length» := by
  apply onFun_le 862 (by rw [guestAst_len]; decide) Guest.Software.guestFn_block_rlp_length _ rfl
  · htab_unfold Guest.Software.guestFn_block_rlp_length
    s13_walk
  · htab_bound K.«block_rlp_length»

example : type_of% (fb_block_rlp_length (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "encode_header") K.«encode_header») →
    (TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark») →
    (TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») →
    (TerminatingFunBoundedOn GuestInv (ofString "rlp_bytes_encoded_len") K.«rlp_bytes_encoded_len») →
    (TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len») →
    (TerminatingFunBoundedOn GuestInv (ofString "withdrawal_rlp_len") K.«withdrawal_rlp_len») →
    TerminatingFunBoundedOn GuestInv (ofString "block_rlp_length") K.«block_rlp_length») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
