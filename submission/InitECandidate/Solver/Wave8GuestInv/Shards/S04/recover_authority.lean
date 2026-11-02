import InitECandidate.Solver.Wave8GuestInv.Shards.S04.Base

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S04

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8Leaves.S04.Light
open InitECandidate.Solver.Wave8Leaves.S04.Base

-- Conditional leaf: final spec compatibility and axioms are checked in Axioms.lean.
theorem fb_recover_authority
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (h_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release»)
    (h_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_rlp_encode_bytes : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    (h_rlp_encode_list_header : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.«rlp_encode_list_header»)
    (h_rlp_encode_word : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word»)
    (h_rlp_list_header_len : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len»)
    (h_rlp_put_u256 : TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.«rlp_put_u256»)
    (h_secp256k1_recover : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_recover") K.«secp256k1_recover»)
    (h_u256_gt : TerminatingFunBoundedOn GuestInv (ofString "u256_gt") K.«u256_gt»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (h_u256_lt : TerminatingFunBoundedOn GuestInv (ofString "u256_lt") K.«u256_lt»)
    : TerminatingFunBoundedOn GuestInv (ofString "recover_authority") K.«recover_authority» := by
  s04_fb_prove 572 Guest.Software.guestFn_recover_authority K.«recover_authority»


end InitECandidate.Solver.Wave8Leaves.S04
