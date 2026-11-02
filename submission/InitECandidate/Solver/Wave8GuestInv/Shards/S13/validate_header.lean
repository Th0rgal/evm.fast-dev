import InitECandidate.Solver.Wave8GuestInv.Shards.S13.Base

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

theorem fb_validate_header
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_calculate_base_fee_per_gas : TerminatingFunBoundedOn GuestInv (ofString "calculate_base_fee_per_gas") K.«calculate_base_fee_per_gas»)
    (h_calculate_excess_blob_gas : TerminatingFunBoundedOn GuestInv (ofString "calculate_excess_blob_gas") K.«calculate_excess_blob_gas»)
    (h_header_hash : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»)
    (h_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (h_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release»)
    (h_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_u256_eq : TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») :
    TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header» := by
  apply onFun_le 239 (by rw [guestAst_len]; decide) Guest.Software.guestFn_validate_header _ rfl
  · htab_unfold Guest.Software.guestFn_validate_header
    htab_walk
  · htab_bound K.«validate_header»

example : type_of% (fb_validate_header (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
    (TerminatingFunBoundedOn GuestInv (ofString "calculate_base_fee_per_gas") K.«calculate_base_fee_per_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "calculate_excess_blob_gas") K.«calculate_excess_blob_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash») →
    (TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark») →
    (TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») →
    (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
    (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») →
    TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header») := rfl

#print axioms fb_validate_header

end InitECandidate.Solver.Wave8Leaves.S13
