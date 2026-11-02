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

theorem fb_calculate_excess_blob_gas
    (h_calculate_blob_gas_price : TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price»)
    (h_u256_from_word : TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word»)
    (h_u256_gt : TerminatingFunBoundedOn GuestInv (ofString "u256_gt") K.«u256_gt»)
    (h_u256_mul : TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul»)
    (h_udiv : TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv») :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_excess_blob_gas") K.«calculate_excess_blob_gas» := by
  apply onFun_le 234 (by rw [guestAst_len]; decide) Guest.Software.guestFn_calculate_excess_blob_gas _ rfl
  · htab_unfold Guest.Software.guestFn_calculate_excess_blob_gas
    htab_walk
  · htab_bound K.«calculate_excess_blob_gas»

example : type_of% (fb_calculate_excess_blob_gas (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_gt") K.«u256_gt») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul») →
    (TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv») →
    TerminatingFunBoundedOn GuestInv (ofString "calculate_excess_blob_gas") K.«calculate_excess_blob_gas») := rfl

#print axioms fb_calculate_excess_blob_gas

end InitECandidate.Solver.Wave8Leaves.S13
