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

theorem fb_calculate_base_fee_per_gas
    (h_check_gas_limit : TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit»)
    (h_u256_add : TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add»)
    (h_u256_div : TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.«u256_div»)
    (h_u256_from_word : TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (h_u256_mul : TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul»)
    (h_u256_sub : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub») :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_base_fee_per_gas") K.«calculate_base_fee_per_gas» := by
  apply onFun_le 236 (by rw [guestAst_len]; decide) Guest.Software.guestFn_calculate_base_fee_per_gas _ rfl
  · htab_unfold Guest.Software.guestFn_calculate_base_fee_per_gas
    htab_walk
  · htab_bound K.«calculate_base_fee_per_gas»

example : type_of% (fb_calculate_base_fee_per_gas (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.«u256_div») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub») →
    TerminatingFunBoundedOn GuestInv (ofString "calculate_base_fee_per_gas") K.«calculate_base_fee_per_gas») := rfl

#print axioms fb_calculate_base_fee_per_gas

end InitECandidate.Solver.Wave8Leaves.S13
