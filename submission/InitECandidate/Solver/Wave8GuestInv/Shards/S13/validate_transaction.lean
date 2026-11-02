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

theorem fb_validate_transaction
    (h_calculate_intrinsic_cost : TerminatingFunBoundedOn GuestInv (ofString "calculate_intrinsic_cost") K.«calculate_intrinsic_cost»)
    (h_u256_fits_word : TerminatingFunBoundedOn GuestInv (ofString "u256_fits_word") K.«u256_fits_word») :
    TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction» := by
  apply onFun_le 346 (by rw [guestAst_len]; decide) Guest.Software.guestFn_validate_transaction _ rfl
  · htab_unfold Guest.Software.guestFn_validate_transaction
    htab_walk
  · htab_bound K.«validate_transaction»

example : type_of% (fb_validate_transaction (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "calculate_intrinsic_cost") K.«calculate_intrinsic_cost») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_fits_word") K.«u256_fits_word») →
    TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction») := rfl

#print axioms fb_validate_transaction

end InitECandidate.Solver.Wave8Leaves.S13
