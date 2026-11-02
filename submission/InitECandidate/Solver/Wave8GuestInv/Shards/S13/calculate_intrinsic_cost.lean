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

theorem fb_calculate_intrinsic_cost
    (h_count_tokens_in_data : TerminatingFunBoundedOn GuestInv (ofString "count_tokens_in_data") K.«count_tokens_in_data»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») :
    TerminatingFunBoundedOn GuestInv (ofString "calculate_intrinsic_cost") K.«calculate_intrinsic_cost» := by
  apply onFun_le 345 (by rw [guestAst_len]; decide) Guest.Software.guestFn_calculate_intrinsic_cost _ rfl
  · htab_unfold Guest.Software.guestFn_calculate_intrinsic_cost
    s13_walk
  · htab_bound K.«calculate_intrinsic_cost»

example : type_of% (fb_calculate_intrinsic_cost (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "count_tokens_in_data") K.«count_tokens_in_data») →
    (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») →
    TerminatingFunBoundedOn GuestInv (ofString "calculate_intrinsic_cost") K.«calculate_intrinsic_cost») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
