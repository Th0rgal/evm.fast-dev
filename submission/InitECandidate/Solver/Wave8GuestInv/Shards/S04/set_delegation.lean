import InitECandidate.Solver.Wave8GuestInv.Shards.S04.SignedLoop

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
theorem fb_set_delegation
    (h_account_exists : TerminatingFunBoundedOn GuestInv (ofString "account_exists") K.«account_exists»)
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_charge_state_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas»)
    (h_get_code : TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code»)
    (h_get_pre_state_account : TerminatingFunBoundedOn GuestInv (ofString "get_pre_state_account") K.«get_pre_state_account»)
    (h_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has»)
    (h_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_increment_nonce : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce»)
    (h_is_valid_delegation : TerminatingFunBoundedOn GuestInv (ofString "is_valid_delegation") K.«is_valid_delegation»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_recover_authority : TerminatingFunBoundedOn GuestInv (ofString "recover_authority") K.«recover_authority»)
    (h_set_code : TerminatingFunBoundedOn GuestInv (ofString "set_code") K.«set_code»)
    (h_u256_fits_word : TerminatingFunBoundedOn GuestInv (ofString "u256_fits_word") K.«u256_fits_word»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (h_validate_authorization_checks : TerminatingFunBoundedOn GuestInv (ofString "validate_authorization_checks") K.«validate_authorization_checks»)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address»)
    : TerminatingFunBoundedOn GuestInv (ofString "set_delegation") K.«set_delegation» := by
  s04_fb_prove 575 Guest.Software.guestFn_set_delegation K.«set_delegation»


end InitECandidate.Solver.Wave8Leaves.S04
