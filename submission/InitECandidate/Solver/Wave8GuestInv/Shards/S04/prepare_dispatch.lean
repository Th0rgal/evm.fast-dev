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
theorem fb_prepare_dispatch
    (h_acct_is_empty : TerminatingFunBoundedOn GuestInv (ofString "acct_is_empty") K.«acct_is_empty»)
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_charge_state_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas»)
    (h_compute_jumpdests : TerminatingFunBoundedOn GuestInv (ofString "compute_jumpdests") K.«compute_jumpdests»)
    (h_ext_code_of : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»)
    (h_get_delegated_code_address : TerminatingFunBoundedOn GuestInv (ofString "get_delegated_code_address") K.«get_delegated_code_address»)
    (h_get_pre_state_account : TerminatingFunBoundedOn GuestInv (ofString "get_pre_state_account") K.«get_pre_state_account»)
    (h_is_account_alive : TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.«is_account_alive»)
    (h_is_warm_address : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»)
    (h_warm_address : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address»)
    : TerminatingFunBoundedOn GuestInv (ofString "prepare_dispatch") K.«prepare_dispatch» := by
  s04_fb_prove 576 Guest.Software.guestFn_prepare_dispatch K.«prepare_dispatch»


end InitECandidate.Solver.Wave8Leaves.S04
