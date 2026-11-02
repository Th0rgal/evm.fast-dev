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
theorem fb_move_ether
    (h_acct_copy : TerminatingFunBoundedOn GuestInv (ofString "acct_copy") K.«acct_copy»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_modify_state_commit : TerminatingFunBoundedOn GuestInv (ofString "modify_state_commit") K.«modify_state_commit»)
    (h_u256_add : TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add»)
    (h_u256_lt : TerminatingFunBoundedOn GuestInv (ofString "u256_lt") K.«u256_lt»)
    (h_u256_sub : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub»)
    : TerminatingFunBoundedOn GuestInv (ofString "move_ether") K.«move_ether» := by
  s04_fb_prove 395 Guest.Software.guestFn_move_ether K.«move_ether»


end InitECandidate.Solver.Wave8Leaves.S04
