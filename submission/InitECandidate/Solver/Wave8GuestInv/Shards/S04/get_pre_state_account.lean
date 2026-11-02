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
theorem fb_get_pre_state_account
    (h_acct_empty : TerminatingFunBoundedOn GuestInv (ofString "acct_empty") K.«acct_empty»)
    (h_get_pre_state_account_optional : TerminatingFunBoundedOn GuestInv (ofString "get_pre_state_account_optional") K.«get_pre_state_account_optional»)
    : TerminatingFunBoundedOn GuestInv (ofString "get_pre_state_account") K.«get_pre_state_account» := by
  s04_fb_prove 373 Guest.Software.guestFn_get_pre_state_account K.«get_pre_state_account»


end InitECandidate.Solver.Wave8Leaves.S04
