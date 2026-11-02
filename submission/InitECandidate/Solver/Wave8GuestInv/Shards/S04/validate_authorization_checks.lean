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
theorem fb_validate_authorization_checks
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_get_code : TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code»)
    (h_is_valid_delegation : TerminatingFunBoundedOn GuestInv (ofString "is_valid_delegation") K.«is_valid_delegation»)
    : TerminatingFunBoundedOn GuestInv (ofString "validate_authorization_checks") K.«validate_authorization_checks» := by
  s04_fb_prove 574 Guest.Software.guestFn_validate_authorization_checks K.«validate_authorization_checks»


end InitECandidate.Solver.Wave8Leaves.S04
