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
theorem fb_get_delegated_code_address
    (h_is_valid_delegation : TerminatingFunBoundedOn GuestInv (ofString "is_valid_delegation") K.«is_valid_delegation»)
    : TerminatingFunBoundedOn GuestInv (ofString "get_delegated_code_address") K.«get_delegated_code_address» := by
  s04_fb_prove 571 Guest.Software.guestFn_get_delegated_code_address K.«get_delegated_code_address»


end InitECandidate.Solver.Wave8Leaves.S04
