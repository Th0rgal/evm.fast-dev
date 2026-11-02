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
theorem fb_precompile_index
    (h_is_zero_bytes : TerminatingFunBoundedOn GuestInv (ofString "is_zero_bytes") K.«is_zero_bytes»)
    : TerminatingFunBoundedOn GuestInv (ofString "precompile_index") K.«precompile_index» := by
  s04_fb_prove 822 Guest.Software.guestFn_precompile_index K.«precompile_index»


end InitECandidate.Solver.Wave8Leaves.S04
