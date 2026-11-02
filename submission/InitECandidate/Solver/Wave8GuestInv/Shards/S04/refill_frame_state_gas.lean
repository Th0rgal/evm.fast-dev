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
theorem fb_refill_frame_state_gas
    : TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.«refill_frame_state_gas» := by
  s04_fb_prove 452 Guest.Software.guestFn_refill_frame_state_gas K.«refill_frame_state_gas»


end InitECandidate.Solver.Wave8Leaves.S04
