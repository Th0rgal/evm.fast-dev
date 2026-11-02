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
theorem fb_depth0_prepare
    (h_frame_state_gas_used : TerminatingFunBoundedOn GuestInv (ofString "frame_state_gas_used") K.«frame_state_gas_used»)
    (h_prepare_dispatch : TerminatingFunBoundedOn GuestInv (ofString "prepare_dispatch") K.«prepare_dispatch»)
    (h_set_delegation : TerminatingFunBoundedOn GuestInv (ofString "set_delegation") K.«set_delegation»)
    : TerminatingFunBoundedOn GuestInv (ofString "depth0_prepare") K.«depth0_prepare» := by
  s04_fb_prove 587 Guest.Software.guestFn_depth0_prepare K.«depth0_prepare»


end InitECandidate.Solver.Wave8Leaves.S04
