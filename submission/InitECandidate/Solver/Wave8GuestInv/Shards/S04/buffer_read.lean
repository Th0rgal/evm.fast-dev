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
theorem fb_buffer_read
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    : TerminatingFunBoundedOn GuestInv (ofString "buffer_read") K.«buffer_read» := by
  s04_fb_prove 462 Guest.Software.guestFn_buffer_read K.«buffer_read»


end InitECandidate.Solver.Wave8Leaves.S04
