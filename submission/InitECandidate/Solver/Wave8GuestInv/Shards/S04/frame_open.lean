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
theorem fb_frame_open
    (h_frame_new : TerminatingFunBoundedOn GuestInv (ofString "frame_new") K.«frame_new»)
    (h_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (h_scratch_alloc : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    : TerminatingFunBoundedOn GuestInv (ofString "frame_open") K.«frame_open» := by
  s04_fb_prove 578 Guest.Software.guestFn_frame_open K.«frame_open»


end InitECandidate.Solver.Wave8Leaves.S04
