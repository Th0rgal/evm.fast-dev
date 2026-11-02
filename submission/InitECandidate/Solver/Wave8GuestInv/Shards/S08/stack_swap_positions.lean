import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_stack_swap_positions :
    TerminatingFunBoundedOn GuestInv (ofString "stack_swap_positions") K.«stack_swap_positions» := by
  fb_prove 516 Guest.Software.guestFn_stack_swap_positions K.«stack_swap_positions»

example : type_of% Wave8GuestInv.«fb_stack_swap_positions» := fb_stack_swap_positions

end InitECandidate.Solver.Wave8Leaves.S08
