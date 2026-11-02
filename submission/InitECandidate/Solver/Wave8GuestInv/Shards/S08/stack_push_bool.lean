import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_stack_push_bool
    (h_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») :
    TerminatingFunBoundedOn GuestInv (ofString "stack_push_bool") K.«stack_push_bool» := by
  fb_prove 456 Guest.Software.guestFn_stack_push_bool K.«stack_push_bool»

example :
    type_of% Wave8GuestInv.«fb_stack_push» →
    type_of% Wave8GuestInv.«fb_stack_push_bool» :=
  fb_stack_push_bool

end InitECandidate.Solver.Wave8Leaves.S08
