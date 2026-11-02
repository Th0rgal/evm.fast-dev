import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_require_not_static :
    TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static» := by
  fb_prove 470 Guest.Software.guestFn_require_not_static K.«require_not_static»

example : type_of% Wave8GuestInv.«fb_require_not_static» := fb_require_not_static

end InitECandidate.Solver.Wave8Leaves.S08
