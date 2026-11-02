import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_decode_single :
    TerminatingFunBoundedOn GuestInv (ofString "decode_single") K.«decode_single» := by
  fb_prove 519 Guest.Software.guestFn_decode_single K.«decode_single»

example : type_of% Wave8GuestInv.«fb_decode_single» := fb_decode_single

end InitECandidate.Solver.Wave8Leaves.S08
