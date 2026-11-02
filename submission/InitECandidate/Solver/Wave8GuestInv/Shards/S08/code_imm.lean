import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_code_imm :
    TerminatingFunBoundedOn GuestInv (ofString "code_imm") K.«code_imm» := by
  fb_prove 518 Guest.Software.guestFn_code_imm K.«code_imm»

example : type_of% Wave8GuestInv.«fb_code_imm» := fb_code_imm

end InitECandidate.Solver.Wave8Leaves.S08
