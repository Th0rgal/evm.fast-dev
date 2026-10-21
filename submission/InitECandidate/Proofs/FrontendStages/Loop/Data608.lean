import InitECandidate.Proofs.FrontendStages.Loop.Translate592
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody608_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody608_1 : HolLoopProg 64 :=
.mark loopBody608_0

def loopBody608_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 0) (Flapjack.HolLoopExp.const 5#64))

def loopBody608_3 : HolLoopProg 64 :=
.mark loopBody608_2

def loopBody608_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 80) [2, 3] none

def loopBody608_5 : HolLoopProg 64 :=
.mark loopBody608_4

def loopBody608_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody608_7 : HolLoopProg 64 :=
.mark loopBody608_6

def loopBody608_8 : HolLoopProg 64 :=
.seq loopBody608_5 loopBody608_7

def loopBody608_9 : HolLoopProg 64 :=
.mark loopBody608_8

def loopBody608_10 : HolLoopProg 64 :=
.seq loopBody608_3 loopBody608_9

def loopBody608_11 : HolLoopProg 64 :=
.mark loopBody608_10

def loopBody608_12 : HolLoopProg 64 :=
.seq loopBody608_1 loopBody608_11

def loopBody608_13 : HolLoopProg 64 :=
.mark loopBody608_12

def output608 : Nat × List Nat × HolLoopProg 64 :=
  (672, [0, 1], loopBody608_13)
end InitECandidate.Proofs.FrontendStages.Loop
