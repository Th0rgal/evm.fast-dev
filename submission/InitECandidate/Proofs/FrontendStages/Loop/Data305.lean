import InitECandidate.Proofs.FrontendStages.Loop.Translate289
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody305_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody305_1 : HolLoopProg 64 :=
.mark loopBody305_0

def loopBody305_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody305_3 : HolLoopProg 64 :=
.mark loopBody305_2

def loopBody305_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody305_5 : HolLoopProg 64 :=
.mark loopBody305_4

def loopBody305_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody305_7 : HolLoopProg 64 :=
.mark loopBody305_6

def loopBody305_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 366) [2, 3, 4, 5] none

def loopBody305_9 : HolLoopProg 64 :=
.mark loopBody305_8

def loopBody305_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody305_11 : HolLoopProg 64 :=
.mark loopBody305_10

def loopBody305_12 : HolLoopProg 64 :=
.seq loopBody305_9 loopBody305_11

def loopBody305_13 : HolLoopProg 64 :=
.mark loopBody305_12

def loopBody305_14 : HolLoopProg 64 :=
.seq loopBody305_7 loopBody305_13

def loopBody305_15 : HolLoopProg 64 :=
.mark loopBody305_14

def loopBody305_16 : HolLoopProg 64 :=
.seq loopBody305_5 loopBody305_15

def loopBody305_17 : HolLoopProg 64 :=
.mark loopBody305_16

def loopBody305_18 : HolLoopProg 64 :=
.seq loopBody305_3 loopBody305_17

def loopBody305_19 : HolLoopProg 64 :=
.mark loopBody305_18

def loopBody305_20 : HolLoopProg 64 :=
.seq loopBody305_1 loopBody305_19

def loopBody305_21 : HolLoopProg 64 :=
.mark loopBody305_20

def output305 : Nat × List Nat × HolLoopProg 64 :=
  (369, [0, 1], loopBody305_21)
end InitECandidate.Proofs.FrontendStages.Loop
