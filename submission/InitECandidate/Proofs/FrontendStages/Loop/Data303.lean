import InitECandidate.Proofs.FrontendStages.Loop.Translate287
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody303_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody303_1 : HolLoopProg 64 :=
.mark loopBody303_0

def loopBody303_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody303_3 : HolLoopProg 64 :=
.mark loopBody303_2

def loopBody303_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody303_5 : HolLoopProg 64 :=
.mark loopBody303_4

def loopBody303_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody303_7 : HolLoopProg 64 :=
.mark loopBody303_6

def loopBody303_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 366) [2, 3, 4, 5] none

def loopBody303_9 : HolLoopProg 64 :=
.mark loopBody303_8

def loopBody303_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody303_11 : HolLoopProg 64 :=
.mark loopBody303_10

def loopBody303_12 : HolLoopProg 64 :=
.seq loopBody303_9 loopBody303_11

def loopBody303_13 : HolLoopProg 64 :=
.mark loopBody303_12

def loopBody303_14 : HolLoopProg 64 :=
.seq loopBody303_7 loopBody303_13

def loopBody303_15 : HolLoopProg 64 :=
.mark loopBody303_14

def loopBody303_16 : HolLoopProg 64 :=
.seq loopBody303_5 loopBody303_15

def loopBody303_17 : HolLoopProg 64 :=
.mark loopBody303_16

def loopBody303_18 : HolLoopProg 64 :=
.seq loopBody303_3 loopBody303_17

def loopBody303_19 : HolLoopProg 64 :=
.mark loopBody303_18

def loopBody303_20 : HolLoopProg 64 :=
.seq loopBody303_1 loopBody303_19

def loopBody303_21 : HolLoopProg 64 :=
.mark loopBody303_20

def output303 : Nat × List Nat × HolLoopProg 64 :=
  (367, [0, 1], loopBody303_21)
end InitECandidate.Proofs.FrontendStages.Loop
