import InitECandidate.Proofs.FrontendStages.Loop.Translate290
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody306_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody306_1 : HolLoopProg 64 :=
.mark loopBody306_0

def loopBody306_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody306_3 : HolLoopProg 64 :=
.mark loopBody306_2

def loopBody306_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody306_5 : HolLoopProg 64 :=
.mark loopBody306_4

def loopBody306_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody306_7 : HolLoopProg 64 :=
.mark loopBody306_6

def loopBody306_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 366) [2, 3, 4, 5] none

def loopBody306_9 : HolLoopProg 64 :=
.mark loopBody306_8

def loopBody306_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody306_11 : HolLoopProg 64 :=
.mark loopBody306_10

def loopBody306_12 : HolLoopProg 64 :=
.seq loopBody306_9 loopBody306_11

def loopBody306_13 : HolLoopProg 64 :=
.mark loopBody306_12

def loopBody306_14 : HolLoopProg 64 :=
.seq loopBody306_7 loopBody306_13

def loopBody306_15 : HolLoopProg 64 :=
.mark loopBody306_14

def loopBody306_16 : HolLoopProg 64 :=
.seq loopBody306_5 loopBody306_15

def loopBody306_17 : HolLoopProg 64 :=
.mark loopBody306_16

def loopBody306_18 : HolLoopProg 64 :=
.seq loopBody306_3 loopBody306_17

def loopBody306_19 : HolLoopProg 64 :=
.mark loopBody306_18

def loopBody306_20 : HolLoopProg 64 :=
.seq loopBody306_1 loopBody306_19

def loopBody306_21 : HolLoopProg 64 :=
.mark loopBody306_20

def output306 : Nat × List Nat × HolLoopProg 64 :=
  (370, [0, 1], loopBody306_21)
end InitECandidate.Proofs.FrontendStages.Loop
