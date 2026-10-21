import InitECandidate.Proofs.FrontendStages.Loop.Translate653
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody669_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody669_1 : HolLoopProg 64 :=
.mark loopBody669_0

def loopBody669_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody669_3 : HolLoopProg 64 :=
.mark loopBody669_2

def loopBody669_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody669_5 : HolLoopProg 64 :=
.mark loopBody669_4

def loopBody669_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 730) [2, 3, 4] none

def loopBody669_7 : HolLoopProg 64 :=
.mark loopBody669_6

def loopBody669_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody669_9 : HolLoopProg 64 :=
.mark loopBody669_8

def loopBody669_10 : HolLoopProg 64 :=
.seq loopBody669_7 loopBody669_9

def loopBody669_11 : HolLoopProg 64 :=
.mark loopBody669_10

def loopBody669_12 : HolLoopProg 64 :=
.seq loopBody669_5 loopBody669_11

def loopBody669_13 : HolLoopProg 64 :=
.mark loopBody669_12

def loopBody669_14 : HolLoopProg 64 :=
.seq loopBody669_3 loopBody669_13

def loopBody669_15 : HolLoopProg 64 :=
.mark loopBody669_14

def loopBody669_16 : HolLoopProg 64 :=
.seq loopBody669_1 loopBody669_15

def loopBody669_17 : HolLoopProg 64 :=
.mark loopBody669_16

def output669 : Nat × List Nat × HolLoopProg 64 :=
  (733, [0, 1], loopBody669_17)
end InitECandidate.Proofs.FrontendStages.Loop
