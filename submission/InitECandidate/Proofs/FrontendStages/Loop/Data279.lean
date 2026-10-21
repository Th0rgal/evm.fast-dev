import InitECandidate.Proofs.FrontendStages.Loop.Translate263
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody279_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 144#64]))

def loopBody279_1 : HolLoopProg 64 :=
.mark loopBody279_0

def loopBody279_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody279_3 : HolLoopProg 64 :=
.mark loopBody279_2

def loopBody279_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody279_5 : HolLoopProg 64 :=
.mark loopBody279_4

def loopBody279_6 : HolLoopProg 64 :=
.seq loopBody279_3 loopBody279_5

def loopBody279_7 : HolLoopProg 64 :=
.mark loopBody279_6

def loopBody279_8 : HolLoopProg 64 :=
.seq loopBody279_1 loopBody279_7

def loopBody279_9 : HolLoopProg 64 :=
.mark loopBody279_8

def output279 : Nat × List Nat × HolLoopProg 64 :=
  (343, [0], loopBody279_9)
end InitECandidate.Proofs.FrontendStages.Loop
