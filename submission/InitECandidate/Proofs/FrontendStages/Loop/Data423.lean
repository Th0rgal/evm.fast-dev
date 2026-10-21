import InitECandidate.Proofs.FrontendStages.Loop.Translate407
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody423_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody423_1 : HolLoopProg 64 :=
.mark loopBody423_0

def loopBody423_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody423_3 : HolLoopProg 64 :=
.mark loopBody423_2

def loopBody423_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody423_5 : HolLoopProg 64 :=
.mark loopBody423_4

def loopBody423_6 : HolLoopProg 64 :=
.seq loopBody423_3 loopBody423_5

def loopBody423_7 : HolLoopProg 64 :=
.mark loopBody423_6

def loopBody423_8 : HolLoopProg 64 :=
.seq loopBody423_1 loopBody423_7

def loopBody423_9 : HolLoopProg 64 :=
.mark loopBody423_8

def output423 : Nat × List Nat × HolLoopProg 64 :=
  (487, [], loopBody423_9)
end InitECandidate.Proofs.FrontendStages.Loop
