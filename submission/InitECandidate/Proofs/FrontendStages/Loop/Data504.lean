import InitECandidate.Proofs.FrontendStages.Loop.Translate488
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody504_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 0#64]))

def loopBody504_1 : HolLoopProg 64 :=
.mark loopBody504_0

def loopBody504_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody504_3 : HolLoopProg 64 :=
.mark loopBody504_2

def loopBody504_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody504_5 : HolLoopProg 64 :=
.mark loopBody504_4

def loopBody504_6 : HolLoopProg 64 :=
.seq loopBody504_3 loopBody504_5

def loopBody504_7 : HolLoopProg 64 :=
.mark loopBody504_6

def loopBody504_8 : HolLoopProg 64 :=
.seq loopBody504_1 loopBody504_7

def loopBody504_9 : HolLoopProg 64 :=
.mark loopBody504_8

def output504 : Nat × List Nat × HolLoopProg 64 :=
  (568, [], loopBody504_9)
end InitECandidate.Proofs.FrontendStages.Loop
