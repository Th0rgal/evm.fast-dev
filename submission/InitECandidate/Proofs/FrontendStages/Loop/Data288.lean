import InitECandidate.Proofs.FrontendStages.Loop.Translate272
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody288_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
    (Flapjack.HolLoopExp.load
      (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 264#64]))
    (Flapjack.HolLoopExp.const 17#64))

def loopBody288_1 : HolLoopProg 64 :=
.mark loopBody288_0

def loopBody288_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody288_3 : HolLoopProg 64 :=
.mark loopBody288_2

def loopBody288_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody288_5 : HolLoopProg 64 :=
.mark loopBody288_4

def loopBody288_6 : HolLoopProg 64 :=
.seq loopBody288_3 loopBody288_5

def loopBody288_7 : HolLoopProg 64 :=
.mark loopBody288_6

def loopBody288_8 : HolLoopProg 64 :=
.seq loopBody288_1 loopBody288_7

def loopBody288_9 : HolLoopProg 64 :=
.mark loopBody288_8

def output288 : Nat × List Nat × HolLoopProg 64 :=
  (352, [0], loopBody288_9)
end InitECandidate.Proofs.FrontendStages.Loop
