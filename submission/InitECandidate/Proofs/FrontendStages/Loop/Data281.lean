import InitECandidate.Proofs.FrontendStages.Loop.Translate265
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody281_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 152#64]))

def loopBody281_1 : HolLoopProg 64 :=
.mark loopBody281_0

def loopBody281_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody281_3 : HolLoopProg 64 :=
.mark loopBody281_2

def loopBody281_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody281_5 : HolLoopProg 64 :=
.mark loopBody281_4

def loopBody281_6 : HolLoopProg 64 :=
.seq loopBody281_3 loopBody281_5

def loopBody281_7 : HolLoopProg 64 :=
.mark loopBody281_6

def loopBody281_8 : HolLoopProg 64 :=
.seq loopBody281_1 loopBody281_7

def loopBody281_9 : HolLoopProg 64 :=
.mark loopBody281_8

def output281 : Nat × List Nat × HolLoopProg 64 :=
  (345, [0], loopBody281_9)
end InitECandidate.Proofs.FrontendStages.Loop
