import InitECandidate.Proofs.FrontendStages.Loop.Translate306
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody322_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 16#64]))

def loopBody322_1 : HolLoopProg 64 :=
.mark loopBody322_0

def loopBody322_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody322_3 : HolLoopProg 64 :=
.mark loopBody322_2

def loopBody322_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody322_5 : HolLoopProg 64 :=
.mark loopBody322_4

def loopBody322_6 : HolLoopProg 64 :=
.seq loopBody322_3 loopBody322_5

def loopBody322_7 : HolLoopProg 64 :=
.mark loopBody322_6

def loopBody322_8 : HolLoopProg 64 :=
.seq loopBody322_1 loopBody322_7

def loopBody322_9 : HolLoopProg 64 :=
.mark loopBody322_8

def output322 : Nat × List Nat × HolLoopProg 64 :=
  (386, [], loopBody322_9)
end InitECandidate.Proofs.FrontendStages.Loop
