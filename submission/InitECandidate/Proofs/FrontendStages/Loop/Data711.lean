import InitECandidate.Proofs.FrontendStages.Loop.Translate695
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody711_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody711_1 : HolLoopProg 64 :=
.mark loopBody711_0

def loopBody711_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 728) [1] none

def loopBody711_3 : HolLoopProg 64 :=
.mark loopBody711_2

def loopBody711_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody711_5 : HolLoopProg 64 :=
.mark loopBody711_4

def loopBody711_6 : HolLoopProg 64 :=
.seq loopBody711_3 loopBody711_5

def loopBody711_7 : HolLoopProg 64 :=
.mark loopBody711_6

def loopBody711_8 : HolLoopProg 64 :=
.seq loopBody711_1 loopBody711_7

def loopBody711_9 : HolLoopProg 64 :=
.mark loopBody711_8

def output711 : Nat × List Nat × HolLoopProg 64 :=
  (775, [0], loopBody711_9)
end InitECandidate.Proofs.FrontendStages.Loop
