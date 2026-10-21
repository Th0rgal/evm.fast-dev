import InitECandidate.Proofs.FrontendStages.Loop.Translate284
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody300_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.var 0)

def loopBody300_1 : HolLoopProg 64 :=
.mark loopBody300_0

def loopBody300_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody300_3 : HolLoopProg 64 :=
.mark loopBody300_2

def loopBody300_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody300_5 : HolLoopProg 64 :=
.mark loopBody300_4

def loopBody300_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 363) [1, 2, 3] none

def loopBody300_7 : HolLoopProg 64 :=
.mark loopBody300_6

def loopBody300_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody300_9 : HolLoopProg 64 :=
.mark loopBody300_8

def loopBody300_10 : HolLoopProg 64 :=
.seq loopBody300_7 loopBody300_9

def loopBody300_11 : HolLoopProg 64 :=
.mark loopBody300_10

def loopBody300_12 : HolLoopProg 64 :=
.seq loopBody300_5 loopBody300_11

def loopBody300_13 : HolLoopProg 64 :=
.mark loopBody300_12

def loopBody300_14 : HolLoopProg 64 :=
.seq loopBody300_3 loopBody300_13

def loopBody300_15 : HolLoopProg 64 :=
.mark loopBody300_14

def loopBody300_16 : HolLoopProg 64 :=
.seq loopBody300_1 loopBody300_15

def loopBody300_17 : HolLoopProg 64 :=
.mark loopBody300_16

def output300 : Nat × List Nat × HolLoopProg 64 :=
  (364, [0], loopBody300_17)
end InitECandidate.Proofs.FrontendStages.Loop
