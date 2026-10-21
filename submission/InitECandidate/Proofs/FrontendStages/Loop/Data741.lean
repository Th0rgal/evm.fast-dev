import InitECandidate.Proofs.FrontendStages.Loop.Translate725
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody741_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody741_1 : HolLoopProg 64 :=
.mark loopBody741_0

def loopBody741_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody741_3 : HolLoopProg 64 :=
.mark loopBody741_2

def loopBody741_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 700) ([]) (some (2, loopBody741_3, loopBody741_1, (Flapjack.Spt.ln)))

def loopBody741_5 : HolLoopProg 64 :=
.mark loopBody741_4

def loopBody741_6 : HolLoopProg 64 :=
.seq loopBody741_5 loopBody741_1

def loopBody741_7 : HolLoopProg 64 :=
.mark loopBody741_6

def loopBody741_8 : HolLoopProg 64 :=
.seq loopBody741_1 loopBody741_7

def loopBody741_9 : HolLoopProg 64 :=
.mark loopBody741_8

def loopBody741_10 : HolLoopProg 64 :=
.seq loopBody741_1 loopBody741_9

def loopBody741_11 : HolLoopProg 64 :=
.mark loopBody741_10

def loopBody741_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody741_13 : HolLoopProg 64 :=
.mark loopBody741_12

def loopBody741_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody741_15 : HolLoopProg 64 :=
.mark loopBody741_14

def loopBody741_16 : HolLoopProg 64 :=
.seq loopBody741_15 loopBody741_1

def loopBody741_17 : HolLoopProg 64 :=
.mark loopBody741_16

def loopBody741_18 : HolLoopProg 64 :=
.seq loopBody741_13 loopBody741_17

def loopBody741_19 : HolLoopProg 64 :=
.mark loopBody741_18

def loopBody741_20 : HolLoopProg 64 :=
.seq loopBody741_11 loopBody741_19

def loopBody741_21 : HolLoopProg 64 :=
.mark loopBody741_20

def output741 : Nat × List Nat × HolLoopProg 64 :=
  (805, [], loopBody741_21)
end InitECandidate.Proofs.FrontendStages.Loop
