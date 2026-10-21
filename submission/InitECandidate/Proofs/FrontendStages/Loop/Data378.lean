import InitECandidate.Proofs.FrontendStages.Loop.Translate362
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody378_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody378_1 : HolLoopProg 64 :=
.mark loopBody378_0

def loopBody378_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody378_3 : HolLoopProg 64 :=
.mark loopBody378_2

def loopBody378_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody378_5 : HolLoopProg 64 :=
.mark loopBody378_4

def loopBody378_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 435) ([2]) (some (2, loopBody378_5, loopBody378_1, (Flapjack.Spt.ln)))

def loopBody378_7 : HolLoopProg 64 :=
.mark loopBody378_6

def loopBody378_8 : HolLoopProg 64 :=
.seq loopBody378_7 loopBody378_1

def loopBody378_9 : HolLoopProg 64 :=
.mark loopBody378_8

def loopBody378_10 : HolLoopProg 64 :=
.seq loopBody378_3 loopBody378_9

def loopBody378_11 : HolLoopProg 64 :=
.mark loopBody378_10

def loopBody378_12 : HolLoopProg 64 :=
.seq loopBody378_1 loopBody378_11

def loopBody378_13 : HolLoopProg 64 :=
.mark loopBody378_12

def loopBody378_14 : HolLoopProg 64 :=
.seq loopBody378_1 loopBody378_13

def loopBody378_15 : HolLoopProg 64 :=
.mark loopBody378_14

def loopBody378_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody378_17 : HolLoopProg 64 :=
.mark loopBody378_16

def loopBody378_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody378_19 : HolLoopProg 64 :=
.mark loopBody378_18

def loopBody378_20 : HolLoopProg 64 :=
.seq loopBody378_19 loopBody378_1

def loopBody378_21 : HolLoopProg 64 :=
.mark loopBody378_20

def loopBody378_22 : HolLoopProg 64 :=
.seq loopBody378_17 loopBody378_21

def loopBody378_23 : HolLoopProg 64 :=
.mark loopBody378_22

def loopBody378_24 : HolLoopProg 64 :=
.seq loopBody378_15 loopBody378_23

def loopBody378_25 : HolLoopProg 64 :=
.mark loopBody378_24

def output378 : Nat × List Nat × HolLoopProg 64 :=
  (442, [0], loopBody378_25)
end InitECandidate.Proofs.FrontendStages.Loop
