import InitECandidate.Proofs.FrontendStages.Loop.Translate780
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody796_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody796_1 : HolLoopProg 64 :=
.mark loopBody796_0

def loopBody796_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody796_3 : HolLoopProg 64 :=
.mark loopBody796_2

def loopBody796_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 5#64)

def loopBody796_5 : HolLoopProg 64 :=
.mark loopBody796_4

def loopBody796_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody796_7 : HolLoopProg 64 :=
.mark loopBody796_6

def loopBody796_8 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 95) ([2, 3]) (some (2, loopBody796_7, loopBody796_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody796_9 : HolLoopProg 64 :=
.mark loopBody796_8

def loopBody796_10 : HolLoopProg 64 :=
.seq loopBody796_9 loopBody796_1

def loopBody796_11 : HolLoopProg 64 :=
.mark loopBody796_10

def loopBody796_12 : HolLoopProg 64 :=
.seq loopBody796_5 loopBody796_11

def loopBody796_13 : HolLoopProg 64 :=
.mark loopBody796_12

def loopBody796_14 : HolLoopProg 64 :=
.seq loopBody796_3 loopBody796_13

def loopBody796_15 : HolLoopProg 64 :=
.mark loopBody796_14

def loopBody796_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody796_17 : HolLoopProg 64 :=
.mark loopBody796_16

def loopBody796_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody796_19 : HolLoopProg 64 :=
.mark loopBody796_18

def loopBody796_20 : HolLoopProg 64 :=
.seq loopBody796_19 loopBody796_1

def loopBody796_21 : HolLoopProg 64 :=
.mark loopBody796_20

def loopBody796_22 : HolLoopProg 64 :=
.seq loopBody796_17 loopBody796_21

def loopBody796_23 : HolLoopProg 64 :=
.mark loopBody796_22

def loopBody796_24 : HolLoopProg 64 :=
.seq loopBody796_15 loopBody796_23

def loopBody796_25 : HolLoopProg 64 :=
.mark loopBody796_24

def loopBody796_26 : HolLoopProg 64 :=
.seq loopBody796_1 loopBody796_25

def loopBody796_27 : HolLoopProg 64 :=
.mark loopBody796_26

def loopBody796_28 : HolLoopProg 64 :=
.seq loopBody796_1 loopBody796_27

def loopBody796_29 : HolLoopProg 64 :=
.mark loopBody796_28

def output796 : Nat × List Nat × HolLoopProg 64 :=
  (860, [0], loopBody796_29)
end InitECandidate.Proofs.FrontendStages.Loop
