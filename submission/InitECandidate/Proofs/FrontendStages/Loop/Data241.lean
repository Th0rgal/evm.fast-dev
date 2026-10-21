import InitECandidate.Proofs.FrontendStages.Loop.Translate225
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody241_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody241_1 : HolLoopProg 64 :=
.mark loopBody241_0

def loopBody241_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody241_3 : HolLoopProg 64 :=
.mark loopBody241_2

def loopBody241_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody241_5 : HolLoopProg 64 :=
.mark loopBody241_4

def loopBody241_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody241_7 : HolLoopProg 64 :=
.mark loopBody241_6

def loopBody241_8 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 301) ([4, 5]) (some (4, loopBody241_7, loopBody241_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody241_9 : HolLoopProg 64 :=
.mark loopBody241_8

def loopBody241_10 : HolLoopProg 64 :=
.seq loopBody241_9 loopBody241_1

def loopBody241_11 : HolLoopProg 64 :=
.mark loopBody241_10

def loopBody241_12 : HolLoopProg 64 :=
.seq loopBody241_5 loopBody241_11

def loopBody241_13 : HolLoopProg 64 :=
.mark loopBody241_12

def loopBody241_14 : HolLoopProg 64 :=
.seq loopBody241_3 loopBody241_13

def loopBody241_15 : HolLoopProg 64 :=
.mark loopBody241_14

def loopBody241_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody241_17 : HolLoopProg 64 :=
.mark loopBody241_16

def loopBody241_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody241_19 : HolLoopProg 64 :=
.mark loopBody241_18

def loopBody241_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 304) [4, 5] none

def loopBody241_21 : HolLoopProg 64 :=
.mark loopBody241_20

def loopBody241_22 : HolLoopProg 64 :=
.seq loopBody241_21 loopBody241_1

def loopBody241_23 : HolLoopProg 64 :=
.mark loopBody241_22

def loopBody241_24 : HolLoopProg 64 :=
.seq loopBody241_19 loopBody241_23

def loopBody241_25 : HolLoopProg 64 :=
.mark loopBody241_24

def loopBody241_26 : HolLoopProg 64 :=
.seq loopBody241_17 loopBody241_25

def loopBody241_27 : HolLoopProg 64 :=
.mark loopBody241_26

def loopBody241_28 : HolLoopProg 64 :=
.seq loopBody241_15 loopBody241_27

def loopBody241_29 : HolLoopProg 64 :=
.mark loopBody241_28

def loopBody241_30 : HolLoopProg 64 :=
.seq loopBody241_1 loopBody241_29

def loopBody241_31 : HolLoopProg 64 :=
.mark loopBody241_30

def loopBody241_32 : HolLoopProg 64 :=
.seq loopBody241_1 loopBody241_31

def loopBody241_33 : HolLoopProg 64 :=
.mark loopBody241_32

def output241 : Nat × List Nat × HolLoopProg 64 :=
  (305, [0, 1, 2], loopBody241_33)
end InitECandidate.Proofs.FrontendStages.Loop
