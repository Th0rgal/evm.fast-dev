import InitECandidate.Proofs.FrontendStages.Loop.Translate662
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody678_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody678_1 : HolLoopProg 64 :=
.mark loopBody678_0

def loopBody678_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody678_3 : HolLoopProg 64 :=
.mark loopBody678_2

def loopBody678_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody678_5 : HolLoopProg 64 :=
.mark loopBody678_4

def loopBody678_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 288#64)

def loopBody678_7 : HolLoopProg 64 :=
.mark loopBody678_6

def loopBody678_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody678_9 : HolLoopProg 64 :=
.mark loopBody678_8

def loopBody678_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 77) ([3, 4, 5]) (some (3, loopBody678_9, loopBody678_1, (Flapjack.Spt.ln)))

def loopBody678_11 : HolLoopProg 64 :=
.mark loopBody678_10

def loopBody678_12 : HolLoopProg 64 :=
.seq loopBody678_11 loopBody678_1

def loopBody678_13 : HolLoopProg 64 :=
.mark loopBody678_12

def loopBody678_14 : HolLoopProg 64 :=
.seq loopBody678_7 loopBody678_13

def loopBody678_15 : HolLoopProg 64 :=
.mark loopBody678_14

def loopBody678_16 : HolLoopProg 64 :=
.seq loopBody678_5 loopBody678_15

def loopBody678_17 : HolLoopProg 64 :=
.mark loopBody678_16

def loopBody678_18 : HolLoopProg 64 :=
.seq loopBody678_3 loopBody678_17

def loopBody678_19 : HolLoopProg 64 :=
.mark loopBody678_18

def loopBody678_20 : HolLoopProg 64 :=
.seq loopBody678_1 loopBody678_19

def loopBody678_21 : HolLoopProg 64 :=
.mark loopBody678_20

def loopBody678_22 : HolLoopProg 64 :=
.seq loopBody678_1 loopBody678_21

def loopBody678_23 : HolLoopProg 64 :=
.mark loopBody678_22

def loopBody678_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody678_25 : HolLoopProg 64 :=
.mark loopBody678_24

def loopBody678_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody678_27 : HolLoopProg 64 :=
.mark loopBody678_26

def loopBody678_28 : HolLoopProg 64 :=
.seq loopBody678_27 loopBody678_1

def loopBody678_29 : HolLoopProg 64 :=
.mark loopBody678_28

def loopBody678_30 : HolLoopProg 64 :=
.seq loopBody678_25 loopBody678_29

def loopBody678_31 : HolLoopProg 64 :=
.mark loopBody678_30

def loopBody678_32 : HolLoopProg 64 :=
.seq loopBody678_23 loopBody678_31

def loopBody678_33 : HolLoopProg 64 :=
.mark loopBody678_32

def output678 : Nat × List Nat × HolLoopProg 64 :=
  (742, [0, 1], loopBody678_33)
end InitECandidate.Proofs.FrontendStages.Loop
