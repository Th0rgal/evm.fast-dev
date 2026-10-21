import InitECandidate.Proofs.FrontendStages.Loop.Translate645
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody661_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody661_1 : HolLoopProg 64 :=
.mark loopBody661_0

def loopBody661_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody661_3 : HolLoopProg 64 :=
.mark loopBody661_2

def loopBody661_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody661_5 : HolLoopProg 64 :=
.mark loopBody661_4

def loopBody661_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 96#64)

def loopBody661_7 : HolLoopProg 64 :=
.mark loopBody661_6

def loopBody661_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody661_9 : HolLoopProg 64 :=
.mark loopBody661_8

def loopBody661_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 77) ([3, 4, 5]) (some (3, loopBody661_9, loopBody661_1, (Flapjack.Spt.ln)))

def loopBody661_11 : HolLoopProg 64 :=
.mark loopBody661_10

def loopBody661_12 : HolLoopProg 64 :=
.seq loopBody661_11 loopBody661_1

def loopBody661_13 : HolLoopProg 64 :=
.mark loopBody661_12

def loopBody661_14 : HolLoopProg 64 :=
.seq loopBody661_7 loopBody661_13

def loopBody661_15 : HolLoopProg 64 :=
.mark loopBody661_14

def loopBody661_16 : HolLoopProg 64 :=
.seq loopBody661_5 loopBody661_15

def loopBody661_17 : HolLoopProg 64 :=
.mark loopBody661_16

def loopBody661_18 : HolLoopProg 64 :=
.seq loopBody661_3 loopBody661_17

def loopBody661_19 : HolLoopProg 64 :=
.mark loopBody661_18

def loopBody661_20 : HolLoopProg 64 :=
.seq loopBody661_1 loopBody661_19

def loopBody661_21 : HolLoopProg 64 :=
.mark loopBody661_20

def loopBody661_22 : HolLoopProg 64 :=
.seq loopBody661_1 loopBody661_21

def loopBody661_23 : HolLoopProg 64 :=
.mark loopBody661_22

def loopBody661_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody661_25 : HolLoopProg 64 :=
.mark loopBody661_24

def loopBody661_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody661_27 : HolLoopProg 64 :=
.mark loopBody661_26

def loopBody661_28 : HolLoopProg 64 :=
.seq loopBody661_27 loopBody661_1

def loopBody661_29 : HolLoopProg 64 :=
.mark loopBody661_28

def loopBody661_30 : HolLoopProg 64 :=
.seq loopBody661_25 loopBody661_29

def loopBody661_31 : HolLoopProg 64 :=
.mark loopBody661_30

def loopBody661_32 : HolLoopProg 64 :=
.seq loopBody661_23 loopBody661_31

def loopBody661_33 : HolLoopProg 64 :=
.mark loopBody661_32

def output661 : Nat × List Nat × HolLoopProg 64 :=
  (725, [0, 1], loopBody661_33)
end InitECandidate.Proofs.FrontendStages.Loop
