import InitECandidate.Proofs.FrontendStages.Loop.Translate684
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody700_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody700_1 : HolLoopProg 64 :=
.mark loopBody700_0

def loopBody700_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody700_3 : HolLoopProg 64 :=
.mark loopBody700_2

def loopBody700_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody700_5 : HolLoopProg 64 :=
.mark loopBody700_4

def loopBody700_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 144#64)

def loopBody700_7 : HolLoopProg 64 :=
.mark loopBody700_6

def loopBody700_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody700_9 : HolLoopProg 64 :=
.mark loopBody700_8

def loopBody700_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 77) ([3, 4, 5]) (some (3, loopBody700_9, loopBody700_1, (Flapjack.Spt.ln)))

def loopBody700_11 : HolLoopProg 64 :=
.mark loopBody700_10

def loopBody700_12 : HolLoopProg 64 :=
.seq loopBody700_11 loopBody700_1

def loopBody700_13 : HolLoopProg 64 :=
.mark loopBody700_12

def loopBody700_14 : HolLoopProg 64 :=
.seq loopBody700_7 loopBody700_13

def loopBody700_15 : HolLoopProg 64 :=
.mark loopBody700_14

def loopBody700_16 : HolLoopProg 64 :=
.seq loopBody700_5 loopBody700_15

def loopBody700_17 : HolLoopProg 64 :=
.mark loopBody700_16

def loopBody700_18 : HolLoopProg 64 :=
.seq loopBody700_3 loopBody700_17

def loopBody700_19 : HolLoopProg 64 :=
.mark loopBody700_18

def loopBody700_20 : HolLoopProg 64 :=
.seq loopBody700_1 loopBody700_19

def loopBody700_21 : HolLoopProg 64 :=
.mark loopBody700_20

def loopBody700_22 : HolLoopProg 64 :=
.seq loopBody700_1 loopBody700_21

def loopBody700_23 : HolLoopProg 64 :=
.mark loopBody700_22

def loopBody700_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody700_25 : HolLoopProg 64 :=
.mark loopBody700_24

def loopBody700_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody700_27 : HolLoopProg 64 :=
.mark loopBody700_26

def loopBody700_28 : HolLoopProg 64 :=
.seq loopBody700_27 loopBody700_1

def loopBody700_29 : HolLoopProg 64 :=
.mark loopBody700_28

def loopBody700_30 : HolLoopProg 64 :=
.seq loopBody700_25 loopBody700_29

def loopBody700_31 : HolLoopProg 64 :=
.mark loopBody700_30

def loopBody700_32 : HolLoopProg 64 :=
.seq loopBody700_23 loopBody700_31

def loopBody700_33 : HolLoopProg 64 :=
.mark loopBody700_32

def output700 : Nat × List Nat × HolLoopProg 64 :=
  (764, [0, 1], loopBody700_33)
end InitECandidate.Proofs.FrontendStages.Loop
