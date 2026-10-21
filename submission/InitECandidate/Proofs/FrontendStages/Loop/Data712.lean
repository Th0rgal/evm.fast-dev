import InitECandidate.Proofs.FrontendStages.Loop.Translate696
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody712_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody712_1 : HolLoopProg 64 :=
.mark loopBody712_0

def loopBody712_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody712_3 : HolLoopProg 64 :=
.mark loopBody712_2

def loopBody712_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody712_5 : HolLoopProg 64 :=
.mark loopBody712_4

def loopBody712_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 288#64)

def loopBody712_7 : HolLoopProg 64 :=
.mark loopBody712_6

def loopBody712_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody712_9 : HolLoopProg 64 :=
.mark loopBody712_8

def loopBody712_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 77) ([3, 4, 5]) (some (3, loopBody712_9, loopBody712_1, (Flapjack.Spt.ln)))

def loopBody712_11 : HolLoopProg 64 :=
.mark loopBody712_10

def loopBody712_12 : HolLoopProg 64 :=
.seq loopBody712_11 loopBody712_1

def loopBody712_13 : HolLoopProg 64 :=
.mark loopBody712_12

def loopBody712_14 : HolLoopProg 64 :=
.seq loopBody712_7 loopBody712_13

def loopBody712_15 : HolLoopProg 64 :=
.mark loopBody712_14

def loopBody712_16 : HolLoopProg 64 :=
.seq loopBody712_5 loopBody712_15

def loopBody712_17 : HolLoopProg 64 :=
.mark loopBody712_16

def loopBody712_18 : HolLoopProg 64 :=
.seq loopBody712_3 loopBody712_17

def loopBody712_19 : HolLoopProg 64 :=
.mark loopBody712_18

def loopBody712_20 : HolLoopProg 64 :=
.seq loopBody712_1 loopBody712_19

def loopBody712_21 : HolLoopProg 64 :=
.mark loopBody712_20

def loopBody712_22 : HolLoopProg 64 :=
.seq loopBody712_1 loopBody712_21

def loopBody712_23 : HolLoopProg 64 :=
.mark loopBody712_22

def loopBody712_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody712_25 : HolLoopProg 64 :=
.mark loopBody712_24

def loopBody712_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody712_27 : HolLoopProg 64 :=
.mark loopBody712_26

def loopBody712_28 : HolLoopProg 64 :=
.seq loopBody712_27 loopBody712_1

def loopBody712_29 : HolLoopProg 64 :=
.mark loopBody712_28

def loopBody712_30 : HolLoopProg 64 :=
.seq loopBody712_25 loopBody712_29

def loopBody712_31 : HolLoopProg 64 :=
.mark loopBody712_30

def loopBody712_32 : HolLoopProg 64 :=
.seq loopBody712_23 loopBody712_31

def loopBody712_33 : HolLoopProg 64 :=
.mark loopBody712_32

def output712 : Nat × List Nat × HolLoopProg 64 :=
  (776, [0, 1], loopBody712_33)
end InitECandidate.Proofs.FrontendStages.Loop
