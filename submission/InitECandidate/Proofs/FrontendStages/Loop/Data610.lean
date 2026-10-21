import InitECandidate.Proofs.FrontendStages.Loop.Translate594
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody610_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody610_1 : HolLoopProg 64 :=
.mark loopBody610_0

def loopBody610_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody610_3 : HolLoopProg 64 :=
.mark loopBody610_2

def loopBody610_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 0) (Flapjack.HolLoopExp.const 5#64))

def loopBody610_5 : HolLoopProg 64 :=
.mark loopBody610_4

def loopBody610_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody610_7 : HolLoopProg 64 :=
.mark loopBody610_6

def loopBody610_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 78) ([3, 4]) (some (3, loopBody610_7, loopBody610_1, (Flapjack.Spt.ln)))

def loopBody610_9 : HolLoopProg 64 :=
.mark loopBody610_8

def loopBody610_10 : HolLoopProg 64 :=
.seq loopBody610_9 loopBody610_1

def loopBody610_11 : HolLoopProg 64 :=
.mark loopBody610_10

def loopBody610_12 : HolLoopProg 64 :=
.seq loopBody610_5 loopBody610_11

def loopBody610_13 : HolLoopProg 64 :=
.mark loopBody610_12

def loopBody610_14 : HolLoopProg 64 :=
.seq loopBody610_3 loopBody610_13

def loopBody610_15 : HolLoopProg 64 :=
.mark loopBody610_14

def loopBody610_16 : HolLoopProg 64 :=
.seq loopBody610_1 loopBody610_15

def loopBody610_17 : HolLoopProg 64 :=
.mark loopBody610_16

def loopBody610_18 : HolLoopProg 64 :=
.seq loopBody610_1 loopBody610_17

def loopBody610_19 : HolLoopProg 64 :=
.mark loopBody610_18

def loopBody610_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody610_21 : HolLoopProg 64 :=
.mark loopBody610_20

def loopBody610_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody610_23 : HolLoopProg 64 :=
.mark loopBody610_22

def loopBody610_24 : HolLoopProg 64 :=
.seq loopBody610_23 loopBody610_1

def loopBody610_25 : HolLoopProg 64 :=
.mark loopBody610_24

def loopBody610_26 : HolLoopProg 64 :=
.seq loopBody610_21 loopBody610_25

def loopBody610_27 : HolLoopProg 64 :=
.mark loopBody610_26

def loopBody610_28 : HolLoopProg 64 :=
.seq loopBody610_19 loopBody610_27

def loopBody610_29 : HolLoopProg 64 :=
.mark loopBody610_28

def output610 : Nat × List Nat × HolLoopProg 64 :=
  (674, [0, 1], loopBody610_29)
end InitECandidate.Proofs.FrontendStages.Loop
