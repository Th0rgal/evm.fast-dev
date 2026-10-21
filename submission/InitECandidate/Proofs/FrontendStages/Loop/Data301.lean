import InitECandidate.Proofs.FrontendStages.Loop.Translate285
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody301_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody301_1 : HolLoopProg 64 :=
.mark loopBody301_0

def loopBody301_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 384#64]))

def loopBody301_3 : HolLoopProg 64 :=
.mark loopBody301_2

def loopBody301_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 392#64]))

def loopBody301_5 : HolLoopProg 64 :=
.mark loopBody301_4

def loopBody301_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody301_7 : HolLoopProg 64 :=
.mark loopBody301_6

def loopBody301_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody301_9 : HolLoopProg 64 :=
.mark loopBody301_8

def loopBody301_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 158) ([3, 4, 5]) (some (3, loopBody301_9, loopBody301_1, (Flapjack.Spt.ln)))

def loopBody301_11 : HolLoopProg 64 :=
.mark loopBody301_10

def loopBody301_12 : HolLoopProg 64 :=
.seq loopBody301_11 loopBody301_1

def loopBody301_13 : HolLoopProg 64 :=
.mark loopBody301_12

def loopBody301_14 : HolLoopProg 64 :=
.seq loopBody301_7 loopBody301_13

def loopBody301_15 : HolLoopProg 64 :=
.mark loopBody301_14

def loopBody301_16 : HolLoopProg 64 :=
.seq loopBody301_5 loopBody301_15

def loopBody301_17 : HolLoopProg 64 :=
.mark loopBody301_16

def loopBody301_18 : HolLoopProg 64 :=
.seq loopBody301_3 loopBody301_17

def loopBody301_19 : HolLoopProg 64 :=
.mark loopBody301_18

def loopBody301_20 : HolLoopProg 64 :=
.seq loopBody301_1 loopBody301_19

def loopBody301_21 : HolLoopProg 64 :=
.mark loopBody301_20

def loopBody301_22 : HolLoopProg 64 :=
.seq loopBody301_1 loopBody301_21

def loopBody301_23 : HolLoopProg 64 :=
.mark loopBody301_22

def loopBody301_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody301_25 : HolLoopProg 64 :=
.mark loopBody301_24

def loopBody301_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody301_27 : HolLoopProg 64 :=
.mark loopBody301_26

def loopBody301_28 : HolLoopProg 64 :=
.seq loopBody301_27 loopBody301_1

def loopBody301_29 : HolLoopProg 64 :=
.mark loopBody301_28

def loopBody301_30 : HolLoopProg 64 :=
.seq loopBody301_25 loopBody301_29

def loopBody301_31 : HolLoopProg 64 :=
.mark loopBody301_30

def loopBody301_32 : HolLoopProg 64 :=
.seq loopBody301_23 loopBody301_31

def loopBody301_33 : HolLoopProg 64 :=
.mark loopBody301_32

def output301 : Nat × List Nat × HolLoopProg 64 :=
  (365, [0, 1], loopBody301_33)
end InitECandidate.Proofs.FrontendStages.Loop
