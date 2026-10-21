import InitECandidate.Proofs.FrontendStages.Loop.Translate672
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody688_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody688_1 : HolLoopProg 64 :=
.mark loopBody688_0

def loopBody688_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody688_3 : HolLoopProg 64 :=
.mark loopBody688_2

def loopBody688_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody688_5 : HolLoopProg 64 :=
.mark loopBody688_4

def loopBody688_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 744) ([2]) (some (2, loopBody688_5, loopBody688_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody688_7 : HolLoopProg 64 :=
.mark loopBody688_6

def loopBody688_8 : HolLoopProg 64 :=
.seq loopBody688_7 loopBody688_1

def loopBody688_9 : HolLoopProg 64 :=
.mark loopBody688_8

def loopBody688_10 : HolLoopProg 64 :=
.seq loopBody688_3 loopBody688_9

def loopBody688_11 : HolLoopProg 64 :=
.mark loopBody688_10

def loopBody688_12 : HolLoopProg 64 :=
.seq loopBody688_1 loopBody688_11

def loopBody688_13 : HolLoopProg 64 :=
.mark loopBody688_12

def loopBody688_14 : HolLoopProg 64 :=
.seq loopBody688_1 loopBody688_13

def loopBody688_15 : HolLoopProg 64 :=
.mark loopBody688_14

def loopBody688_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 288#64])

def loopBody688_17 : HolLoopProg 64 :=
.mark loopBody688_16

def loopBody688_18 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 743) ([2]) (some (2, loopBody688_5, loopBody688_1, (Flapjack.Spt.ln)))

def loopBody688_19 : HolLoopProg 64 :=
.mark loopBody688_18

def loopBody688_20 : HolLoopProg 64 :=
.seq loopBody688_19 loopBody688_1

def loopBody688_21 : HolLoopProg 64 :=
.mark loopBody688_20

def loopBody688_22 : HolLoopProg 64 :=
.seq loopBody688_17 loopBody688_21

def loopBody688_23 : HolLoopProg 64 :=
.mark loopBody688_22

def loopBody688_24 : HolLoopProg 64 :=
.seq loopBody688_1 loopBody688_23

def loopBody688_25 : HolLoopProg 64 :=
.mark loopBody688_24

def loopBody688_26 : HolLoopProg 64 :=
.seq loopBody688_1 loopBody688_25

def loopBody688_27 : HolLoopProg 64 :=
.mark loopBody688_26

def loopBody688_28 : HolLoopProg 64 :=
.seq loopBody688_15 loopBody688_27

def loopBody688_29 : HolLoopProg 64 :=
.mark loopBody688_28

def loopBody688_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody688_31 : HolLoopProg 64 :=
.mark loopBody688_30

def loopBody688_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody688_33 : HolLoopProg 64 :=
.mark loopBody688_32

def loopBody688_34 : HolLoopProg 64 :=
.seq loopBody688_33 loopBody688_1

def loopBody688_35 : HolLoopProg 64 :=
.mark loopBody688_34

def loopBody688_36 : HolLoopProg 64 :=
.seq loopBody688_31 loopBody688_35

def loopBody688_37 : HolLoopProg 64 :=
.mark loopBody688_36

def loopBody688_38 : HolLoopProg 64 :=
.seq loopBody688_29 loopBody688_37

def loopBody688_39 : HolLoopProg 64 :=
.mark loopBody688_38

def output688 : Nat × List Nat × HolLoopProg 64 :=
  (752, [0], loopBody688_39)
end InitECandidate.Proofs.FrontendStages.Loop
