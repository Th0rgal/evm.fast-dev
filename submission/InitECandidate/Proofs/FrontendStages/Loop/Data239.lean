import InitECandidate.Proofs.FrontendStages.Loop.Translate223
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody239_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody239_1 : HolLoopProg 64 :=
.mark loopBody239_0

def loopBody239_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody239_3 : HolLoopProg 64 :=
.mark loopBody239_2

def loopBody239_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 32#64)

def loopBody239_5 : HolLoopProg 64 :=
.mark loopBody239_4

def loopBody239_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 144#64]))

def loopBody239_7 : HolLoopProg 64 :=
.mark loopBody239_6

def loopBody239_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody239_9 : HolLoopProg 64 :=
.mark loopBody239_8

def loopBody239_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ls PUnit.unit)) (some 284) ([3, 4, 5]) (some (3, loopBody239_9, loopBody239_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody239_11 : HolLoopProg 64 :=
.mark loopBody239_10

def loopBody239_12 : HolLoopProg 64 :=
.seq loopBody239_11 loopBody239_1

def loopBody239_13 : HolLoopProg 64 :=
.mark loopBody239_12

def loopBody239_14 : HolLoopProg 64 :=
.seq loopBody239_7 loopBody239_13

def loopBody239_15 : HolLoopProg 64 :=
.mark loopBody239_14

def loopBody239_16 : HolLoopProg 64 :=
.seq loopBody239_5 loopBody239_15

def loopBody239_17 : HolLoopProg 64 :=
.mark loopBody239_16

def loopBody239_18 : HolLoopProg 64 :=
.seq loopBody239_3 loopBody239_17

def loopBody239_19 : HolLoopProg 64 :=
.mark loopBody239_18

def loopBody239_20 : HolLoopProg 64 :=
.seq loopBody239_1 loopBody239_19

def loopBody239_21 : HolLoopProg 64 :=
.mark loopBody239_20

def loopBody239_22 : HolLoopProg 64 :=
.seq loopBody239_1 loopBody239_21

def loopBody239_23 : HolLoopProg 64 :=
.mark loopBody239_22

def loopBody239_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody239_25 : HolLoopProg 64 :=
.mark loopBody239_24

def loopBody239_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 144#64]))

def loopBody239_27 : HolLoopProg 64 :=
.mark loopBody239_26

def loopBody239_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 64#64)

def loopBody239_29 : HolLoopProg 64 :=
.mark loopBody239_28

def loopBody239_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 302) [2, 3, 4] none

def loopBody239_31 : HolLoopProg 64 :=
.mark loopBody239_30

def loopBody239_32 : HolLoopProg 64 :=
.seq loopBody239_31 loopBody239_1

def loopBody239_33 : HolLoopProg 64 :=
.mark loopBody239_32

def loopBody239_34 : HolLoopProg 64 :=
.seq loopBody239_29 loopBody239_33

def loopBody239_35 : HolLoopProg 64 :=
.mark loopBody239_34

def loopBody239_36 : HolLoopProg 64 :=
.seq loopBody239_27 loopBody239_35

def loopBody239_37 : HolLoopProg 64 :=
.mark loopBody239_36

def loopBody239_38 : HolLoopProg 64 :=
.seq loopBody239_25 loopBody239_37

def loopBody239_39 : HolLoopProg 64 :=
.mark loopBody239_38

def loopBody239_40 : HolLoopProg 64 :=
.seq loopBody239_23 loopBody239_39

def loopBody239_41 : HolLoopProg 64 :=
.mark loopBody239_40

def output239 : Nat × List Nat × HolLoopProg 64 :=
  (303, [0, 1], loopBody239_41)
end InitECandidate.Proofs.FrontendStages.Loop
