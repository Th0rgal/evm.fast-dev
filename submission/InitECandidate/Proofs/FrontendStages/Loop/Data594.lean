import InitECandidate.Proofs.FrontendStages.Loop.Translate578
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody594_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody594_1 : HolLoopProg 64 :=
.mark loopBody594_0

def loopBody594_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody594_3 : HolLoopProg 64 :=
.mark loopBody594_2

def loopBody594_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody594_5 : HolLoopProg 64 :=
.mark loopBody594_4

def loopBody594_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody594_7 : HolLoopProg 64 :=
.mark loopBody594_6

def loopBody594_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 17522657719365597833#64)

def loopBody594_9 : HolLoopProg 64 :=
.mark loopBody594_8

def loopBody594_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 13107472804851548667#64)

def loopBody594_11 : HolLoopProg 64 :=
.mark loopBody594_10

def loopBody594_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 5164255478447964150#64)

def loopBody594_13 : HolLoopProg 64 :=
.mark loopBody594_12

def loopBody594_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 493319470278259999#64)

def loopBody594_15 : HolLoopProg 64 :=
.mark loopBody594_14

def loopBody594_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 657) [4, 5, 6, 7, 8, 9, 10, 11] none

def loopBody594_17 : HolLoopProg 64 :=
.mark loopBody594_16

def loopBody594_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody594_19 : HolLoopProg 64 :=
.mark loopBody594_18

def loopBody594_20 : HolLoopProg 64 :=
.seq loopBody594_17 loopBody594_19

def loopBody594_21 : HolLoopProg 64 :=
.mark loopBody594_20

def loopBody594_22 : HolLoopProg 64 :=
.seq loopBody594_15 loopBody594_21

def loopBody594_23 : HolLoopProg 64 :=
.mark loopBody594_22

def loopBody594_24 : HolLoopProg 64 :=
.seq loopBody594_13 loopBody594_23

def loopBody594_25 : HolLoopProg 64 :=
.mark loopBody594_24

def loopBody594_26 : HolLoopProg 64 :=
.seq loopBody594_11 loopBody594_25

def loopBody594_27 : HolLoopProg 64 :=
.mark loopBody594_26

def loopBody594_28 : HolLoopProg 64 :=
.seq loopBody594_9 loopBody594_27

def loopBody594_29 : HolLoopProg 64 :=
.mark loopBody594_28

def loopBody594_30 : HolLoopProg 64 :=
.seq loopBody594_7 loopBody594_29

def loopBody594_31 : HolLoopProg 64 :=
.mark loopBody594_30

def loopBody594_32 : HolLoopProg 64 :=
.seq loopBody594_5 loopBody594_31

def loopBody594_33 : HolLoopProg 64 :=
.mark loopBody594_32

def loopBody594_34 : HolLoopProg 64 :=
.seq loopBody594_3 loopBody594_33

def loopBody594_35 : HolLoopProg 64 :=
.mark loopBody594_34

def loopBody594_36 : HolLoopProg 64 :=
.seq loopBody594_1 loopBody594_35

def loopBody594_37 : HolLoopProg 64 :=
.mark loopBody594_36

def output594 : Nat × List Nat × HolLoopProg 64 :=
  (658, [0, 1, 2, 3], loopBody594_37)
end InitECandidate.Proofs.FrontendStages.Loop
