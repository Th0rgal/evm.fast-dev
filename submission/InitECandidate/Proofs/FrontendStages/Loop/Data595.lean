import InitECandidate.Proofs.FrontendStages.Loop.Translate579
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody595_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody595_1 : HolLoopProg 64 :=
.mark loopBody595_0

def loopBody595_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody595_3 : HolLoopProg 64 :=
.mark loopBody595_2

def loopBody595_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody595_5 : HolLoopProg 64 :=
.mark loopBody595_4

def loopBody595_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody595_7 : HolLoopProg 64 :=
.mark loopBody595_6

def loopBody595_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody595_9 : HolLoopProg 64 :=
.mark loopBody595_8

def loopBody595_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody595_11 : HolLoopProg 64 :=
.mark loopBody595_10

def loopBody595_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody595_13 : HolLoopProg 64 :=
.mark loopBody595_12

def loopBody595_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody595_15 : HolLoopProg 64 :=
.mark loopBody595_14

def loopBody595_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 657) [4, 5, 6, 7, 8, 9, 10, 11] none

def loopBody595_17 : HolLoopProg 64 :=
.mark loopBody595_16

def loopBody595_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody595_19 : HolLoopProg 64 :=
.mark loopBody595_18

def loopBody595_20 : HolLoopProg 64 :=
.seq loopBody595_17 loopBody595_19

def loopBody595_21 : HolLoopProg 64 :=
.mark loopBody595_20

def loopBody595_22 : HolLoopProg 64 :=
.seq loopBody595_15 loopBody595_21

def loopBody595_23 : HolLoopProg 64 :=
.mark loopBody595_22

def loopBody595_24 : HolLoopProg 64 :=
.seq loopBody595_13 loopBody595_23

def loopBody595_25 : HolLoopProg 64 :=
.mark loopBody595_24

def loopBody595_26 : HolLoopProg 64 :=
.seq loopBody595_11 loopBody595_25

def loopBody595_27 : HolLoopProg 64 :=
.mark loopBody595_26

def loopBody595_28 : HolLoopProg 64 :=
.seq loopBody595_9 loopBody595_27

def loopBody595_29 : HolLoopProg 64 :=
.mark loopBody595_28

def loopBody595_30 : HolLoopProg 64 :=
.seq loopBody595_7 loopBody595_29

def loopBody595_31 : HolLoopProg 64 :=
.mark loopBody595_30

def loopBody595_32 : HolLoopProg 64 :=
.seq loopBody595_5 loopBody595_31

def loopBody595_33 : HolLoopProg 64 :=
.mark loopBody595_32

def loopBody595_34 : HolLoopProg 64 :=
.seq loopBody595_3 loopBody595_33

def loopBody595_35 : HolLoopProg 64 :=
.mark loopBody595_34

def loopBody595_36 : HolLoopProg 64 :=
.seq loopBody595_1 loopBody595_35

def loopBody595_37 : HolLoopProg 64 :=
.mark loopBody595_36

def output595 : Nat × List Nat × HolLoopProg 64 :=
  (659, [0, 1, 2, 3], loopBody595_37)
end InitECandidate.Proofs.FrontendStages.Loop
