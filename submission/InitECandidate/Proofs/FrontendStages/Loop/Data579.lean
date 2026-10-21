import InitECandidate.Proofs.FrontendStages.Loop.Translate563
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody579_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody579_1 : HolLoopProg 64 :=
.mark loopBody579_0

def loopBody579_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody579_3 : HolLoopProg 64 :=
.mark loopBody579_2

def loopBody579_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody579_5 : HolLoopProg 64 :=
.mark loopBody579_4

def loopBody579_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody579_7 : HolLoopProg 64 :=
.mark loopBody579_6

def loopBody579_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 18446744073709551615#64)

def loopBody579_9 : HolLoopProg 64 :=
.mark loopBody579_8

def loopBody579_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 4294967295#64)

def loopBody579_11 : HolLoopProg 64 :=
.mark loopBody579_10

def loopBody579_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody579_13 : HolLoopProg 64 :=
.mark loopBody579_12

def loopBody579_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 18446744069414584321#64)

def loopBody579_15 : HolLoopProg 64 :=
.mark loopBody579_14

def loopBody579_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 210) [4, 5, 6, 7, 8, 9, 10, 11] none

def loopBody579_17 : HolLoopProg 64 :=
.mark loopBody579_16

def loopBody579_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody579_19 : HolLoopProg 64 :=
.mark loopBody579_18

def loopBody579_20 : HolLoopProg 64 :=
.seq loopBody579_17 loopBody579_19

def loopBody579_21 : HolLoopProg 64 :=
.mark loopBody579_20

def loopBody579_22 : HolLoopProg 64 :=
.seq loopBody579_15 loopBody579_21

def loopBody579_23 : HolLoopProg 64 :=
.mark loopBody579_22

def loopBody579_24 : HolLoopProg 64 :=
.seq loopBody579_13 loopBody579_23

def loopBody579_25 : HolLoopProg 64 :=
.mark loopBody579_24

def loopBody579_26 : HolLoopProg 64 :=
.seq loopBody579_11 loopBody579_25

def loopBody579_27 : HolLoopProg 64 :=
.mark loopBody579_26

def loopBody579_28 : HolLoopProg 64 :=
.seq loopBody579_9 loopBody579_27

def loopBody579_29 : HolLoopProg 64 :=
.mark loopBody579_28

def loopBody579_30 : HolLoopProg 64 :=
.seq loopBody579_7 loopBody579_29

def loopBody579_31 : HolLoopProg 64 :=
.mark loopBody579_30

def loopBody579_32 : HolLoopProg 64 :=
.seq loopBody579_5 loopBody579_31

def loopBody579_33 : HolLoopProg 64 :=
.mark loopBody579_32

def loopBody579_34 : HolLoopProg 64 :=
.seq loopBody579_3 loopBody579_33

def loopBody579_35 : HolLoopProg 64 :=
.mark loopBody579_34

def loopBody579_36 : HolLoopProg 64 :=
.seq loopBody579_1 loopBody579_35

def loopBody579_37 : HolLoopProg 64 :=
.mark loopBody579_36

def output579 : Nat × List Nat × HolLoopProg 64 :=
  (643, [0, 1, 2, 3], loopBody579_37)
end InitECandidate.Proofs.FrontendStages.Loop
