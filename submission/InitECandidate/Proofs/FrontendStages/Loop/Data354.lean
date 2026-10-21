import InitECandidate.Proofs.FrontendStages.Loop.Translate338
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody354_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody354_1 : HolLoopProg 64 :=
.mark loopBody354_0

def loopBody354_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody354_3 : HolLoopProg 64 :=
.mark loopBody354_2

def loopBody354_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody354_5 : HolLoopProg 64 :=
.mark loopBody354_4

def loopBody354_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 417) ([2]) (some (2, loopBody354_5, loopBody354_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody354_7 : HolLoopProg 64 :=
.mark loopBody354_6

def loopBody354_8 : HolLoopProg 64 :=
.seq loopBody354_7 loopBody354_1

def loopBody354_9 : HolLoopProg 64 :=
.mark loopBody354_8

def loopBody354_10 : HolLoopProg 64 :=
.seq loopBody354_3 loopBody354_9

def loopBody354_11 : HolLoopProg 64 :=
.mark loopBody354_10

def loopBody354_12 : HolLoopProg 64 :=
.seq loopBody354_1 loopBody354_11

def loopBody354_13 : HolLoopProg 64 :=
.mark loopBody354_12

def loopBody354_14 : HolLoopProg 64 :=
.seq loopBody354_1 loopBody354_13

def loopBody354_15 : HolLoopProg 64 :=
.mark loopBody354_14

def loopBody354_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody354_17 : HolLoopProg 64 :=
.mark loopBody354_16

def loopBody354_18 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 415) ([2, 3]) (some (2, loopBody354_5, loopBody354_1, (Flapjack.Spt.ln)))

def loopBody354_19 : HolLoopProg 64 :=
.mark loopBody354_18

def loopBody354_20 : HolLoopProg 64 :=
.seq loopBody354_19 loopBody354_1

def loopBody354_21 : HolLoopProg 64 :=
.mark loopBody354_20

def loopBody354_22 : HolLoopProg 64 :=
.seq loopBody354_17 loopBody354_21

def loopBody354_23 : HolLoopProg 64 :=
.mark loopBody354_22

def loopBody354_24 : HolLoopProg 64 :=
.seq loopBody354_3 loopBody354_23

def loopBody354_25 : HolLoopProg 64 :=
.mark loopBody354_24

def loopBody354_26 : HolLoopProg 64 :=
.seq loopBody354_1 loopBody354_25

def loopBody354_27 : HolLoopProg 64 :=
.mark loopBody354_26

def loopBody354_28 : HolLoopProg 64 :=
.seq loopBody354_1 loopBody354_27

def loopBody354_29 : HolLoopProg 64 :=
.mark loopBody354_28

def loopBody354_30 : HolLoopProg 64 :=
.seq loopBody354_15 loopBody354_29

def loopBody354_31 : HolLoopProg 64 :=
.mark loopBody354_30

def loopBody354_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody354_33 : HolLoopProg 64 :=
.mark loopBody354_32

def loopBody354_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody354_35 : HolLoopProg 64 :=
.mark loopBody354_34

def loopBody354_36 : HolLoopProg 64 :=
.seq loopBody354_35 loopBody354_1

def loopBody354_37 : HolLoopProg 64 :=
.mark loopBody354_36

def loopBody354_38 : HolLoopProg 64 :=
.seq loopBody354_33 loopBody354_37

def loopBody354_39 : HolLoopProg 64 :=
.mark loopBody354_38

def loopBody354_40 : HolLoopProg 64 :=
.seq loopBody354_31 loopBody354_39

def loopBody354_41 : HolLoopProg 64 :=
.mark loopBody354_40

def output354 : Nat × List Nat × HolLoopProg 64 :=
  (418, [0], loopBody354_41)
end InitECandidate.Proofs.FrontendStages.Loop
