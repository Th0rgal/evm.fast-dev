import InitECandidate.Proofs.FrontendStages.Loop.Translate404
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody420_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody420_1 : HolLoopProg 64 :=
.mark loopBody420_0

def loopBody420_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 176#64)

def loopBody420_3 : HolLoopProg 64 :=
.mark loopBody420_2

def loopBody420_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody420_5 : HolLoopProg 64 :=
.mark loopBody420_4

def loopBody420_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 74) ([2]) (some (2, loopBody420_5, loopBody420_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody420_7 : HolLoopProg 64 :=
.mark loopBody420_6

def loopBody420_8 : HolLoopProg 64 :=
.seq loopBody420_7 loopBody420_1

def loopBody420_9 : HolLoopProg 64 :=
.mark loopBody420_8

def loopBody420_10 : HolLoopProg 64 :=
.seq loopBody420_3 loopBody420_9

def loopBody420_11 : HolLoopProg 64 :=
.mark loopBody420_10

def loopBody420_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody420_13 : HolLoopProg 64 :=
.mark loopBody420_12

def loopBody420_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 176#64)

def loopBody420_15 : HolLoopProg 64 :=
.mark loopBody420_14

def loopBody420_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody420_17 : HolLoopProg 64 :=
.mark loopBody420_16

def loopBody420_18 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 78) ([3, 4]) (some (3, loopBody420_17, loopBody420_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody420_19 : HolLoopProg 64 :=
.mark loopBody420_18

def loopBody420_20 : HolLoopProg 64 :=
.seq loopBody420_19 loopBody420_1

def loopBody420_21 : HolLoopProg 64 :=
.mark loopBody420_20

def loopBody420_22 : HolLoopProg 64 :=
.seq loopBody420_15 loopBody420_21

def loopBody420_23 : HolLoopProg 64 :=
.mark loopBody420_22

def loopBody420_24 : HolLoopProg 64 :=
.seq loopBody420_13 loopBody420_23

def loopBody420_25 : HolLoopProg 64 :=
.mark loopBody420_24

def loopBody420_26 : HolLoopProg 64 :=
.seq loopBody420_1 loopBody420_25

def loopBody420_27 : HolLoopProg 64 :=
.mark loopBody420_26

def loopBody420_28 : HolLoopProg 64 :=
.seq loopBody420_1 loopBody420_27

def loopBody420_29 : HolLoopProg 64 :=
.mark loopBody420_28

def loopBody420_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody420_31 : HolLoopProg 64 :=
.mark loopBody420_30

def loopBody420_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody420_33 : HolLoopProg 64 :=
.mark loopBody420_32

def loopBody420_34 : HolLoopProg 64 :=
.seq loopBody420_33 loopBody420_1

def loopBody420_35 : HolLoopProg 64 :=
.mark loopBody420_34

def loopBody420_36 : HolLoopProg 64 :=
.seq loopBody420_31 loopBody420_35

def loopBody420_37 : HolLoopProg 64 :=
.mark loopBody420_36

def loopBody420_38 : HolLoopProg 64 :=
.seq loopBody420_29 loopBody420_37

def loopBody420_39 : HolLoopProg 64 :=
.mark loopBody420_38

def loopBody420_40 : HolLoopProg 64 :=
.seq loopBody420_11 loopBody420_39

def loopBody420_41 : HolLoopProg 64 :=
.mark loopBody420_40

def loopBody420_42 : HolLoopProg 64 :=
.seq loopBody420_1 loopBody420_41

def loopBody420_43 : HolLoopProg 64 :=
.mark loopBody420_42

def loopBody420_44 : HolLoopProg 64 :=
.seq loopBody420_1 loopBody420_43

def loopBody420_45 : HolLoopProg 64 :=
.mark loopBody420_44

def output420 : Nat × List Nat × HolLoopProg 64 :=
  (484, [], loopBody420_45)
end InitECandidate.Proofs.FrontendStages.Loop
