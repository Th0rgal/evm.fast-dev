import InitECandidate.Proofs.FrontendStages.Loop.Translate403
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody419_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody419_1 : HolLoopProg 64 :=
.mark loopBody419_0

def loopBody419_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 176#64)

def loopBody419_3 : HolLoopProg 64 :=
.mark loopBody419_2

def loopBody419_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody419_5 : HolLoopProg 64 :=
.mark loopBody419_4

def loopBody419_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 68) ([2]) (some (2, loopBody419_5, loopBody419_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody419_7 : HolLoopProg 64 :=
.mark loopBody419_6

def loopBody419_8 : HolLoopProg 64 :=
.seq loopBody419_7 loopBody419_1

def loopBody419_9 : HolLoopProg 64 :=
.mark loopBody419_8

def loopBody419_10 : HolLoopProg 64 :=
.seq loopBody419_3 loopBody419_9

def loopBody419_11 : HolLoopProg 64 :=
.mark loopBody419_10

def loopBody419_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody419_13 : HolLoopProg 64 :=
.mark loopBody419_12

def loopBody419_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 176#64)

def loopBody419_15 : HolLoopProg 64 :=
.mark loopBody419_14

def loopBody419_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody419_17 : HolLoopProg 64 :=
.mark loopBody419_16

def loopBody419_18 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 78) ([3, 4]) (some (3, loopBody419_17, loopBody419_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody419_19 : HolLoopProg 64 :=
.mark loopBody419_18

def loopBody419_20 : HolLoopProg 64 :=
.seq loopBody419_19 loopBody419_1

def loopBody419_21 : HolLoopProg 64 :=
.mark loopBody419_20

def loopBody419_22 : HolLoopProg 64 :=
.seq loopBody419_15 loopBody419_21

def loopBody419_23 : HolLoopProg 64 :=
.mark loopBody419_22

def loopBody419_24 : HolLoopProg 64 :=
.seq loopBody419_13 loopBody419_23

def loopBody419_25 : HolLoopProg 64 :=
.mark loopBody419_24

def loopBody419_26 : HolLoopProg 64 :=
.seq loopBody419_1 loopBody419_25

def loopBody419_27 : HolLoopProg 64 :=
.mark loopBody419_26

def loopBody419_28 : HolLoopProg 64 :=
.seq loopBody419_1 loopBody419_27

def loopBody419_29 : HolLoopProg 64 :=
.mark loopBody419_28

def loopBody419_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody419_31 : HolLoopProg 64 :=
.mark loopBody419_30

def loopBody419_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody419_33 : HolLoopProg 64 :=
.mark loopBody419_32

def loopBody419_34 : HolLoopProg 64 :=
.seq loopBody419_33 loopBody419_1

def loopBody419_35 : HolLoopProg 64 :=
.mark loopBody419_34

def loopBody419_36 : HolLoopProg 64 :=
.seq loopBody419_31 loopBody419_35

def loopBody419_37 : HolLoopProg 64 :=
.mark loopBody419_36

def loopBody419_38 : HolLoopProg 64 :=
.seq loopBody419_29 loopBody419_37

def loopBody419_39 : HolLoopProg 64 :=
.mark loopBody419_38

def loopBody419_40 : HolLoopProg 64 :=
.seq loopBody419_11 loopBody419_39

def loopBody419_41 : HolLoopProg 64 :=
.mark loopBody419_40

def loopBody419_42 : HolLoopProg 64 :=
.seq loopBody419_1 loopBody419_41

def loopBody419_43 : HolLoopProg 64 :=
.mark loopBody419_42

def loopBody419_44 : HolLoopProg 64 :=
.seq loopBody419_1 loopBody419_43

def loopBody419_45 : HolLoopProg 64 :=
.mark loopBody419_44

def output419 : Nat × List Nat × HolLoopProg 64 :=
  (483, [], loopBody419_45)
end InitECandidate.Proofs.FrontendStages.Loop
