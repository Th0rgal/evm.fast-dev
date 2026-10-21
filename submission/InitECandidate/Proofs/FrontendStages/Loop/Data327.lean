import InitECandidate.Proofs.FrontendStages.Loop.Translate311
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody327_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody327_1 : HolLoopProg 64 :=
.mark loopBody327_0

def loopBody327_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 56#64)

def loopBody327_3 : HolLoopProg 64 :=
.mark loopBody327_2

def loopBody327_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody327_5 : HolLoopProg 64 :=
.mark loopBody327_4

def loopBody327_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 68) ([2]) (some (2, loopBody327_5, loopBody327_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody327_7 : HolLoopProg 64 :=
.mark loopBody327_6

def loopBody327_8 : HolLoopProg 64 :=
.seq loopBody327_7 loopBody327_1

def loopBody327_9 : HolLoopProg 64 :=
.mark loopBody327_8

def loopBody327_10 : HolLoopProg 64 :=
.seq loopBody327_3 loopBody327_9

def loopBody327_11 : HolLoopProg 64 :=
.mark loopBody327_10

def loopBody327_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody327_13 : HolLoopProg 64 :=
.mark loopBody327_12

def loopBody327_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody327_15 : HolLoopProg 64 :=
.mark loopBody327_14

def loopBody327_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 56#64)

def loopBody327_17 : HolLoopProg 64 :=
.mark loopBody327_16

def loopBody327_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody327_19 : HolLoopProg 64 :=
.mark loopBody327_18

def loopBody327_20 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 77) ([3, 4, 5]) (some (3, loopBody327_19, loopBody327_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody327_21 : HolLoopProg 64 :=
.mark loopBody327_20

def loopBody327_22 : HolLoopProg 64 :=
.seq loopBody327_21 loopBody327_1

def loopBody327_23 : HolLoopProg 64 :=
.mark loopBody327_22

def loopBody327_24 : HolLoopProg 64 :=
.seq loopBody327_17 loopBody327_23

def loopBody327_25 : HolLoopProg 64 :=
.mark loopBody327_24

def loopBody327_26 : HolLoopProg 64 :=
.seq loopBody327_15 loopBody327_25

def loopBody327_27 : HolLoopProg 64 :=
.mark loopBody327_26

def loopBody327_28 : HolLoopProg 64 :=
.seq loopBody327_13 loopBody327_27

def loopBody327_29 : HolLoopProg 64 :=
.mark loopBody327_28

def loopBody327_30 : HolLoopProg 64 :=
.seq loopBody327_1 loopBody327_29

def loopBody327_31 : HolLoopProg 64 :=
.mark loopBody327_30

def loopBody327_32 : HolLoopProg 64 :=
.seq loopBody327_1 loopBody327_31

def loopBody327_33 : HolLoopProg 64 :=
.mark loopBody327_32

def loopBody327_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody327_35 : HolLoopProg 64 :=
.mark loopBody327_34

def loopBody327_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody327_37 : HolLoopProg 64 :=
.mark loopBody327_36

def loopBody327_38 : HolLoopProg 64 :=
.seq loopBody327_37 loopBody327_1

def loopBody327_39 : HolLoopProg 64 :=
.mark loopBody327_38

def loopBody327_40 : HolLoopProg 64 :=
.seq loopBody327_35 loopBody327_39

def loopBody327_41 : HolLoopProg 64 :=
.mark loopBody327_40

def loopBody327_42 : HolLoopProg 64 :=
.seq loopBody327_33 loopBody327_41

def loopBody327_43 : HolLoopProg 64 :=
.mark loopBody327_42

def loopBody327_44 : HolLoopProg 64 :=
.seq loopBody327_11 loopBody327_43

def loopBody327_45 : HolLoopProg 64 :=
.mark loopBody327_44

def loopBody327_46 : HolLoopProg 64 :=
.seq loopBody327_1 loopBody327_45

def loopBody327_47 : HolLoopProg 64 :=
.mark loopBody327_46

def loopBody327_48 : HolLoopProg 64 :=
.seq loopBody327_1 loopBody327_47

def loopBody327_49 : HolLoopProg 64 :=
.mark loopBody327_48

def output327 : Nat × List Nat × HolLoopProg 64 :=
  (391, [0], loopBody327_49)
end InitECandidate.Proofs.FrontendStages.Loop
