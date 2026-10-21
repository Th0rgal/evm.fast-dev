import InitECandidate.Proofs.FrontendStages.Loop.Translate174
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody190_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody190_1 : HolLoopProg 64 :=
.mark loopBody190_0

def loopBody190_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody190_3 : HolLoopProg 64 :=
.mark loopBody190_2

def loopBody190_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody190_5 : HolLoopProg 64 :=
.mark loopBody190_4

def loopBody190_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody190_7 : HolLoopProg 64 :=
.mark loopBody190_6

def loopBody190_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody190_9 : HolLoopProg 64 :=
.mark loopBody190_8

def loopBody190_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody190_11 : HolLoopProg 64 :=
.mark loopBody190_10

def loopBody190_12 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 235) ([5, 6, 7, 8]) (some (5, loopBody190_11, loopBody190_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody190_13 : HolLoopProg 64 :=
.mark loopBody190_12

def loopBody190_14 : HolLoopProg 64 :=
.seq loopBody190_13 loopBody190_1

def loopBody190_15 : HolLoopProg 64 :=
.mark loopBody190_14

def loopBody190_16 : HolLoopProg 64 :=
.seq loopBody190_9 loopBody190_15

def loopBody190_17 : HolLoopProg 64 :=
.mark loopBody190_16

def loopBody190_18 : HolLoopProg 64 :=
.seq loopBody190_7 loopBody190_17

def loopBody190_19 : HolLoopProg 64 :=
.mark loopBody190_18

def loopBody190_20 : HolLoopProg 64 :=
.seq loopBody190_5 loopBody190_19

def loopBody190_21 : HolLoopProg 64 :=
.mark loopBody190_20

def loopBody190_22 : HolLoopProg 64 :=
.seq loopBody190_3 loopBody190_21

def loopBody190_23 : HolLoopProg 64 :=
.mark loopBody190_22

def loopBody190_24 : HolLoopProg 64 :=
.seq loopBody190_1 loopBody190_23

def loopBody190_25 : HolLoopProg 64 :=
.mark loopBody190_24

def loopBody190_26 : HolLoopProg 64 :=
.seq loopBody190_1 loopBody190_25

def loopBody190_27 : HolLoopProg 64 :=
.mark loopBody190_26

def loopBody190_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody190_29 : HolLoopProg 64 :=
.mark loopBody190_28

def loopBody190_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody190_31 : HolLoopProg 64 :=
.mark loopBody190_30

def loopBody190_32 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 236) ([5, 6, 7]) (some (5, loopBody190_11, loopBody190_1, (Flapjack.Spt.ln)))

def loopBody190_33 : HolLoopProg 64 :=
.mark loopBody190_32

def loopBody190_34 : HolLoopProg 64 :=
.seq loopBody190_33 loopBody190_1

def loopBody190_35 : HolLoopProg 64 :=
.mark loopBody190_34

def loopBody190_36 : HolLoopProg 64 :=
.seq loopBody190_31 loopBody190_35

def loopBody190_37 : HolLoopProg 64 :=
.mark loopBody190_36

def loopBody190_38 : HolLoopProg 64 :=
.seq loopBody190_5 loopBody190_37

def loopBody190_39 : HolLoopProg 64 :=
.mark loopBody190_38

def loopBody190_40 : HolLoopProg 64 :=
.seq loopBody190_29 loopBody190_39

def loopBody190_41 : HolLoopProg 64 :=
.mark loopBody190_40

def loopBody190_42 : HolLoopProg 64 :=
.seq loopBody190_1 loopBody190_41

def loopBody190_43 : HolLoopProg 64 :=
.mark loopBody190_42

def loopBody190_44 : HolLoopProg 64 :=
.seq loopBody190_1 loopBody190_43

def loopBody190_45 : HolLoopProg 64 :=
.mark loopBody190_44

def loopBody190_46 : HolLoopProg 64 :=
.seq loopBody190_27 loopBody190_45

def loopBody190_47 : HolLoopProg 64 :=
.mark loopBody190_46

def loopBody190_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody190_49 : HolLoopProg 64 :=
.mark loopBody190_48

def loopBody190_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody190_51 : HolLoopProg 64 :=
.mark loopBody190_50

def loopBody190_52 : HolLoopProg 64 :=
.seq loopBody190_51 loopBody190_1

def loopBody190_53 : HolLoopProg 64 :=
.mark loopBody190_52

def loopBody190_54 : HolLoopProg 64 :=
.seq loopBody190_49 loopBody190_53

def loopBody190_55 : HolLoopProg 64 :=
.mark loopBody190_54

def loopBody190_56 : HolLoopProg 64 :=
.seq loopBody190_47 loopBody190_55

def loopBody190_57 : HolLoopProg 64 :=
.mark loopBody190_56

def output190 : Nat × List Nat × HolLoopProg 64 :=
  (254, [0, 1, 2, 3], loopBody190_57)
end InitECandidate.Proofs.FrontendStages.Loop
