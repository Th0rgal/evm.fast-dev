import InitECandidate.Proofs.FrontendStages.Loop.Translate374
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody390_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody390_1 : HolLoopProg 64 :=
.mark loopBody390_0

def loopBody390_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody390_3 : HolLoopProg 64 :=
.mark loopBody390_2

def loopBody390_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody390_5 : HolLoopProg 64 :=
.mark loopBody390_4

def loopBody390_6 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 198) ([4]) (some (4, loopBody390_5, loopBody390_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody390_7 : HolLoopProg 64 :=
.mark loopBody390_6

def loopBody390_8 : HolLoopProg 64 :=
.seq loopBody390_7 loopBody390_1

def loopBody390_9 : HolLoopProg 64 :=
.mark loopBody390_8

def loopBody390_10 : HolLoopProg 64 :=
.seq loopBody390_3 loopBody390_9

def loopBody390_11 : HolLoopProg 64 :=
.mark loopBody390_10

def loopBody390_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody390_13 : HolLoopProg 64 :=
.mark loopBody390_12

def loopBody390_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody390_15 : HolLoopProg 64 :=
.mark loopBody390_14

def loopBody390_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 32#64)

def loopBody390_17 : HolLoopProg 64 :=
.mark loopBody390_16

def loopBody390_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 2#64)

def loopBody390_19 : HolLoopProg 64 :=
.mark loopBody390_18

def loopBody390_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody390_21 : HolLoopProg 64 :=
.mark loopBody390_20

def loopBody390_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody390_23 : HolLoopProg 64 :=
.mark loopBody390_22

def loopBody390_24 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 453) ([5, 6, 7, 8, 9]) (some (5, loopBody390_23, loopBody390_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody390_25 : HolLoopProg 64 :=
.mark loopBody390_24

def loopBody390_26 : HolLoopProg 64 :=
.seq loopBody390_25 loopBody390_1

def loopBody390_27 : HolLoopProg 64 :=
.mark loopBody390_26

def loopBody390_28 : HolLoopProg 64 :=
.seq loopBody390_21 loopBody390_27

def loopBody390_29 : HolLoopProg 64 :=
.mark loopBody390_28

def loopBody390_30 : HolLoopProg 64 :=
.seq loopBody390_19 loopBody390_29

def loopBody390_31 : HolLoopProg 64 :=
.mark loopBody390_30

def loopBody390_32 : HolLoopProg 64 :=
.seq loopBody390_17 loopBody390_31

def loopBody390_33 : HolLoopProg 64 :=
.mark loopBody390_32

def loopBody390_34 : HolLoopProg 64 :=
.seq loopBody390_15 loopBody390_33

def loopBody390_35 : HolLoopProg 64 :=
.mark loopBody390_34

def loopBody390_36 : HolLoopProg 64 :=
.seq loopBody390_13 loopBody390_35

def loopBody390_37 : HolLoopProg 64 :=
.mark loopBody390_36

def loopBody390_38 : HolLoopProg 64 :=
.seq loopBody390_1 loopBody390_37

def loopBody390_39 : HolLoopProg 64 :=
.mark loopBody390_38

def loopBody390_40 : HolLoopProg 64 :=
.seq loopBody390_1 loopBody390_39

def loopBody390_41 : HolLoopProg 64 :=
.mark loopBody390_40

def loopBody390_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody390_43 : HolLoopProg 64 :=
.mark loopBody390_42

def loopBody390_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody390_45 : HolLoopProg 64 :=
.mark loopBody390_44

def loopBody390_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4, 5]

def loopBody390_47 : HolLoopProg 64 :=
.mark loopBody390_46

def loopBody390_48 : HolLoopProg 64 :=
.seq loopBody390_47 loopBody390_1

def loopBody390_49 : HolLoopProg 64 :=
.mark loopBody390_48

def loopBody390_50 : HolLoopProg 64 :=
.seq loopBody390_45 loopBody390_49

def loopBody390_51 : HolLoopProg 64 :=
.mark loopBody390_50

def loopBody390_52 : HolLoopProg 64 :=
.seq loopBody390_43 loopBody390_51

def loopBody390_53 : HolLoopProg 64 :=
.mark loopBody390_52

def loopBody390_54 : HolLoopProg 64 :=
.seq loopBody390_41 loopBody390_53

def loopBody390_55 : HolLoopProg 64 :=
.mark loopBody390_54

def loopBody390_56 : HolLoopProg 64 :=
.seq loopBody390_11 loopBody390_55

def loopBody390_57 : HolLoopProg 64 :=
.mark loopBody390_56

def loopBody390_58 : HolLoopProg 64 :=
.seq loopBody390_1 loopBody390_57

def loopBody390_59 : HolLoopProg 64 :=
.mark loopBody390_58

def loopBody390_60 : HolLoopProg 64 :=
.seq loopBody390_1 loopBody390_59

def loopBody390_61 : HolLoopProg 64 :=
.mark loopBody390_60

def loopBody390_62 : HolLoopProg 64 :=
.seq loopBody390_1 loopBody390_61

def loopBody390_63 : HolLoopProg 64 :=
.mark loopBody390_62

def loopBody390_64 : HolLoopProg 64 :=
.seq loopBody390_1 loopBody390_63

def loopBody390_65 : HolLoopProg 64 :=
.mark loopBody390_64

def output390 : Nat × List Nat × HolLoopProg 64 :=
  (454, [0, 1], loopBody390_65)
end InitECandidate.Proofs.FrontendStages.Loop
