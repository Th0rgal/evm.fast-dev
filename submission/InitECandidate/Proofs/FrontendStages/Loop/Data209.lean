import InitECandidate.Proofs.FrontendStages.Loop.Translate193
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody209_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody209_1 : HolLoopProg 64 :=
.mark loopBody209_0

def loopBody209_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody209_3 : HolLoopProg 64 :=
.mark loopBody209_2

def loopBody209_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody209_3, loopBody209_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody209_5 : HolLoopProg 64 :=
.mark loopBody209_4

def loopBody209_6 : HolLoopProg 64 :=
.seq loopBody209_5 loopBody209_1

def loopBody209_7 : HolLoopProg 64 :=
.mark loopBody209_6

def loopBody209_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody209_9 : HolLoopProg 64 :=
.mark loopBody209_8

def loopBody209_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody209_11 : HolLoopProg 64 :=
.mark loopBody209_10

def loopBody209_12 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 272) ([5]) (some (5, loopBody209_11, loopBody209_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody209_13 : HolLoopProg 64 :=
.mark loopBody209_12

def loopBody209_14 : HolLoopProg 64 :=
.seq loopBody209_13 loopBody209_1

def loopBody209_15 : HolLoopProg 64 :=
.mark loopBody209_14

def loopBody209_16 : HolLoopProg 64 :=
.seq loopBody209_9 loopBody209_15

def loopBody209_17 : HolLoopProg 64 :=
.mark loopBody209_16

def loopBody209_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody209_19 : HolLoopProg 64 :=
.mark loopBody209_18

def loopBody209_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody209_21 : HolLoopProg 64 :=
.mark loopBody209_20

def loopBody209_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody209_23 : HolLoopProg 64 :=
.mark loopBody209_22

def loopBody209_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody209_25 : HolLoopProg 64 :=
.mark loopBody209_24

def loopBody209_26 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 158) ([6, 7, 8]) (some (6, loopBody209_25, loopBody209_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody209_27 : HolLoopProg 64 :=
.mark loopBody209_26

def loopBody209_28 : HolLoopProg 64 :=
.seq loopBody209_27 loopBody209_1

def loopBody209_29 : HolLoopProg 64 :=
.mark loopBody209_28

def loopBody209_30 : HolLoopProg 64 :=
.seq loopBody209_23 loopBody209_29

def loopBody209_31 : HolLoopProg 64 :=
.mark loopBody209_30

def loopBody209_32 : HolLoopProg 64 :=
.seq loopBody209_21 loopBody209_31

def loopBody209_33 : HolLoopProg 64 :=
.mark loopBody209_32

def loopBody209_34 : HolLoopProg 64 :=
.seq loopBody209_19 loopBody209_33

def loopBody209_35 : HolLoopProg 64 :=
.mark loopBody209_34

def loopBody209_36 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_35

def loopBody209_37 : HolLoopProg 64 :=
.mark loopBody209_36

def loopBody209_38 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_37

def loopBody209_39 : HolLoopProg 64 :=
.mark loopBody209_38

def loopBody209_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody209_41 : HolLoopProg 64 :=
.mark loopBody209_40

def loopBody209_42 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 70) ([6]) (some (6, loopBody209_25, loopBody209_1, (Flapjack.Spt.ln)))

def loopBody209_43 : HolLoopProg 64 :=
.mark loopBody209_42

def loopBody209_44 : HolLoopProg 64 :=
.seq loopBody209_43 loopBody209_1

def loopBody209_45 : HolLoopProg 64 :=
.mark loopBody209_44

def loopBody209_46 : HolLoopProg 64 :=
.seq loopBody209_41 loopBody209_45

def loopBody209_47 : HolLoopProg 64 :=
.mark loopBody209_46

def loopBody209_48 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_47

def loopBody209_49 : HolLoopProg 64 :=
.mark loopBody209_48

def loopBody209_50 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_49

def loopBody209_51 : HolLoopProg 64 :=
.mark loopBody209_50

def loopBody209_52 : HolLoopProg 64 :=
.seq loopBody209_39 loopBody209_51

def loopBody209_53 : HolLoopProg 64 :=
.mark loopBody209_52

def loopBody209_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody209_55 : HolLoopProg 64 :=
.mark loopBody209_54

def loopBody209_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody209_57 : HolLoopProg 64 :=
.mark loopBody209_56

def loopBody209_58 : HolLoopProg 64 :=
.seq loopBody209_57 loopBody209_1

def loopBody209_59 : HolLoopProg 64 :=
.mark loopBody209_58

def loopBody209_60 : HolLoopProg 64 :=
.seq loopBody209_55 loopBody209_59

def loopBody209_61 : HolLoopProg 64 :=
.mark loopBody209_60

def loopBody209_62 : HolLoopProg 64 :=
.seq loopBody209_53 loopBody209_61

def loopBody209_63 : HolLoopProg 64 :=
.mark loopBody209_62

def loopBody209_64 : HolLoopProg 64 :=
.seq loopBody209_17 loopBody209_63

def loopBody209_65 : HolLoopProg 64 :=
.mark loopBody209_64

def loopBody209_66 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_65

def loopBody209_67 : HolLoopProg 64 :=
.mark loopBody209_66

def loopBody209_68 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_67

def loopBody209_69 : HolLoopProg 64 :=
.mark loopBody209_68

def loopBody209_70 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_69

def loopBody209_71 : HolLoopProg 64 :=
.mark loopBody209_70

def loopBody209_72 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_71

def loopBody209_73 : HolLoopProg 64 :=
.mark loopBody209_72

def loopBody209_74 : HolLoopProg 64 :=
.seq loopBody209_7 loopBody209_73

def loopBody209_75 : HolLoopProg 64 :=
.mark loopBody209_74

def loopBody209_76 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_75

def loopBody209_77 : HolLoopProg 64 :=
.mark loopBody209_76

def loopBody209_78 : HolLoopProg 64 :=
.seq loopBody209_1 loopBody209_77

def loopBody209_79 : HolLoopProg 64 :=
.mark loopBody209_78

def output209 : Nat × List Nat × HolLoopProg 64 :=
  (273, [0, 1], loopBody209_79)
end InitECandidate.Proofs.FrontendStages.Loop
