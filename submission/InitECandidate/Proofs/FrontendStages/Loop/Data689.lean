import InitECandidate.Proofs.FrontendStages.Loop.Translate673
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody689_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody689_1 : HolLoopProg 64 :=
.mark loopBody689_0

def loopBody689_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody689_3 : HolLoopProg 64 :=
.mark loopBody689_2

def loopBody689_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 69) ([]) (some (2, loopBody689_3, loopBody689_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody689_5 : HolLoopProg 64 :=
.mark loopBody689_4

def loopBody689_6 : HolLoopProg 64 :=
.seq loopBody689_5 loopBody689_1

def loopBody689_7 : HolLoopProg 64 :=
.mark loopBody689_6

def loopBody689_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 576#64)

def loopBody689_9 : HolLoopProg 64 :=
.mark loopBody689_8

def loopBody689_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody689_11 : HolLoopProg 64 :=
.mark loopBody689_10

def loopBody689_12 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([3]) (some (3, loopBody689_11, loopBody689_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody689_13 : HolLoopProg 64 :=
.mark loopBody689_12

def loopBody689_14 : HolLoopProg 64 :=
.seq loopBody689_13 loopBody689_1

def loopBody689_15 : HolLoopProg 64 :=
.mark loopBody689_14

def loopBody689_16 : HolLoopProg 64 :=
.seq loopBody689_9 loopBody689_15

def loopBody689_17 : HolLoopProg 64 :=
.mark loopBody689_16

def loopBody689_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody689_19 : HolLoopProg 64 :=
.mark loopBody689_18

def loopBody689_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody689_21 : HolLoopProg 64 :=
.mark loopBody689_20

def loopBody689_22 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 752) ([4]) (some (4, loopBody689_21, loopBody689_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody689_23 : HolLoopProg 64 :=
.mark loopBody689_22

def loopBody689_24 : HolLoopProg 64 :=
.seq loopBody689_23 loopBody689_1

def loopBody689_25 : HolLoopProg 64 :=
.mark loopBody689_24

def loopBody689_26 : HolLoopProg 64 :=
.seq loopBody689_19 loopBody689_25

def loopBody689_27 : HolLoopProg 64 :=
.mark loopBody689_26

def loopBody689_28 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_27

def loopBody689_29 : HolLoopProg 64 :=
.mark loopBody689_28

def loopBody689_30 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_29

def loopBody689_31 : HolLoopProg 64 :=
.mark loopBody689_30

def loopBody689_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody689_33 : HolLoopProg 64 :=
.mark loopBody689_32

def loopBody689_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody689_35 : HolLoopProg 64 :=
.mark loopBody689_34

def loopBody689_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 576#64)

def loopBody689_37 : HolLoopProg 64 :=
.mark loopBody689_36

def loopBody689_38 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 79) ([4, 5, 6]) (some (4, loopBody689_21, loopBody689_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody689_39 : HolLoopProg 64 :=
.mark loopBody689_38

def loopBody689_40 : HolLoopProg 64 :=
.seq loopBody689_39 loopBody689_1

def loopBody689_41 : HolLoopProg 64 :=
.mark loopBody689_40

def loopBody689_42 : HolLoopProg 64 :=
.seq loopBody689_37 loopBody689_41

def loopBody689_43 : HolLoopProg 64 :=
.mark loopBody689_42

def loopBody689_44 : HolLoopProg 64 :=
.seq loopBody689_35 loopBody689_43

def loopBody689_45 : HolLoopProg 64 :=
.mark loopBody689_44

def loopBody689_46 : HolLoopProg 64 :=
.seq loopBody689_33 loopBody689_45

def loopBody689_47 : HolLoopProg 64 :=
.mark loopBody689_46

def loopBody689_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody689_49 : HolLoopProg 64 :=
.mark loopBody689_48

def loopBody689_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody689_51 : HolLoopProg 64 :=
.mark loopBody689_50

def loopBody689_52 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 70) ([5]) (some (5, loopBody689_51, loopBody689_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody689_53 : HolLoopProg 64 :=
.mark loopBody689_52

def loopBody689_54 : HolLoopProg 64 :=
.seq loopBody689_53 loopBody689_1

def loopBody689_55 : HolLoopProg 64 :=
.mark loopBody689_54

def loopBody689_56 : HolLoopProg 64 :=
.seq loopBody689_49 loopBody689_55

def loopBody689_57 : HolLoopProg 64 :=
.mark loopBody689_56

def loopBody689_58 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_57

def loopBody689_59 : HolLoopProg 64 :=
.mark loopBody689_58

def loopBody689_60 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_59

def loopBody689_61 : HolLoopProg 64 :=
.mark loopBody689_60

def loopBody689_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody689_63 : HolLoopProg 64 :=
.mark loopBody689_62

def loopBody689_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody689_65 : HolLoopProg 64 :=
.mark loopBody689_64

def loopBody689_66 : HolLoopProg 64 :=
.seq loopBody689_65 loopBody689_1

def loopBody689_67 : HolLoopProg 64 :=
.mark loopBody689_66

def loopBody689_68 : HolLoopProg 64 :=
.seq loopBody689_63 loopBody689_67

def loopBody689_69 : HolLoopProg 64 :=
.mark loopBody689_68

def loopBody689_70 : HolLoopProg 64 :=
.seq loopBody689_61 loopBody689_69

def loopBody689_71 : HolLoopProg 64 :=
.mark loopBody689_70

def loopBody689_72 : HolLoopProg 64 :=
.seq loopBody689_47 loopBody689_71

def loopBody689_73 : HolLoopProg 64 :=
.mark loopBody689_72

def loopBody689_74 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_73

def loopBody689_75 : HolLoopProg 64 :=
.mark loopBody689_74

def loopBody689_76 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_75

def loopBody689_77 : HolLoopProg 64 :=
.mark loopBody689_76

def loopBody689_78 : HolLoopProg 64 :=
.seq loopBody689_31 loopBody689_77

def loopBody689_79 : HolLoopProg 64 :=
.mark loopBody689_78

def loopBody689_80 : HolLoopProg 64 :=
.seq loopBody689_17 loopBody689_79

def loopBody689_81 : HolLoopProg 64 :=
.mark loopBody689_80

def loopBody689_82 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_81

def loopBody689_83 : HolLoopProg 64 :=
.mark loopBody689_82

def loopBody689_84 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_83

def loopBody689_85 : HolLoopProg 64 :=
.mark loopBody689_84

def loopBody689_86 : HolLoopProg 64 :=
.seq loopBody689_7 loopBody689_85

def loopBody689_87 : HolLoopProg 64 :=
.mark loopBody689_86

def loopBody689_88 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_87

def loopBody689_89 : HolLoopProg 64 :=
.mark loopBody689_88

def loopBody689_90 : HolLoopProg 64 :=
.seq loopBody689_1 loopBody689_89

def loopBody689_91 : HolLoopProg 64 :=
.mark loopBody689_90

def output689 : Nat × List Nat × HolLoopProg 64 :=
  (753, [0], loopBody689_91)
end InitECandidate.Proofs.FrontendStages.Loop
