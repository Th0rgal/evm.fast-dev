import InitECandidate.Proofs.FrontendStages.Loop.Translate296
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody312_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody312_1 : HolLoopProg 64 :=
.mark loopBody312_0

def loopBody312_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody312_3 : HolLoopProg 64 :=
.mark loopBody312_2

def loopBody312_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody312_3, loopBody312_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody312_5 : HolLoopProg 64 :=
.mark loopBody312_4

def loopBody312_6 : HolLoopProg 64 :=
.seq loopBody312_5 loopBody312_1

def loopBody312_7 : HolLoopProg 64 :=
.mark loopBody312_6

def loopBody312_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 32#64)

def loopBody312_9 : HolLoopProg 64 :=
.mark loopBody312_8

def loopBody312_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody312_11 : HolLoopProg 64 :=
.mark loopBody312_10

def loopBody312_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody312_11, loopBody312_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody312_13 : HolLoopProg 64 :=
.mark loopBody312_12

def loopBody312_14 : HolLoopProg 64 :=
.seq loopBody312_13 loopBody312_1

def loopBody312_15 : HolLoopProg 64 :=
.mark loopBody312_14

def loopBody312_16 : HolLoopProg 64 :=
.seq loopBody312_9 loopBody312_15

def loopBody312_17 : HolLoopProg 64 :=
.mark loopBody312_16

def loopBody312_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 1#64])

def loopBody312_19 : HolLoopProg 64 :=
.mark loopBody312_18

def loopBody312_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 64#64)

def loopBody312_21 : HolLoopProg 64 :=
.mark loopBody312_20

def loopBody312_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody312_23 : HolLoopProg 64 :=
.mark loopBody312_22

def loopBody312_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody312_25 : HolLoopProg 64 :=
.mark loopBody312_24

def loopBody312_26 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 158) ([5, 6, 7]) (some (5, loopBody312_25, loopBody312_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody312_27 : HolLoopProg 64 :=
.mark loopBody312_26

def loopBody312_28 : HolLoopProg 64 :=
.seq loopBody312_27 loopBody312_1

def loopBody312_29 : HolLoopProg 64 :=
.mark loopBody312_28

def loopBody312_30 : HolLoopProg 64 :=
.seq loopBody312_23 loopBody312_29

def loopBody312_31 : HolLoopProg 64 :=
.mark loopBody312_30

def loopBody312_32 : HolLoopProg 64 :=
.seq loopBody312_21 loopBody312_31

def loopBody312_33 : HolLoopProg 64 :=
.mark loopBody312_32

def loopBody312_34 : HolLoopProg 64 :=
.seq loopBody312_19 loopBody312_33

def loopBody312_35 : HolLoopProg 64 :=
.mark loopBody312_34

def loopBody312_36 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_35

def loopBody312_37 : HolLoopProg 64 :=
.mark loopBody312_36

def loopBody312_38 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_37

def loopBody312_39 : HolLoopProg 64 :=
.mark loopBody312_38

def loopBody312_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody312_41 : HolLoopProg 64 :=
.mark loopBody312_40

def loopBody312_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 12#64])

def loopBody312_43 : HolLoopProg 64 :=
.mark loopBody312_42

def loopBody312_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 20#64)

def loopBody312_45 : HolLoopProg 64 :=
.mark loopBody312_44

def loopBody312_46 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 77) ([5, 6, 7]) (some (5, loopBody312_25, loopBody312_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody312_47 : HolLoopProg 64 :=
.mark loopBody312_46

def loopBody312_48 : HolLoopProg 64 :=
.seq loopBody312_47 loopBody312_1

def loopBody312_49 : HolLoopProg 64 :=
.mark loopBody312_48

def loopBody312_50 : HolLoopProg 64 :=
.seq loopBody312_45 loopBody312_49

def loopBody312_51 : HolLoopProg 64 :=
.mark loopBody312_50

def loopBody312_52 : HolLoopProg 64 :=
.seq loopBody312_43 loopBody312_51

def loopBody312_53 : HolLoopProg 64 :=
.mark loopBody312_52

def loopBody312_54 : HolLoopProg 64 :=
.seq loopBody312_41 loopBody312_53

def loopBody312_55 : HolLoopProg 64 :=
.mark loopBody312_54

def loopBody312_56 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_55

def loopBody312_57 : HolLoopProg 64 :=
.mark loopBody312_56

def loopBody312_58 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_57

def loopBody312_59 : HolLoopProg 64 :=
.mark loopBody312_58

def loopBody312_60 : HolLoopProg 64 :=
.seq loopBody312_39 loopBody312_59

def loopBody312_61 : HolLoopProg 64 :=
.mark loopBody312_60

def loopBody312_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody312_63 : HolLoopProg 64 :=
.mark loopBody312_62

def loopBody312_64 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody312_25, loopBody312_1, (Flapjack.Spt.ln)))

def loopBody312_65 : HolLoopProg 64 :=
.mark loopBody312_64

def loopBody312_66 : HolLoopProg 64 :=
.seq loopBody312_65 loopBody312_1

def loopBody312_67 : HolLoopProg 64 :=
.mark loopBody312_66

def loopBody312_68 : HolLoopProg 64 :=
.seq loopBody312_63 loopBody312_67

def loopBody312_69 : HolLoopProg 64 :=
.mark loopBody312_68

def loopBody312_70 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_69

def loopBody312_71 : HolLoopProg 64 :=
.mark loopBody312_70

def loopBody312_72 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_71

def loopBody312_73 : HolLoopProg 64 :=
.mark loopBody312_72

def loopBody312_74 : HolLoopProg 64 :=
.seq loopBody312_61 loopBody312_73

def loopBody312_75 : HolLoopProg 64 :=
.mark loopBody312_74

def loopBody312_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody312_77 : HolLoopProg 64 :=
.mark loopBody312_76

def loopBody312_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody312_79 : HolLoopProg 64 :=
.mark loopBody312_78

def loopBody312_80 : HolLoopProg 64 :=
.seq loopBody312_79 loopBody312_1

def loopBody312_81 : HolLoopProg 64 :=
.mark loopBody312_80

def loopBody312_82 : HolLoopProg 64 :=
.seq loopBody312_77 loopBody312_81

def loopBody312_83 : HolLoopProg 64 :=
.mark loopBody312_82

def loopBody312_84 : HolLoopProg 64 :=
.seq loopBody312_75 loopBody312_83

def loopBody312_85 : HolLoopProg 64 :=
.mark loopBody312_84

def loopBody312_86 : HolLoopProg 64 :=
.seq loopBody312_17 loopBody312_85

def loopBody312_87 : HolLoopProg 64 :=
.mark loopBody312_86

def loopBody312_88 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_87

def loopBody312_89 : HolLoopProg 64 :=
.mark loopBody312_88

def loopBody312_90 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_89

def loopBody312_91 : HolLoopProg 64 :=
.mark loopBody312_90

def loopBody312_92 : HolLoopProg 64 :=
.seq loopBody312_7 loopBody312_91

def loopBody312_93 : HolLoopProg 64 :=
.mark loopBody312_92

def loopBody312_94 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_93

def loopBody312_95 : HolLoopProg 64 :=
.mark loopBody312_94

def loopBody312_96 : HolLoopProg 64 :=
.seq loopBody312_1 loopBody312_95

def loopBody312_97 : HolLoopProg 64 :=
.mark loopBody312_96

def output312 : Nat × List Nat × HolLoopProg 64 :=
  (376, [0, 1], loopBody312_97)
end InitECandidate.Proofs.FrontendStages.Loop
