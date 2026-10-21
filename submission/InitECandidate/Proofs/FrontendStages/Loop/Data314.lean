import InitECandidate.Proofs.FrontendStages.Loop.Translate298
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody314_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody314_1 : HolLoopProg 64 :=
.mark loopBody314_0

def loopBody314_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody314_3 : HolLoopProg 64 :=
.mark loopBody314_2

def loopBody314_4 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (4, loopBody314_3, loopBody314_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody314_5 : HolLoopProg 64 :=
.mark loopBody314_4

def loopBody314_6 : HolLoopProg 64 :=
.seq loopBody314_5 loopBody314_1

def loopBody314_7 : HolLoopProg 64 :=
.mark loopBody314_6

def loopBody314_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 72#64)

def loopBody314_9 : HolLoopProg 64 :=
.mark loopBody314_8

def loopBody314_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody314_11 : HolLoopProg 64 :=
.mark loopBody314_10

def loopBody314_12 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody314_11, loopBody314_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody314_13 : HolLoopProg 64 :=
.mark loopBody314_12

def loopBody314_14 : HolLoopProg 64 :=
.seq loopBody314_13 loopBody314_1

def loopBody314_15 : HolLoopProg 64 :=
.mark loopBody314_14

def loopBody314_16 : HolLoopProg 64 :=
.seq loopBody314_9 loopBody314_15

def loopBody314_17 : HolLoopProg 64 :=
.mark loopBody314_16

def loopBody314_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody314_19 : HolLoopProg 64 :=
.mark loopBody314_18

def loopBody314_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 4#64)

def loopBody314_21 : HolLoopProg 64 :=
.mark loopBody314_20

def loopBody314_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 5 6

def loopBody314_23 : HolLoopProg 64 :=
.mark loopBody314_22

def loopBody314_24 : HolLoopProg 64 :=
.seq loopBody314_23 loopBody314_1

def loopBody314_25 : HolLoopProg 64 :=
.mark loopBody314_24

def loopBody314_26 : HolLoopProg 64 :=
.seq loopBody314_21 loopBody314_25

def loopBody314_27 : HolLoopProg 64 :=
.mark loopBody314_26

def loopBody314_28 : HolLoopProg 64 :=
.seq loopBody314_19 loopBody314_27

def loopBody314_29 : HolLoopProg 64 :=
.mark loopBody314_28

def loopBody314_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody314_31 : HolLoopProg 64 :=
.mark loopBody314_30

def loopBody314_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody314_33 : HolLoopProg 64 :=
.mark loopBody314_32

def loopBody314_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody314_35 : HolLoopProg 64 :=
.mark loopBody314_34

def loopBody314_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody314_37 : HolLoopProg 64 :=
.mark loopBody314_36

def loopBody314_38 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 375) ([6, 7, 8]) (some (6, loopBody314_37, loopBody314_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody314_39 : HolLoopProg 64 :=
.mark loopBody314_38

def loopBody314_40 : HolLoopProg 64 :=
.seq loopBody314_39 loopBody314_1

def loopBody314_41 : HolLoopProg 64 :=
.mark loopBody314_40

def loopBody314_42 : HolLoopProg 64 :=
.seq loopBody314_35 loopBody314_41

def loopBody314_43 : HolLoopProg 64 :=
.mark loopBody314_42

def loopBody314_44 : HolLoopProg 64 :=
.seq loopBody314_33 loopBody314_43

def loopBody314_45 : HolLoopProg 64 :=
.mark loopBody314_44

def loopBody314_46 : HolLoopProg 64 :=
.seq loopBody314_31 loopBody314_45

def loopBody314_47 : HolLoopProg 64 :=
.mark loopBody314_46

def loopBody314_48 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_47

def loopBody314_49 : HolLoopProg 64 :=
.mark loopBody314_48

def loopBody314_50 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_49

def loopBody314_51 : HolLoopProg 64 :=
.mark loopBody314_50

def loopBody314_52 : HolLoopProg 64 :=
.seq loopBody314_29 loopBody314_51

def loopBody314_53 : HolLoopProg 64 :=
.mark loopBody314_52

def loopBody314_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody314_55 : HolLoopProg 64 :=
.mark loopBody314_54

def loopBody314_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody314_57 : HolLoopProg 64 :=
.mark loopBody314_56

def loopBody314_58 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 376) ([6, 7]) (some (6, loopBody314_37, loopBody314_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody314_59 : HolLoopProg 64 :=
.mark loopBody314_58

def loopBody314_60 : HolLoopProg 64 :=
.seq loopBody314_59 loopBody314_1

def loopBody314_61 : HolLoopProg 64 :=
.mark loopBody314_60

def loopBody314_62 : HolLoopProg 64 :=
.seq loopBody314_57 loopBody314_61

def loopBody314_63 : HolLoopProg 64 :=
.mark loopBody314_62

def loopBody314_64 : HolLoopProg 64 :=
.seq loopBody314_55 loopBody314_63

def loopBody314_65 : HolLoopProg 64 :=
.mark loopBody314_64

def loopBody314_66 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_65

def loopBody314_67 : HolLoopProg 64 :=
.mark loopBody314_66

def loopBody314_68 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_67

def loopBody314_69 : HolLoopProg 64 :=
.mark loopBody314_68

def loopBody314_70 : HolLoopProg 64 :=
.seq loopBody314_53 loopBody314_69

def loopBody314_71 : HolLoopProg 64 :=
.mark loopBody314_70

def loopBody314_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody314_73 : HolLoopProg 64 :=
.mark loopBody314_72

def loopBody314_74 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 70) ([6]) (some (6, loopBody314_37, loopBody314_1, (Flapjack.Spt.ln)))

def loopBody314_75 : HolLoopProg 64 :=
.mark loopBody314_74

def loopBody314_76 : HolLoopProg 64 :=
.seq loopBody314_75 loopBody314_1

def loopBody314_77 : HolLoopProg 64 :=
.mark loopBody314_76

def loopBody314_78 : HolLoopProg 64 :=
.seq loopBody314_73 loopBody314_77

def loopBody314_79 : HolLoopProg 64 :=
.mark loopBody314_78

def loopBody314_80 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_79

def loopBody314_81 : HolLoopProg 64 :=
.mark loopBody314_80

def loopBody314_82 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_81

def loopBody314_83 : HolLoopProg 64 :=
.mark loopBody314_82

def loopBody314_84 : HolLoopProg 64 :=
.seq loopBody314_71 loopBody314_83

def loopBody314_85 : HolLoopProg 64 :=
.mark loopBody314_84

def loopBody314_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody314_87 : HolLoopProg 64 :=
.mark loopBody314_86

def loopBody314_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody314_89 : HolLoopProg 64 :=
.mark loopBody314_88

def loopBody314_90 : HolLoopProg 64 :=
.seq loopBody314_89 loopBody314_1

def loopBody314_91 : HolLoopProg 64 :=
.mark loopBody314_90

def loopBody314_92 : HolLoopProg 64 :=
.seq loopBody314_87 loopBody314_91

def loopBody314_93 : HolLoopProg 64 :=
.mark loopBody314_92

def loopBody314_94 : HolLoopProg 64 :=
.seq loopBody314_85 loopBody314_93

def loopBody314_95 : HolLoopProg 64 :=
.mark loopBody314_94

def loopBody314_96 : HolLoopProg 64 :=
.seq loopBody314_17 loopBody314_95

def loopBody314_97 : HolLoopProg 64 :=
.mark loopBody314_96

def loopBody314_98 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_97

def loopBody314_99 : HolLoopProg 64 :=
.mark loopBody314_98

def loopBody314_100 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_99

def loopBody314_101 : HolLoopProg 64 :=
.mark loopBody314_100

def loopBody314_102 : HolLoopProg 64 :=
.seq loopBody314_7 loopBody314_101

def loopBody314_103 : HolLoopProg 64 :=
.mark loopBody314_102

def loopBody314_104 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_103

def loopBody314_105 : HolLoopProg 64 :=
.mark loopBody314_104

def loopBody314_106 : HolLoopProg 64 :=
.seq loopBody314_1 loopBody314_105

def loopBody314_107 : HolLoopProg 64 :=
.mark loopBody314_106

def output314 : Nat × List Nat × HolLoopProg 64 :=
  (378, [0, 1, 2], loopBody314_107)
end InitECandidate.Proofs.FrontendStages.Loop
