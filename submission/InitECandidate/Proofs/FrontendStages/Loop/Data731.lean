import InitECandidate.Proofs.FrontendStages.Loop.Translate715
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody731_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody731_1 : HolLoopProg 64 :=
.mark loopBody731_0

def loopBody731_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody731_3 : HolLoopProg 64 :=
.mark loopBody731_2

def loopBody731_4 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 69) ([]) (some (8, loopBody731_3, loopBody731_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody731_5 : HolLoopProg 64 :=
.mark loopBody731_4

def loopBody731_6 : HolLoopProg 64 :=
.seq loopBody731_5 loopBody731_1

def loopBody731_7 : HolLoopProg 64 :=
.mark loopBody731_6

def loopBody731_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 144#64)

def loopBody731_9 : HolLoopProg 64 :=
.mark loopBody731_8

def loopBody731_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody731_11 : HolLoopProg 64 :=
.mark loopBody731_10

def loopBody731_12 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 68) ([9]) (some (9, loopBody731_11, loopBody731_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody731_13 : HolLoopProg 64 :=
.mark loopBody731_12

def loopBody731_14 : HolLoopProg 64 :=
.seq loopBody731_13 loopBody731_1

def loopBody731_15 : HolLoopProg 64 :=
.mark loopBody731_14

def loopBody731_16 : HolLoopProg 64 :=
.seq loopBody731_9 loopBody731_15

def loopBody731_17 : HolLoopProg 64 :=
.mark loopBody731_16

def loopBody731_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody731_19 : HolLoopProg 64 :=
.mark loopBody731_18

def loopBody731_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 1)

def loopBody731_21 : HolLoopProg 64 :=
.mark loopBody731_20

def loopBody731_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 2)

def loopBody731_23 : HolLoopProg 64 :=
.mark loopBody731_22

def loopBody731_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 3)

def loopBody731_25 : HolLoopProg 64 :=
.mark loopBody731_24

def loopBody731_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 4)

def loopBody731_27 : HolLoopProg 64 :=
.mark loopBody731_26

def loopBody731_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 5)

def loopBody731_29 : HolLoopProg 64 :=
.mark loopBody731_28

def loopBody731_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 6)

def loopBody731_31 : HolLoopProg 64 :=
.mark loopBody731_30

def loopBody731_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody731_33 : HolLoopProg 64 :=
.mark loopBody731_32

def loopBody731_34 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 792) ([10, 11, 12, 13, 14, 15, 16]) (some (10, loopBody731_33, loopBody731_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody731_35 : HolLoopProg 64 :=
.mark loopBody731_34

def loopBody731_36 : HolLoopProg 64 :=
.seq loopBody731_35 loopBody731_1

def loopBody731_37 : HolLoopProg 64 :=
.mark loopBody731_36

def loopBody731_38 : HolLoopProg 64 :=
.seq loopBody731_31 loopBody731_37

def loopBody731_39 : HolLoopProg 64 :=
.mark loopBody731_38

def loopBody731_40 : HolLoopProg 64 :=
.seq loopBody731_29 loopBody731_39

def loopBody731_41 : HolLoopProg 64 :=
.mark loopBody731_40

def loopBody731_42 : HolLoopProg 64 :=
.seq loopBody731_27 loopBody731_41

def loopBody731_43 : HolLoopProg 64 :=
.mark loopBody731_42

def loopBody731_44 : HolLoopProg 64 :=
.seq loopBody731_25 loopBody731_43

def loopBody731_45 : HolLoopProg 64 :=
.mark loopBody731_44

def loopBody731_46 : HolLoopProg 64 :=
.seq loopBody731_23 loopBody731_45

def loopBody731_47 : HolLoopProg 64 :=
.mark loopBody731_46

def loopBody731_48 : HolLoopProg 64 :=
.seq loopBody731_21 loopBody731_47

def loopBody731_49 : HolLoopProg 64 :=
.mark loopBody731_48

def loopBody731_50 : HolLoopProg 64 :=
.seq loopBody731_19 loopBody731_49

def loopBody731_51 : HolLoopProg 64 :=
.mark loopBody731_50

def loopBody731_52 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_51

def loopBody731_53 : HolLoopProg 64 :=
.mark loopBody731_52

def loopBody731_54 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_53

def loopBody731_55 : HolLoopProg 64 :=
.mark loopBody731_54

def loopBody731_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody731_57 : HolLoopProg 64 :=
.mark loopBody731_56

def loopBody731_58 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 794) ([10, 11]) (some (10, loopBody731_33, loopBody731_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody731_59 : HolLoopProg 64 :=
.mark loopBody731_58

def loopBody731_60 : HolLoopProg 64 :=
.seq loopBody731_59 loopBody731_1

def loopBody731_61 : HolLoopProg 64 :=
.mark loopBody731_60

def loopBody731_62 : HolLoopProg 64 :=
.seq loopBody731_57 loopBody731_61

def loopBody731_63 : HolLoopProg 64 :=
.mark loopBody731_62

def loopBody731_64 : HolLoopProg 64 :=
.seq loopBody731_19 loopBody731_63

def loopBody731_65 : HolLoopProg 64 :=
.mark loopBody731_64

def loopBody731_66 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_65

def loopBody731_67 : HolLoopProg 64 :=
.mark loopBody731_66

def loopBody731_68 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_67

def loopBody731_69 : HolLoopProg 64 :=
.mark loopBody731_68

def loopBody731_70 : HolLoopProg 64 :=
.seq loopBody731_55 loopBody731_69

def loopBody731_71 : HolLoopProg 64 :=
.mark loopBody731_70

def loopBody731_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 0)

def loopBody731_73 : HolLoopProg 64 :=
.mark loopBody731_72

def loopBody731_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 1624#64])

def loopBody731_75 : HolLoopProg 64 :=
.mark loopBody731_74

def loopBody731_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody731_77 : HolLoopProg 64 :=
.mark loopBody731_76

def loopBody731_78 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 768) ([10, 11, 12, 13]) (some (10, loopBody731_33, loopBody731_1, (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody731_79 : HolLoopProg 64 :=
.mark loopBody731_78

def loopBody731_80 : HolLoopProg 64 :=
.seq loopBody731_79 loopBody731_1

def loopBody731_81 : HolLoopProg 64 :=
.mark loopBody731_80

def loopBody731_82 : HolLoopProg 64 :=
.seq loopBody731_77 loopBody731_81

def loopBody731_83 : HolLoopProg 64 :=
.mark loopBody731_82

def loopBody731_84 : HolLoopProg 64 :=
.seq loopBody731_75 loopBody731_83

def loopBody731_85 : HolLoopProg 64 :=
.mark loopBody731_84

def loopBody731_86 : HolLoopProg 64 :=
.seq loopBody731_57 loopBody731_85

def loopBody731_87 : HolLoopProg 64 :=
.mark loopBody731_86

def loopBody731_88 : HolLoopProg 64 :=
.seq loopBody731_73 loopBody731_87

def loopBody731_89 : HolLoopProg 64 :=
.mark loopBody731_88

def loopBody731_90 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_89

def loopBody731_91 : HolLoopProg 64 :=
.mark loopBody731_90

def loopBody731_92 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_91

def loopBody731_93 : HolLoopProg 64 :=
.mark loopBody731_92

def loopBody731_94 : HolLoopProg 64 :=
.seq loopBody731_71 loopBody731_93

def loopBody731_95 : HolLoopProg 64 :=
.mark loopBody731_94

def loopBody731_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 7)

def loopBody731_97 : HolLoopProg 64 :=
.mark loopBody731_96

def loopBody731_98 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 70) ([10]) (some (10, loopBody731_33, loopBody731_1, (Flapjack.Spt.ln)))

def loopBody731_99 : HolLoopProg 64 :=
.mark loopBody731_98

def loopBody731_100 : HolLoopProg 64 :=
.seq loopBody731_99 loopBody731_1

def loopBody731_101 : HolLoopProg 64 :=
.mark loopBody731_100

def loopBody731_102 : HolLoopProg 64 :=
.seq loopBody731_97 loopBody731_101

def loopBody731_103 : HolLoopProg 64 :=
.mark loopBody731_102

def loopBody731_104 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_103

def loopBody731_105 : HolLoopProg 64 :=
.mark loopBody731_104

def loopBody731_106 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_105

def loopBody731_107 : HolLoopProg 64 :=
.mark loopBody731_106

def loopBody731_108 : HolLoopProg 64 :=
.seq loopBody731_95 loopBody731_107

def loopBody731_109 : HolLoopProg 64 :=
.mark loopBody731_108

def loopBody731_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody731_111 : HolLoopProg 64 :=
.mark loopBody731_110

def loopBody731_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9]

def loopBody731_113 : HolLoopProg 64 :=
.mark loopBody731_112

def loopBody731_114 : HolLoopProg 64 :=
.seq loopBody731_113 loopBody731_1

def loopBody731_115 : HolLoopProg 64 :=
.mark loopBody731_114

def loopBody731_116 : HolLoopProg 64 :=
.seq loopBody731_111 loopBody731_115

def loopBody731_117 : HolLoopProg 64 :=
.mark loopBody731_116

def loopBody731_118 : HolLoopProg 64 :=
.seq loopBody731_109 loopBody731_117

def loopBody731_119 : HolLoopProg 64 :=
.mark loopBody731_118

def loopBody731_120 : HolLoopProg 64 :=
.seq loopBody731_17 loopBody731_119

def loopBody731_121 : HolLoopProg 64 :=
.mark loopBody731_120

def loopBody731_122 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_121

def loopBody731_123 : HolLoopProg 64 :=
.mark loopBody731_122

def loopBody731_124 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_123

def loopBody731_125 : HolLoopProg 64 :=
.mark loopBody731_124

def loopBody731_126 : HolLoopProg 64 :=
.seq loopBody731_7 loopBody731_125

def loopBody731_127 : HolLoopProg 64 :=
.mark loopBody731_126

def loopBody731_128 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_127

def loopBody731_129 : HolLoopProg 64 :=
.mark loopBody731_128

def loopBody731_130 : HolLoopProg 64 :=
.seq loopBody731_1 loopBody731_129

def loopBody731_131 : HolLoopProg 64 :=
.mark loopBody731_130

def output731 : Nat × List Nat × HolLoopProg 64 :=
  (795, [0, 1, 2, 3, 4, 5, 6], loopBody731_131)
end InitECandidate.Proofs.FrontendStages.Loop
