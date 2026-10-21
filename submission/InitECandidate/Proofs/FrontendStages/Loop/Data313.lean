import InitECandidate.Proofs.FrontendStages.Loop.Translate297
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody313_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody313_1 : HolLoopProg 64 :=
.mark loopBody313_0

def loopBody313_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody313_3 : HolLoopProg 64 :=
.mark loopBody313_2

def loopBody313_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody313_5 : HolLoopProg 64 :=
.mark loopBody313_4

def loopBody313_6 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 373) ([4]) (some (4, loopBody313_5, loopBody313_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody313_7 : HolLoopProg 64 :=
.mark loopBody313_6

def loopBody313_8 : HolLoopProg 64 :=
.seq loopBody313_7 loopBody313_1

def loopBody313_9 : HolLoopProg 64 :=
.mark loopBody313_8

def loopBody313_10 : HolLoopProg 64 :=
.seq loopBody313_3 loopBody313_9

def loopBody313_11 : HolLoopProg 64 :=
.mark loopBody313_10

def loopBody313_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody313_13 : HolLoopProg 64 :=
.mark loopBody313_12

def loopBody313_14 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 69) ([]) (some (5, loopBody313_13, loopBody313_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody313_15 : HolLoopProg 64 :=
.mark loopBody313_14

def loopBody313_16 : HolLoopProg 64 :=
.seq loopBody313_15 loopBody313_1

def loopBody313_17 : HolLoopProg 64 :=
.mark loopBody313_16

def loopBody313_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 72#64)

def loopBody313_19 : HolLoopProg 64 :=
.mark loopBody313_18

def loopBody313_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody313_21 : HolLoopProg 64 :=
.mark loopBody313_20

def loopBody313_22 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([6]) (some (6, loopBody313_21, loopBody313_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody313_23 : HolLoopProg 64 :=
.mark loopBody313_22

def loopBody313_24 : HolLoopProg 64 :=
.seq loopBody313_23 loopBody313_1

def loopBody313_25 : HolLoopProg 64 :=
.mark loopBody313_24

def loopBody313_26 : HolLoopProg 64 :=
.seq loopBody313_19 loopBody313_25

def loopBody313_27 : HolLoopProg 64 :=
.mark loopBody313_26

def loopBody313_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody313_29 : HolLoopProg 64 :=
.mark loopBody313_28

def loopBody313_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 4#64)

def loopBody313_31 : HolLoopProg 64 :=
.mark loopBody313_30

def loopBody313_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 6 7

def loopBody313_33 : HolLoopProg 64 :=
.mark loopBody313_32

def loopBody313_34 : HolLoopProg 64 :=
.seq loopBody313_33 loopBody313_1

def loopBody313_35 : HolLoopProg 64 :=
.mark loopBody313_34

def loopBody313_36 : HolLoopProg 64 :=
.seq loopBody313_31 loopBody313_35

def loopBody313_37 : HolLoopProg 64 :=
.mark loopBody313_36

def loopBody313_38 : HolLoopProg 64 :=
.seq loopBody313_29 loopBody313_37

def loopBody313_39 : HolLoopProg 64 :=
.mark loopBody313_38

def loopBody313_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody313_41 : HolLoopProg 64 :=
.mark loopBody313_40

def loopBody313_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody313_43 : HolLoopProg 64 :=
.mark loopBody313_42

def loopBody313_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody313_45 : HolLoopProg 64 :=
.mark loopBody313_44

def loopBody313_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody313_47 : HolLoopProg 64 :=
.mark loopBody313_46

def loopBody313_48 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))) (some 375) ([7, 8, 9]) (some (7, loopBody313_47, loopBody313_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))

def loopBody313_49 : HolLoopProg 64 :=
.mark loopBody313_48

def loopBody313_50 : HolLoopProg 64 :=
.seq loopBody313_49 loopBody313_1

def loopBody313_51 : HolLoopProg 64 :=
.mark loopBody313_50

def loopBody313_52 : HolLoopProg 64 :=
.seq loopBody313_45 loopBody313_51

def loopBody313_53 : HolLoopProg 64 :=
.mark loopBody313_52

def loopBody313_54 : HolLoopProg 64 :=
.seq loopBody313_43 loopBody313_53

def loopBody313_55 : HolLoopProg 64 :=
.mark loopBody313_54

def loopBody313_56 : HolLoopProg 64 :=
.seq loopBody313_41 loopBody313_55

def loopBody313_57 : HolLoopProg 64 :=
.mark loopBody313_56

def loopBody313_58 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_57

def loopBody313_59 : HolLoopProg 64 :=
.mark loopBody313_58

def loopBody313_60 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_59

def loopBody313_61 : HolLoopProg 64 :=
.mark loopBody313_60

def loopBody313_62 : HolLoopProg 64 :=
.seq loopBody313_39 loopBody313_61

def loopBody313_63 : HolLoopProg 64 :=
.mark loopBody313_62

def loopBody313_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody313_65 : HolLoopProg 64 :=
.mark loopBody313_64

def loopBody313_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody313_67 : HolLoopProg 64 :=
.mark loopBody313_66

def loopBody313_68 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 376) ([7, 8]) (some (7, loopBody313_47, loopBody313_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody313_69 : HolLoopProg 64 :=
.mark loopBody313_68

def loopBody313_70 : HolLoopProg 64 :=
.seq loopBody313_69 loopBody313_1

def loopBody313_71 : HolLoopProg 64 :=
.mark loopBody313_70

def loopBody313_72 : HolLoopProg 64 :=
.seq loopBody313_67 loopBody313_71

def loopBody313_73 : HolLoopProg 64 :=
.mark loopBody313_72

def loopBody313_74 : HolLoopProg 64 :=
.seq loopBody313_65 loopBody313_73

def loopBody313_75 : HolLoopProg 64 :=
.mark loopBody313_74

def loopBody313_76 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_75

def loopBody313_77 : HolLoopProg 64 :=
.mark loopBody313_76

def loopBody313_78 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_77

def loopBody313_79 : HolLoopProg 64 :=
.mark loopBody313_78

def loopBody313_80 : HolLoopProg 64 :=
.seq loopBody313_63 loopBody313_79

def loopBody313_81 : HolLoopProg 64 :=
.mark loopBody313_80

def loopBody313_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody313_83 : HolLoopProg 64 :=
.mark loopBody313_82

def loopBody313_84 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 70) ([7]) (some (7, loopBody313_47, loopBody313_1, (Flapjack.Spt.ln)))

def loopBody313_85 : HolLoopProg 64 :=
.mark loopBody313_84

def loopBody313_86 : HolLoopProg 64 :=
.seq loopBody313_85 loopBody313_1

def loopBody313_87 : HolLoopProg 64 :=
.mark loopBody313_86

def loopBody313_88 : HolLoopProg 64 :=
.seq loopBody313_83 loopBody313_87

def loopBody313_89 : HolLoopProg 64 :=
.mark loopBody313_88

def loopBody313_90 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_89

def loopBody313_91 : HolLoopProg 64 :=
.mark loopBody313_90

def loopBody313_92 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_91

def loopBody313_93 : HolLoopProg 64 :=
.mark loopBody313_92

def loopBody313_94 : HolLoopProg 64 :=
.seq loopBody313_81 loopBody313_93

def loopBody313_95 : HolLoopProg 64 :=
.mark loopBody313_94

def loopBody313_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody313_97 : HolLoopProg 64 :=
.mark loopBody313_96

def loopBody313_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody313_99 : HolLoopProg 64 :=
.mark loopBody313_98

def loopBody313_100 : HolLoopProg 64 :=
.seq loopBody313_99 loopBody313_1

def loopBody313_101 : HolLoopProg 64 :=
.mark loopBody313_100

def loopBody313_102 : HolLoopProg 64 :=
.seq loopBody313_97 loopBody313_101

def loopBody313_103 : HolLoopProg 64 :=
.mark loopBody313_102

def loopBody313_104 : HolLoopProg 64 :=
.seq loopBody313_95 loopBody313_103

def loopBody313_105 : HolLoopProg 64 :=
.mark loopBody313_104

def loopBody313_106 : HolLoopProg 64 :=
.seq loopBody313_27 loopBody313_105

def loopBody313_107 : HolLoopProg 64 :=
.mark loopBody313_106

def loopBody313_108 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_107

def loopBody313_109 : HolLoopProg 64 :=
.mark loopBody313_108

def loopBody313_110 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_109

def loopBody313_111 : HolLoopProg 64 :=
.mark loopBody313_110

def loopBody313_112 : HolLoopProg 64 :=
.seq loopBody313_17 loopBody313_111

def loopBody313_113 : HolLoopProg 64 :=
.mark loopBody313_112

def loopBody313_114 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_113

def loopBody313_115 : HolLoopProg 64 :=
.mark loopBody313_114

def loopBody313_116 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_115

def loopBody313_117 : HolLoopProg 64 :=
.mark loopBody313_116

def loopBody313_118 : HolLoopProg 64 :=
.seq loopBody313_11 loopBody313_117

def loopBody313_119 : HolLoopProg 64 :=
.mark loopBody313_118

def loopBody313_120 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_119

def loopBody313_121 : HolLoopProg 64 :=
.mark loopBody313_120

def loopBody313_122 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_121

def loopBody313_123 : HolLoopProg 64 :=
.mark loopBody313_122

def loopBody313_124 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_123

def loopBody313_125 : HolLoopProg 64 :=
.mark loopBody313_124

def loopBody313_126 : HolLoopProg 64 :=
.seq loopBody313_1 loopBody313_125

def loopBody313_127 : HolLoopProg 64 :=
.mark loopBody313_126

def output313 : Nat × List Nat × HolLoopProg 64 :=
  (377, [0, 1], loopBody313_127)
end InitECandidate.Proofs.FrontendStages.Loop
