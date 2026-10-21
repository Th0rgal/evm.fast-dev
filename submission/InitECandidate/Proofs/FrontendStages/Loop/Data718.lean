import InitECandidate.Proofs.FrontendStages.Loop.Translate702
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody718_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody718_1 : HolLoopProg 64 :=
.mark loopBody718_0

def loopBody718_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody718_3 : HolLoopProg 64 :=
.mark loopBody718_2

def loopBody718_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody718_3, loopBody718_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody718_5 : HolLoopProg 64 :=
.mark loopBody718_4

def loopBody718_6 : HolLoopProg 64 :=
.seq loopBody718_5 loopBody718_1

def loopBody718_7 : HolLoopProg 64 :=
.mark loopBody718_6

def loopBody718_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 96#64)

def loopBody718_9 : HolLoopProg 64 :=
.mark loopBody718_8

def loopBody718_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody718_11 : HolLoopProg 64 :=
.mark loopBody718_10

def loopBody718_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody718_11, loopBody718_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody718_13 : HolLoopProg 64 :=
.mark loopBody718_12

def loopBody718_14 : HolLoopProg 64 :=
.seq loopBody718_13 loopBody718_1

def loopBody718_15 : HolLoopProg 64 :=
.mark loopBody718_14

def loopBody718_16 : HolLoopProg 64 :=
.seq loopBody718_9 loopBody718_15

def loopBody718_17 : HolLoopProg 64 :=
.mark loopBody718_16

def loopBody718_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 96#64)

def loopBody718_19 : HolLoopProg 64 :=
.mark loopBody718_18

def loopBody718_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody718_21 : HolLoopProg 64 :=
.mark loopBody718_20

def loopBody718_22 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody718_21, loopBody718_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody718_23 : HolLoopProg 64 :=
.mark loopBody718_22

def loopBody718_24 : HolLoopProg 64 :=
.seq loopBody718_23 loopBody718_1

def loopBody718_25 : HolLoopProg 64 :=
.mark loopBody718_24

def loopBody718_26 : HolLoopProg 64 :=
.seq loopBody718_19 loopBody718_25

def loopBody718_27 : HolLoopProg 64 :=
.mark loopBody718_26

def loopBody718_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody718_29 : HolLoopProg 64 :=
.mark loopBody718_28

def loopBody718_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody718_31 : HolLoopProg 64 :=
.mark loopBody718_30

def loopBody718_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody718_33 : HolLoopProg 64 :=
.mark loopBody718_32

def loopBody718_34 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 736) ([6, 7]) (some (6, loopBody718_33, loopBody718_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody718_35 : HolLoopProg 64 :=
.mark loopBody718_34

def loopBody718_36 : HolLoopProg 64 :=
.seq loopBody718_35 loopBody718_1

def loopBody718_37 : HolLoopProg 64 :=
.mark loopBody718_36

def loopBody718_38 : HolLoopProg 64 :=
.seq loopBody718_31 loopBody718_37

def loopBody718_39 : HolLoopProg 64 :=
.mark loopBody718_38

def loopBody718_40 : HolLoopProg 64 :=
.seq loopBody718_29 loopBody718_39

def loopBody718_41 : HolLoopProg 64 :=
.mark loopBody718_40

def loopBody718_42 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_41

def loopBody718_43 : HolLoopProg 64 :=
.mark loopBody718_42

def loopBody718_44 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_43

def loopBody718_45 : HolLoopProg 64 :=
.mark loopBody718_44

def loopBody718_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody718_47 : HolLoopProg 64 :=
.mark loopBody718_46

def loopBody718_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody718_49 : HolLoopProg 64 :=
.mark loopBody718_48

def loopBody718_50 : HolLoopProg 64 :=
.seq loopBody718_49 loopBody718_37

def loopBody718_51 : HolLoopProg 64 :=
.mark loopBody718_50

def loopBody718_52 : HolLoopProg 64 :=
.seq loopBody718_47 loopBody718_51

def loopBody718_53 : HolLoopProg 64 :=
.mark loopBody718_52

def loopBody718_54 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_53

def loopBody718_55 : HolLoopProg 64 :=
.mark loopBody718_54

def loopBody718_56 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_55

def loopBody718_57 : HolLoopProg 64 :=
.mark loopBody718_56

def loopBody718_58 : HolLoopProg 64 :=
.seq loopBody718_45 loopBody718_57

def loopBody718_59 : HolLoopProg 64 :=
.mark loopBody718_58

def loopBody718_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody718_61 : HolLoopProg 64 :=
.mark loopBody718_60

def loopBody718_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 0)

def loopBody718_63 : HolLoopProg 64 :=
.mark loopBody718_62

def loopBody718_64 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 735) ([6, 7, 8]) (some (6, loopBody718_33, loopBody718_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody718_65 : HolLoopProg 64 :=
.mark loopBody718_64

def loopBody718_66 : HolLoopProg 64 :=
.seq loopBody718_65 loopBody718_1

def loopBody718_67 : HolLoopProg 64 :=
.mark loopBody718_66

def loopBody718_68 : HolLoopProg 64 :=
.seq loopBody718_63 loopBody718_67

def loopBody718_69 : HolLoopProg 64 :=
.mark loopBody718_68

def loopBody718_70 : HolLoopProg 64 :=
.seq loopBody718_61 loopBody718_69

def loopBody718_71 : HolLoopProg 64 :=
.mark loopBody718_70

def loopBody718_72 : HolLoopProg 64 :=
.seq loopBody718_47 loopBody718_71

def loopBody718_73 : HolLoopProg 64 :=
.mark loopBody718_72

def loopBody718_74 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_73

def loopBody718_75 : HolLoopProg 64 :=
.mark loopBody718_74

def loopBody718_76 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_75

def loopBody718_77 : HolLoopProg 64 :=
.mark loopBody718_76

def loopBody718_78 : HolLoopProg 64 :=
.seq loopBody718_59 loopBody718_77

def loopBody718_79 : HolLoopProg 64 :=
.mark loopBody718_78

def loopBody718_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 288#64])

def loopBody718_81 : HolLoopProg 64 :=
.mark loopBody718_80

def loopBody718_82 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 730) ([6, 7, 8]) (some (6, loopBody718_33, loopBody718_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody718_83 : HolLoopProg 64 :=
.mark loopBody718_82

def loopBody718_84 : HolLoopProg 64 :=
.seq loopBody718_83 loopBody718_1

def loopBody718_85 : HolLoopProg 64 :=
.mark loopBody718_84

def loopBody718_86 : HolLoopProg 64 :=
.seq loopBody718_81 loopBody718_85

def loopBody718_87 : HolLoopProg 64 :=
.mark loopBody718_86

def loopBody718_88 : HolLoopProg 64 :=
.seq loopBody718_61 loopBody718_87

def loopBody718_89 : HolLoopProg 64 :=
.mark loopBody718_88

def loopBody718_90 : HolLoopProg 64 :=
.seq loopBody718_47 loopBody718_89

def loopBody718_91 : HolLoopProg 64 :=
.mark loopBody718_90

def loopBody718_92 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_91

def loopBody718_93 : HolLoopProg 64 :=
.mark loopBody718_92

def loopBody718_94 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_93

def loopBody718_95 : HolLoopProg 64 :=
.mark loopBody718_94

def loopBody718_96 : HolLoopProg 64 :=
.seq loopBody718_79 loopBody718_95

def loopBody718_97 : HolLoopProg 64 :=
.mark loopBody718_96

def loopBody718_98 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 729) ([6, 7]) (some (6, loopBody718_33, loopBody718_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody718_99 : HolLoopProg 64 :=
.mark loopBody718_98

def loopBody718_100 : HolLoopProg 64 :=
.seq loopBody718_99 loopBody718_1

def loopBody718_101 : HolLoopProg 64 :=
.mark loopBody718_100

def loopBody718_102 : HolLoopProg 64 :=
.seq loopBody718_61 loopBody718_101

def loopBody718_103 : HolLoopProg 64 :=
.mark loopBody718_102

def loopBody718_104 : HolLoopProg 64 :=
.seq loopBody718_29 loopBody718_103

def loopBody718_105 : HolLoopProg 64 :=
.mark loopBody718_104

def loopBody718_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody718_107 : HolLoopProg 64 :=
.mark loopBody718_106

def loopBody718_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody718_109 : HolLoopProg 64 :=
.mark loopBody718_108

def loopBody718_110 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 70) ([7]) (some (7, loopBody718_109, loopBody718_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody718_111 : HolLoopProg 64 :=
.mark loopBody718_110

def loopBody718_112 : HolLoopProg 64 :=
.seq loopBody718_111 loopBody718_1

def loopBody718_113 : HolLoopProg 64 :=
.mark loopBody718_112

def loopBody718_114 : HolLoopProg 64 :=
.seq loopBody718_107 loopBody718_113

def loopBody718_115 : HolLoopProg 64 :=
.mark loopBody718_114

def loopBody718_116 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_115

def loopBody718_117 : HolLoopProg 64 :=
.mark loopBody718_116

def loopBody718_118 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_117

def loopBody718_119 : HolLoopProg 64 :=
.mark loopBody718_118

def loopBody718_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody718_121 : HolLoopProg 64 :=
.mark loopBody718_120

def loopBody718_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody718_123 : HolLoopProg 64 :=
.mark loopBody718_122

def loopBody718_124 : HolLoopProg 64 :=
.seq loopBody718_123 loopBody718_1

def loopBody718_125 : HolLoopProg 64 :=
.mark loopBody718_124

def loopBody718_126 : HolLoopProg 64 :=
.seq loopBody718_121 loopBody718_125

def loopBody718_127 : HolLoopProg 64 :=
.mark loopBody718_126

def loopBody718_128 : HolLoopProg 64 :=
.seq loopBody718_119 loopBody718_127

def loopBody718_129 : HolLoopProg 64 :=
.mark loopBody718_128

def loopBody718_130 : HolLoopProg 64 :=
.seq loopBody718_105 loopBody718_129

def loopBody718_131 : HolLoopProg 64 :=
.mark loopBody718_130

def loopBody718_132 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_131

def loopBody718_133 : HolLoopProg 64 :=
.mark loopBody718_132

def loopBody718_134 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_133

def loopBody718_135 : HolLoopProg 64 :=
.mark loopBody718_134

def loopBody718_136 : HolLoopProg 64 :=
.seq loopBody718_97 loopBody718_135

def loopBody718_137 : HolLoopProg 64 :=
.mark loopBody718_136

def loopBody718_138 : HolLoopProg 64 :=
.seq loopBody718_27 loopBody718_137

def loopBody718_139 : HolLoopProg 64 :=
.mark loopBody718_138

def loopBody718_140 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_139

def loopBody718_141 : HolLoopProg 64 :=
.mark loopBody718_140

def loopBody718_142 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_141

def loopBody718_143 : HolLoopProg 64 :=
.mark loopBody718_142

def loopBody718_144 : HolLoopProg 64 :=
.seq loopBody718_17 loopBody718_143

def loopBody718_145 : HolLoopProg 64 :=
.mark loopBody718_144

def loopBody718_146 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_145

def loopBody718_147 : HolLoopProg 64 :=
.mark loopBody718_146

def loopBody718_148 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_147

def loopBody718_149 : HolLoopProg 64 :=
.mark loopBody718_148

def loopBody718_150 : HolLoopProg 64 :=
.seq loopBody718_7 loopBody718_149

def loopBody718_151 : HolLoopProg 64 :=
.mark loopBody718_150

def loopBody718_152 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_151

def loopBody718_153 : HolLoopProg 64 :=
.mark loopBody718_152

def loopBody718_154 : HolLoopProg 64 :=
.seq loopBody718_1 loopBody718_153

def loopBody718_155 : HolLoopProg 64 :=
.mark loopBody718_154

def output718 : Nat × List Nat × HolLoopProg 64 :=
  (782, [0, 1], loopBody718_155)
end InitECandidate.Proofs.FrontendStages.Loop
