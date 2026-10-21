import InitECandidate.Proofs.FrontendStages.Loop.Translate728
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody744_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody744_1 : HolLoopProg 64 :=
.mark loopBody744_0

def loopBody744_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody744_3 : HolLoopProg 64 :=
.mark loopBody744_2

def loopBody744_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody744_3, loopBody744_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody744_5 : HolLoopProg 64 :=
.mark loopBody744_4

def loopBody744_6 : HolLoopProg 64 :=
.seq loopBody744_5 loopBody744_1

def loopBody744_7 : HolLoopProg 64 :=
.mark loopBody744_6

def loopBody744_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 288#64)

def loopBody744_9 : HolLoopProg 64 :=
.mark loopBody744_8

def loopBody744_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody744_11 : HolLoopProg 64 :=
.mark loopBody744_10

def loopBody744_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody744_11, loopBody744_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody744_13 : HolLoopProg 64 :=
.mark loopBody744_12

def loopBody744_14 : HolLoopProg 64 :=
.seq loopBody744_13 loopBody744_1

def loopBody744_15 : HolLoopProg 64 :=
.mark loopBody744_14

def loopBody744_16 : HolLoopProg 64 :=
.seq loopBody744_9 loopBody744_15

def loopBody744_17 : HolLoopProg 64 :=
.mark loopBody744_16

def loopBody744_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 288#64)

def loopBody744_19 : HolLoopProg 64 :=
.mark loopBody744_18

def loopBody744_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody744_21 : HolLoopProg 64 :=
.mark loopBody744_20

def loopBody744_22 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody744_21, loopBody744_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody744_23 : HolLoopProg 64 :=
.mark loopBody744_22

def loopBody744_24 : HolLoopProg 64 :=
.seq loopBody744_23 loopBody744_1

def loopBody744_25 : HolLoopProg 64 :=
.mark loopBody744_24

def loopBody744_26 : HolLoopProg 64 :=
.seq loopBody744_19 loopBody744_25

def loopBody744_27 : HolLoopProg 64 :=
.mark loopBody744_26

def loopBody744_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody744_29 : HolLoopProg 64 :=
.mark loopBody744_28

def loopBody744_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody744_31 : HolLoopProg 64 :=
.mark loopBody744_30

def loopBody744_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody744_33 : HolLoopProg 64 :=
.mark loopBody744_32

def loopBody744_34 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 783) ([6, 7]) (some (6, loopBody744_33, loopBody744_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody744_35 : HolLoopProg 64 :=
.mark loopBody744_34

def loopBody744_36 : HolLoopProg 64 :=
.seq loopBody744_35 loopBody744_1

def loopBody744_37 : HolLoopProg 64 :=
.mark loopBody744_36

def loopBody744_38 : HolLoopProg 64 :=
.seq loopBody744_31 loopBody744_37

def loopBody744_39 : HolLoopProg 64 :=
.mark loopBody744_38

def loopBody744_40 : HolLoopProg 64 :=
.seq loopBody744_29 loopBody744_39

def loopBody744_41 : HolLoopProg 64 :=
.mark loopBody744_40

def loopBody744_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody744_43 : HolLoopProg 64 :=
.mark loopBody744_42

def loopBody744_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody744_45 : HolLoopProg 64 :=
.mark loopBody744_44

def loopBody744_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody744_47 : HolLoopProg 64 :=
.mark loopBody744_46

def loopBody744_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody744_49 : HolLoopProg 64 :=
.mark loopBody744_48

def loopBody744_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody744_47 loopBody744_49 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody744_51 : HolLoopProg 64 :=
.mark loopBody744_50

def loopBody744_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody744_53 : HolLoopProg 64 :=
.mark loopBody744_52

def loopBody744_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 256#64])

def loopBody744_55 : HolLoopProg 64 :=
.mark loopBody744_54

def loopBody744_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody744_57 : HolLoopProg 64 :=
.mark loopBody744_56

def loopBody744_58 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 783) ([6, 7]) (some (6, loopBody744_33, loopBody744_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody744_59 : HolLoopProg 64 :=
.mark loopBody744_58

def loopBody744_60 : HolLoopProg 64 :=
.seq loopBody744_59 loopBody744_1

def loopBody744_61 : HolLoopProg 64 :=
.mark loopBody744_60

def loopBody744_62 : HolLoopProg 64 :=
.seq loopBody744_57 loopBody744_61

def loopBody744_63 : HolLoopProg 64 :=
.mark loopBody744_62

def loopBody744_64 : HolLoopProg 64 :=
.seq loopBody744_55 loopBody744_63

def loopBody744_65 : HolLoopProg 64 :=
.mark loopBody744_64

def loopBody744_66 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody744_65 loopBody744_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody744_67 : HolLoopProg 64 :=
.mark loopBody744_66

def loopBody744_68 : HolLoopProg 64 :=
.seq loopBody744_67 loopBody744_1

def loopBody744_69 : HolLoopProg 64 :=
.mark loopBody744_68

def loopBody744_70 : HolLoopProg 64 :=
.seq loopBody744_53 loopBody744_69

def loopBody744_71 : HolLoopProg 64 :=
.mark loopBody744_70

def loopBody744_72 : HolLoopProg 64 :=
.seq loopBody744_51 loopBody744_71

def loopBody744_73 : HolLoopProg 64 :=
.mark loopBody744_72

def loopBody744_74 : HolLoopProg 64 :=
.seq loopBody744_45 loopBody744_73

def loopBody744_75 : HolLoopProg 64 :=
.mark loopBody744_74

def loopBody744_76 : HolLoopProg 64 :=
.seq loopBody744_43 loopBody744_75

def loopBody744_77 : HolLoopProg 64 :=
.mark loopBody744_76

def loopBody744_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody744_79 : HolLoopProg 64 :=
.mark loopBody744_78

def loopBody744_80 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody744_47 loopBody744_49 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody744_81 : HolLoopProg 64 :=
.mark loopBody744_80

def loopBody744_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody744_83 : HolLoopProg 64 :=
.mark loopBody744_82

def loopBody744_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody744_85 : HolLoopProg 64 :=
.mark loopBody744_84

def loopBody744_86 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 70) ([7]) (some (7, loopBody744_85, loopBody744_1, (Flapjack.Spt.ln)))

def loopBody744_87 : HolLoopProg 64 :=
.mark loopBody744_86

def loopBody744_88 : HolLoopProg 64 :=
.seq loopBody744_87 loopBody744_1

def loopBody744_89 : HolLoopProg 64 :=
.mark loopBody744_88

def loopBody744_90 : HolLoopProg 64 :=
.seq loopBody744_83 loopBody744_89

def loopBody744_91 : HolLoopProg 64 :=
.mark loopBody744_90

def loopBody744_92 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_91

def loopBody744_93 : HolLoopProg 64 :=
.mark loopBody744_92

def loopBody744_94 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_93

def loopBody744_95 : HolLoopProg 64 :=
.mark loopBody744_94

def loopBody744_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody744_97 : HolLoopProg 64 :=
.mark loopBody744_96

def loopBody744_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody744_99 : HolLoopProg 64 :=
.mark loopBody744_98

def loopBody744_100 : HolLoopProg 64 :=
.seq loopBody744_99 loopBody744_1

def loopBody744_101 : HolLoopProg 64 :=
.mark loopBody744_100

def loopBody744_102 : HolLoopProg 64 :=
.seq loopBody744_97 loopBody744_101

def loopBody744_103 : HolLoopProg 64 :=
.mark loopBody744_102

def loopBody744_104 : HolLoopProg 64 :=
.seq loopBody744_95 loopBody744_103

def loopBody744_105 : HolLoopProg 64 :=
.mark loopBody744_104

def loopBody744_106 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody744_105 loopBody744_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody744_107 : HolLoopProg 64 :=
.mark loopBody744_106

def loopBody744_108 : HolLoopProg 64 :=
.seq loopBody744_107 loopBody744_1

def loopBody744_109 : HolLoopProg 64 :=
.mark loopBody744_108

def loopBody744_110 : HolLoopProg 64 :=
.seq loopBody744_53 loopBody744_109

def loopBody744_111 : HolLoopProg 64 :=
.mark loopBody744_110

def loopBody744_112 : HolLoopProg 64 :=
.seq loopBody744_81 loopBody744_111

def loopBody744_113 : HolLoopProg 64 :=
.mark loopBody744_112

def loopBody744_114 : HolLoopProg 64 :=
.seq loopBody744_79 loopBody744_113

def loopBody744_115 : HolLoopProg 64 :=
.mark loopBody744_114

def loopBody744_116 : HolLoopProg 64 :=
.seq loopBody744_43 loopBody744_115

def loopBody744_117 : HolLoopProg 64 :=
.mark loopBody744_116

def loopBody744_118 : HolLoopProg 64 :=
.seq loopBody744_77 loopBody744_117

def loopBody744_119 : HolLoopProg 64 :=
.mark loopBody744_118

def loopBody744_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody744_121 : HolLoopProg 64 :=
.mark loopBody744_120

def loopBody744_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody744_123 : HolLoopProg 64 :=
.mark loopBody744_122

def loopBody744_124 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 779) ([7, 8, 9]) (some (7, loopBody744_85, loopBody744_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody744_125 : HolLoopProg 64 :=
.mark loopBody744_124

def loopBody744_126 : HolLoopProg 64 :=
.seq loopBody744_125 loopBody744_1

def loopBody744_127 : HolLoopProg 64 :=
.mark loopBody744_126

def loopBody744_128 : HolLoopProg 64 :=
.seq loopBody744_123 loopBody744_127

def loopBody744_129 : HolLoopProg 64 :=
.mark loopBody744_128

def loopBody744_130 : HolLoopProg 64 :=
.seq loopBody744_121 loopBody744_129

def loopBody744_131 : HolLoopProg 64 :=
.mark loopBody744_130

def loopBody744_132 : HolLoopProg 64 :=
.seq loopBody744_31 loopBody744_131

def loopBody744_133 : HolLoopProg 64 :=
.mark loopBody744_132

def loopBody744_134 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_133

def loopBody744_135 : HolLoopProg 64 :=
.mark loopBody744_134

def loopBody744_136 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_135

def loopBody744_137 : HolLoopProg 64 :=
.mark loopBody744_136

def loopBody744_138 : HolLoopProg 64 :=
.seq loopBody744_119 loopBody744_137

def loopBody744_139 : HolLoopProg 64 :=
.mark loopBody744_138

def loopBody744_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody744_141 : HolLoopProg 64 :=
.mark loopBody744_140

def loopBody744_142 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 784) ([7, 8]) (some (7, loopBody744_85, loopBody744_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody744_143 : HolLoopProg 64 :=
.mark loopBody744_142

def loopBody744_144 : HolLoopProg 64 :=
.seq loopBody744_143 loopBody744_1

def loopBody744_145 : HolLoopProg 64 :=
.mark loopBody744_144

def loopBody744_146 : HolLoopProg 64 :=
.seq loopBody744_141 loopBody744_145

def loopBody744_147 : HolLoopProg 64 :=
.mark loopBody744_146

def loopBody744_148 : HolLoopProg 64 :=
.seq loopBody744_31 loopBody744_147

def loopBody744_149 : HolLoopProg 64 :=
.mark loopBody744_148

def loopBody744_150 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_149

def loopBody744_151 : HolLoopProg 64 :=
.mark loopBody744_150

def loopBody744_152 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_151

def loopBody744_153 : HolLoopProg 64 :=
.mark loopBody744_152

def loopBody744_154 : HolLoopProg 64 :=
.seq loopBody744_139 loopBody744_153

def loopBody744_155 : HolLoopProg 64 :=
.mark loopBody744_154

def loopBody744_156 : HolLoopProg 64 :=
.seq loopBody744_155 loopBody744_95

def loopBody744_157 : HolLoopProg 64 :=
.mark loopBody744_156

def loopBody744_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody744_159 : HolLoopProg 64 :=
.mark loopBody744_158

def loopBody744_160 : HolLoopProg 64 :=
.seq loopBody744_159 loopBody744_101

def loopBody744_161 : HolLoopProg 64 :=
.mark loopBody744_160

def loopBody744_162 : HolLoopProg 64 :=
.seq loopBody744_157 loopBody744_161

def loopBody744_163 : HolLoopProg 64 :=
.mark loopBody744_162

def loopBody744_164 : HolLoopProg 64 :=
.seq loopBody744_41 loopBody744_163

def loopBody744_165 : HolLoopProg 64 :=
.mark loopBody744_164

def loopBody744_166 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_165

def loopBody744_167 : HolLoopProg 64 :=
.mark loopBody744_166

def loopBody744_168 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_167

def loopBody744_169 : HolLoopProg 64 :=
.mark loopBody744_168

def loopBody744_170 : HolLoopProg 64 :=
.seq loopBody744_27 loopBody744_169

def loopBody744_171 : HolLoopProg 64 :=
.mark loopBody744_170

def loopBody744_172 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_171

def loopBody744_173 : HolLoopProg 64 :=
.mark loopBody744_172

def loopBody744_174 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_173

def loopBody744_175 : HolLoopProg 64 :=
.mark loopBody744_174

def loopBody744_176 : HolLoopProg 64 :=
.seq loopBody744_17 loopBody744_175

def loopBody744_177 : HolLoopProg 64 :=
.mark loopBody744_176

def loopBody744_178 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_177

def loopBody744_179 : HolLoopProg 64 :=
.mark loopBody744_178

def loopBody744_180 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_179

def loopBody744_181 : HolLoopProg 64 :=
.mark loopBody744_180

def loopBody744_182 : HolLoopProg 64 :=
.seq loopBody744_7 loopBody744_181

def loopBody744_183 : HolLoopProg 64 :=
.mark loopBody744_182

def loopBody744_184 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_183

def loopBody744_185 : HolLoopProg 64 :=
.mark loopBody744_184

def loopBody744_186 : HolLoopProg 64 :=
.seq loopBody744_1 loopBody744_185

def loopBody744_187 : HolLoopProg 64 :=
.mark loopBody744_186

def output744 : Nat × List Nat × HolLoopProg 64 :=
  (808, [0, 1], loopBody744_187)
end InitECandidate.Proofs.FrontendStages.Loop
