import InitECandidate.Proofs.FrontendStages.Loop.Translate726
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody742_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody742_1 : HolLoopProg 64 :=
.mark loopBody742_0

def loopBody742_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody742_3 : HolLoopProg 64 :=
.mark loopBody742_2

def loopBody742_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody742_3, loopBody742_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody742_5 : HolLoopProg 64 :=
.mark loopBody742_4

def loopBody742_6 : HolLoopProg 64 :=
.seq loopBody742_5 loopBody742_1

def loopBody742_7 : HolLoopProg 64 :=
.mark loopBody742_6

def loopBody742_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 144#64)

def loopBody742_9 : HolLoopProg 64 :=
.mark loopBody742_8

def loopBody742_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody742_11 : HolLoopProg 64 :=
.mark loopBody742_10

def loopBody742_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody742_11, loopBody742_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody742_13 : HolLoopProg 64 :=
.mark loopBody742_12

def loopBody742_14 : HolLoopProg 64 :=
.seq loopBody742_13 loopBody742_1

def loopBody742_15 : HolLoopProg 64 :=
.mark loopBody742_14

def loopBody742_16 : HolLoopProg 64 :=
.seq loopBody742_9 loopBody742_15

def loopBody742_17 : HolLoopProg 64 :=
.mark loopBody742_16

def loopBody742_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 144#64)

def loopBody742_19 : HolLoopProg 64 :=
.mark loopBody742_18

def loopBody742_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody742_21 : HolLoopProg 64 :=
.mark loopBody742_20

def loopBody742_22 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody742_21, loopBody742_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody742_23 : HolLoopProg 64 :=
.mark loopBody742_22

def loopBody742_24 : HolLoopProg 64 :=
.seq loopBody742_23 loopBody742_1

def loopBody742_25 : HolLoopProg 64 :=
.mark loopBody742_24

def loopBody742_26 : HolLoopProg 64 :=
.seq loopBody742_19 loopBody742_25

def loopBody742_27 : HolLoopProg 64 :=
.mark loopBody742_26

def loopBody742_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody742_29 : HolLoopProg 64 :=
.mark loopBody742_28

def loopBody742_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody742_31 : HolLoopProg 64 :=
.mark loopBody742_30

def loopBody742_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody742_33 : HolLoopProg 64 :=
.mark loopBody742_32

def loopBody742_34 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 771) ([6, 7]) (some (6, loopBody742_33, loopBody742_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody742_35 : HolLoopProg 64 :=
.mark loopBody742_34

def loopBody742_36 : HolLoopProg 64 :=
.seq loopBody742_35 loopBody742_1

def loopBody742_37 : HolLoopProg 64 :=
.mark loopBody742_36

def loopBody742_38 : HolLoopProg 64 :=
.seq loopBody742_31 loopBody742_37

def loopBody742_39 : HolLoopProg 64 :=
.mark loopBody742_38

def loopBody742_40 : HolLoopProg 64 :=
.seq loopBody742_29 loopBody742_39

def loopBody742_41 : HolLoopProg 64 :=
.mark loopBody742_40

def loopBody742_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody742_43 : HolLoopProg 64 :=
.mark loopBody742_42

def loopBody742_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody742_45 : HolLoopProg 64 :=
.mark loopBody742_44

def loopBody742_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody742_47 : HolLoopProg 64 :=
.mark loopBody742_46

def loopBody742_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody742_49 : HolLoopProg 64 :=
.mark loopBody742_48

def loopBody742_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody742_47 loopBody742_49 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody742_51 : HolLoopProg 64 :=
.mark loopBody742_50

def loopBody742_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody742_53 : HolLoopProg 64 :=
.mark loopBody742_52

def loopBody742_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 128#64])

def loopBody742_55 : HolLoopProg 64 :=
.mark loopBody742_54

def loopBody742_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody742_57 : HolLoopProg 64 :=
.mark loopBody742_56

def loopBody742_58 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 771) ([6, 7]) (some (6, loopBody742_33, loopBody742_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody742_59 : HolLoopProg 64 :=
.mark loopBody742_58

def loopBody742_60 : HolLoopProg 64 :=
.seq loopBody742_59 loopBody742_1

def loopBody742_61 : HolLoopProg 64 :=
.mark loopBody742_60

def loopBody742_62 : HolLoopProg 64 :=
.seq loopBody742_57 loopBody742_61

def loopBody742_63 : HolLoopProg 64 :=
.mark loopBody742_62

def loopBody742_64 : HolLoopProg 64 :=
.seq loopBody742_55 loopBody742_63

def loopBody742_65 : HolLoopProg 64 :=
.mark loopBody742_64

def loopBody742_66 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody742_65 loopBody742_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody742_67 : HolLoopProg 64 :=
.mark loopBody742_66

def loopBody742_68 : HolLoopProg 64 :=
.seq loopBody742_67 loopBody742_1

def loopBody742_69 : HolLoopProg 64 :=
.mark loopBody742_68

def loopBody742_70 : HolLoopProg 64 :=
.seq loopBody742_53 loopBody742_69

def loopBody742_71 : HolLoopProg 64 :=
.mark loopBody742_70

def loopBody742_72 : HolLoopProg 64 :=
.seq loopBody742_51 loopBody742_71

def loopBody742_73 : HolLoopProg 64 :=
.mark loopBody742_72

def loopBody742_74 : HolLoopProg 64 :=
.seq loopBody742_45 loopBody742_73

def loopBody742_75 : HolLoopProg 64 :=
.mark loopBody742_74

def loopBody742_76 : HolLoopProg 64 :=
.seq loopBody742_43 loopBody742_75

def loopBody742_77 : HolLoopProg 64 :=
.mark loopBody742_76

def loopBody742_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody742_79 : HolLoopProg 64 :=
.mark loopBody742_78

def loopBody742_80 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody742_47 loopBody742_49 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody742_81 : HolLoopProg 64 :=
.mark loopBody742_80

def loopBody742_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody742_83 : HolLoopProg 64 :=
.mark loopBody742_82

def loopBody742_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody742_85 : HolLoopProg 64 :=
.mark loopBody742_84

def loopBody742_86 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 70) ([7]) (some (7, loopBody742_85, loopBody742_1, (Flapjack.Spt.ln)))

def loopBody742_87 : HolLoopProg 64 :=
.mark loopBody742_86

def loopBody742_88 : HolLoopProg 64 :=
.seq loopBody742_87 loopBody742_1

def loopBody742_89 : HolLoopProg 64 :=
.mark loopBody742_88

def loopBody742_90 : HolLoopProg 64 :=
.seq loopBody742_83 loopBody742_89

def loopBody742_91 : HolLoopProg 64 :=
.mark loopBody742_90

def loopBody742_92 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_91

def loopBody742_93 : HolLoopProg 64 :=
.mark loopBody742_92

def loopBody742_94 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_93

def loopBody742_95 : HolLoopProg 64 :=
.mark loopBody742_94

def loopBody742_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody742_97 : HolLoopProg 64 :=
.mark loopBody742_96

def loopBody742_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody742_99 : HolLoopProg 64 :=
.mark loopBody742_98

def loopBody742_100 : HolLoopProg 64 :=
.seq loopBody742_99 loopBody742_1

def loopBody742_101 : HolLoopProg 64 :=
.mark loopBody742_100

def loopBody742_102 : HolLoopProg 64 :=
.seq loopBody742_97 loopBody742_101

def loopBody742_103 : HolLoopProg 64 :=
.mark loopBody742_102

def loopBody742_104 : HolLoopProg 64 :=
.seq loopBody742_95 loopBody742_103

def loopBody742_105 : HolLoopProg 64 :=
.mark loopBody742_104

def loopBody742_106 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody742_105 loopBody742_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody742_107 : HolLoopProg 64 :=
.mark loopBody742_106

def loopBody742_108 : HolLoopProg 64 :=
.seq loopBody742_107 loopBody742_1

def loopBody742_109 : HolLoopProg 64 :=
.mark loopBody742_108

def loopBody742_110 : HolLoopProg 64 :=
.seq loopBody742_53 loopBody742_109

def loopBody742_111 : HolLoopProg 64 :=
.mark loopBody742_110

def loopBody742_112 : HolLoopProg 64 :=
.seq loopBody742_81 loopBody742_111

def loopBody742_113 : HolLoopProg 64 :=
.mark loopBody742_112

def loopBody742_114 : HolLoopProg 64 :=
.seq loopBody742_79 loopBody742_113

def loopBody742_115 : HolLoopProg 64 :=
.mark loopBody742_114

def loopBody742_116 : HolLoopProg 64 :=
.seq loopBody742_43 loopBody742_115

def loopBody742_117 : HolLoopProg 64 :=
.mark loopBody742_116

def loopBody742_118 : HolLoopProg 64 :=
.seq loopBody742_77 loopBody742_117

def loopBody742_119 : HolLoopProg 64 :=
.mark loopBody742_118

def loopBody742_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody742_121 : HolLoopProg 64 :=
.mark loopBody742_120

def loopBody742_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody742_123 : HolLoopProg 64 :=
.mark loopBody742_122

def loopBody742_124 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 767) ([7, 8, 9]) (some (7, loopBody742_85, loopBody742_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody742_125 : HolLoopProg 64 :=
.mark loopBody742_124

def loopBody742_126 : HolLoopProg 64 :=
.seq loopBody742_125 loopBody742_1

def loopBody742_127 : HolLoopProg 64 :=
.mark loopBody742_126

def loopBody742_128 : HolLoopProg 64 :=
.seq loopBody742_123 loopBody742_127

def loopBody742_129 : HolLoopProg 64 :=
.mark loopBody742_128

def loopBody742_130 : HolLoopProg 64 :=
.seq loopBody742_121 loopBody742_129

def loopBody742_131 : HolLoopProg 64 :=
.mark loopBody742_130

def loopBody742_132 : HolLoopProg 64 :=
.seq loopBody742_31 loopBody742_131

def loopBody742_133 : HolLoopProg 64 :=
.mark loopBody742_132

def loopBody742_134 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_133

def loopBody742_135 : HolLoopProg 64 :=
.mark loopBody742_134

def loopBody742_136 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_135

def loopBody742_137 : HolLoopProg 64 :=
.mark loopBody742_136

def loopBody742_138 : HolLoopProg 64 :=
.seq loopBody742_119 loopBody742_137

def loopBody742_139 : HolLoopProg 64 :=
.mark loopBody742_138

def loopBody742_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody742_141 : HolLoopProg 64 :=
.mark loopBody742_140

def loopBody742_142 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 772) ([7, 8]) (some (7, loopBody742_85, loopBody742_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody742_143 : HolLoopProg 64 :=
.mark loopBody742_142

def loopBody742_144 : HolLoopProg 64 :=
.seq loopBody742_143 loopBody742_1

def loopBody742_145 : HolLoopProg 64 :=
.mark loopBody742_144

def loopBody742_146 : HolLoopProg 64 :=
.seq loopBody742_141 loopBody742_145

def loopBody742_147 : HolLoopProg 64 :=
.mark loopBody742_146

def loopBody742_148 : HolLoopProg 64 :=
.seq loopBody742_31 loopBody742_147

def loopBody742_149 : HolLoopProg 64 :=
.mark loopBody742_148

def loopBody742_150 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_149

def loopBody742_151 : HolLoopProg 64 :=
.mark loopBody742_150

def loopBody742_152 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_151

def loopBody742_153 : HolLoopProg 64 :=
.mark loopBody742_152

def loopBody742_154 : HolLoopProg 64 :=
.seq loopBody742_139 loopBody742_153

def loopBody742_155 : HolLoopProg 64 :=
.mark loopBody742_154

def loopBody742_156 : HolLoopProg 64 :=
.seq loopBody742_155 loopBody742_95

def loopBody742_157 : HolLoopProg 64 :=
.mark loopBody742_156

def loopBody742_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody742_159 : HolLoopProg 64 :=
.mark loopBody742_158

def loopBody742_160 : HolLoopProg 64 :=
.seq loopBody742_159 loopBody742_101

def loopBody742_161 : HolLoopProg 64 :=
.mark loopBody742_160

def loopBody742_162 : HolLoopProg 64 :=
.seq loopBody742_157 loopBody742_161

def loopBody742_163 : HolLoopProg 64 :=
.mark loopBody742_162

def loopBody742_164 : HolLoopProg 64 :=
.seq loopBody742_41 loopBody742_163

def loopBody742_165 : HolLoopProg 64 :=
.mark loopBody742_164

def loopBody742_166 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_165

def loopBody742_167 : HolLoopProg 64 :=
.mark loopBody742_166

def loopBody742_168 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_167

def loopBody742_169 : HolLoopProg 64 :=
.mark loopBody742_168

def loopBody742_170 : HolLoopProg 64 :=
.seq loopBody742_27 loopBody742_169

def loopBody742_171 : HolLoopProg 64 :=
.mark loopBody742_170

def loopBody742_172 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_171

def loopBody742_173 : HolLoopProg 64 :=
.mark loopBody742_172

def loopBody742_174 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_173

def loopBody742_175 : HolLoopProg 64 :=
.mark loopBody742_174

def loopBody742_176 : HolLoopProg 64 :=
.seq loopBody742_17 loopBody742_175

def loopBody742_177 : HolLoopProg 64 :=
.mark loopBody742_176

def loopBody742_178 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_177

def loopBody742_179 : HolLoopProg 64 :=
.mark loopBody742_178

def loopBody742_180 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_179

def loopBody742_181 : HolLoopProg 64 :=
.mark loopBody742_180

def loopBody742_182 : HolLoopProg 64 :=
.seq loopBody742_7 loopBody742_181

def loopBody742_183 : HolLoopProg 64 :=
.mark loopBody742_182

def loopBody742_184 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_183

def loopBody742_185 : HolLoopProg 64 :=
.mark loopBody742_184

def loopBody742_186 : HolLoopProg 64 :=
.seq loopBody742_1 loopBody742_185

def loopBody742_187 : HolLoopProg 64 :=
.mark loopBody742_186

def output742 : Nat × List Nat × HolLoopProg 64 :=
  (806, [0, 1], loopBody742_187)
end InitECandidate.Proofs.FrontendStages.Loop
