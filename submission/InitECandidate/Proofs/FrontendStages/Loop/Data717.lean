import InitECandidate.Proofs.FrontendStages.Loop.Translate701
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody717_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody717_1 : HolLoopProg 64 :=
.mark loopBody717_0

def loopBody717_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody717_3 : HolLoopProg 64 :=
.mark loopBody717_2

def loopBody717_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody717_3, loopBody717_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody717_5 : HolLoopProg 64 :=
.mark loopBody717_4

def loopBody717_6 : HolLoopProg 64 :=
.seq loopBody717_5 loopBody717_1

def loopBody717_7 : HolLoopProg 64 :=
.mark loopBody717_6

def loopBody717_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 96#64)

def loopBody717_9 : HolLoopProg 64 :=
.mark loopBody717_8

def loopBody717_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody717_11 : HolLoopProg 64 :=
.mark loopBody717_10

def loopBody717_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody717_11, loopBody717_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody717_13 : HolLoopProg 64 :=
.mark loopBody717_12

def loopBody717_14 : HolLoopProg 64 :=
.seq loopBody717_13 loopBody717_1

def loopBody717_15 : HolLoopProg 64 :=
.mark loopBody717_14

def loopBody717_16 : HolLoopProg 64 :=
.seq loopBody717_9 loopBody717_15

def loopBody717_17 : HolLoopProg 64 :=
.mark loopBody717_16

def loopBody717_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody717_19 : HolLoopProg 64 :=
.mark loopBody717_18

def loopBody717_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody717_21 : HolLoopProg 64 :=
.mark loopBody717_20

def loopBody717_22 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 775) ([5]) (some (5, loopBody717_21, loopBody717_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody717_23 : HolLoopProg 64 :=
.mark loopBody717_22

def loopBody717_24 : HolLoopProg 64 :=
.seq loopBody717_23 loopBody717_1

def loopBody717_25 : HolLoopProg 64 :=
.mark loopBody717_24

def loopBody717_26 : HolLoopProg 64 :=
.seq loopBody717_19 loopBody717_25

def loopBody717_27 : HolLoopProg 64 :=
.mark loopBody717_26

def loopBody717_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody717_29 : HolLoopProg 64 :=
.mark loopBody717_28

def loopBody717_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody717_31 : HolLoopProg 64 :=
.mark loopBody717_30

def loopBody717_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody717_33 : HolLoopProg 64 :=
.mark loopBody717_32

def loopBody717_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody717_35 : HolLoopProg 64 :=
.mark loopBody717_34

def loopBody717_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody717_33 loopBody717_35 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody717_37 : HolLoopProg 64 :=
.mark loopBody717_36

def loopBody717_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody717_39 : HolLoopProg 64 :=
.mark loopBody717_38

def loopBody717_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody717_41 : HolLoopProg 64 :=
.mark loopBody717_40

def loopBody717_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 192#64)

def loopBody717_43 : HolLoopProg 64 :=
.mark loopBody717_42

def loopBody717_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody717_45 : HolLoopProg 64 :=
.mark loopBody717_44

def loopBody717_46 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 78) ([6, 7]) (some (6, loopBody717_45, loopBody717_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody717_47 : HolLoopProg 64 :=
.mark loopBody717_46

def loopBody717_48 : HolLoopProg 64 :=
.seq loopBody717_47 loopBody717_1

def loopBody717_49 : HolLoopProg 64 :=
.mark loopBody717_48

def loopBody717_50 : HolLoopProg 64 :=
.seq loopBody717_43 loopBody717_49

def loopBody717_51 : HolLoopProg 64 :=
.mark loopBody717_50

def loopBody717_52 : HolLoopProg 64 :=
.seq loopBody717_41 loopBody717_51

def loopBody717_53 : HolLoopProg 64 :=
.mark loopBody717_52

def loopBody717_54 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_53

def loopBody717_55 : HolLoopProg 64 :=
.mark loopBody717_54

def loopBody717_56 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_55

def loopBody717_57 : HolLoopProg 64 :=
.mark loopBody717_56

def loopBody717_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody717_59 : HolLoopProg 64 :=
.mark loopBody717_58

def loopBody717_60 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 70) ([6]) (some (6, loopBody717_45, loopBody717_1, (Flapjack.Spt.ln)))

def loopBody717_61 : HolLoopProg 64 :=
.mark loopBody717_60

def loopBody717_62 : HolLoopProg 64 :=
.seq loopBody717_61 loopBody717_1

def loopBody717_63 : HolLoopProg 64 :=
.mark loopBody717_62

def loopBody717_64 : HolLoopProg 64 :=
.seq loopBody717_59 loopBody717_63

def loopBody717_65 : HolLoopProg 64 :=
.mark loopBody717_64

def loopBody717_66 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_65

def loopBody717_67 : HolLoopProg 64 :=
.mark loopBody717_66

def loopBody717_68 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_67

def loopBody717_69 : HolLoopProg 64 :=
.mark loopBody717_68

def loopBody717_70 : HolLoopProg 64 :=
.seq loopBody717_57 loopBody717_69

def loopBody717_71 : HolLoopProg 64 :=
.mark loopBody717_70

def loopBody717_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody717_73 : HolLoopProg 64 :=
.mark loopBody717_72

def loopBody717_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody717_75 : HolLoopProg 64 :=
.mark loopBody717_74

def loopBody717_76 : HolLoopProg 64 :=
.seq loopBody717_75 loopBody717_1

def loopBody717_77 : HolLoopProg 64 :=
.mark loopBody717_76

def loopBody717_78 : HolLoopProg 64 :=
.seq loopBody717_73 loopBody717_77

def loopBody717_79 : HolLoopProg 64 :=
.mark loopBody717_78

def loopBody717_80 : HolLoopProg 64 :=
.seq loopBody717_71 loopBody717_79

def loopBody717_81 : HolLoopProg 64 :=
.mark loopBody717_80

def loopBody717_82 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody717_81 loopBody717_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody717_83 : HolLoopProg 64 :=
.mark loopBody717_82

def loopBody717_84 : HolLoopProg 64 :=
.seq loopBody717_83 loopBody717_1

def loopBody717_85 : HolLoopProg 64 :=
.mark loopBody717_84

def loopBody717_86 : HolLoopProg 64 :=
.seq loopBody717_39 loopBody717_85

def loopBody717_87 : HolLoopProg 64 :=
.mark loopBody717_86

def loopBody717_88 : HolLoopProg 64 :=
.seq loopBody717_37 loopBody717_87

def loopBody717_89 : HolLoopProg 64 :=
.mark loopBody717_88

def loopBody717_90 : HolLoopProg 64 :=
.seq loopBody717_31 loopBody717_89

def loopBody717_91 : HolLoopProg 64 :=
.mark loopBody717_90

def loopBody717_92 : HolLoopProg 64 :=
.seq loopBody717_29 loopBody717_91

def loopBody717_93 : HolLoopProg 64 :=
.mark loopBody717_92

def loopBody717_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody717_95 : HolLoopProg 64 :=
.mark loopBody717_94

def loopBody717_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 192#64])

def loopBody717_97 : HolLoopProg 64 :=
.mark loopBody717_96

def loopBody717_98 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 739) ([6, 7]) (some (6, loopBody717_45, loopBody717_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody717_99 : HolLoopProg 64 :=
.mark loopBody717_98

def loopBody717_100 : HolLoopProg 64 :=
.seq loopBody717_99 loopBody717_1

def loopBody717_101 : HolLoopProg 64 :=
.mark loopBody717_100

def loopBody717_102 : HolLoopProg 64 :=
.seq loopBody717_97 loopBody717_101

def loopBody717_103 : HolLoopProg 64 :=
.mark loopBody717_102

def loopBody717_104 : HolLoopProg 64 :=
.seq loopBody717_95 loopBody717_103

def loopBody717_105 : HolLoopProg 64 :=
.mark loopBody717_104

def loopBody717_106 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_105

def loopBody717_107 : HolLoopProg 64 :=
.mark loopBody717_106

def loopBody717_108 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_107

def loopBody717_109 : HolLoopProg 64 :=
.mark loopBody717_108

def loopBody717_110 : HolLoopProg 64 :=
.seq loopBody717_93 loopBody717_109

def loopBody717_111 : HolLoopProg 64 :=
.mark loopBody717_110

def loopBody717_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody717_113 : HolLoopProg 64 :=
.mark loopBody717_112

def loopBody717_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody717_115 : HolLoopProg 64 :=
.mark loopBody717_114

def loopBody717_116 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 735) ([6, 7, 8]) (some (6, loopBody717_45, loopBody717_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody717_117 : HolLoopProg 64 :=
.mark loopBody717_116

def loopBody717_118 : HolLoopProg 64 :=
.seq loopBody717_117 loopBody717_1

def loopBody717_119 : HolLoopProg 64 :=
.mark loopBody717_118

def loopBody717_120 : HolLoopProg 64 :=
.seq loopBody717_115 loopBody717_119

def loopBody717_121 : HolLoopProg 64 :=
.mark loopBody717_120

def loopBody717_122 : HolLoopProg 64 :=
.seq loopBody717_113 loopBody717_121

def loopBody717_123 : HolLoopProg 64 :=
.mark loopBody717_122

def loopBody717_124 : HolLoopProg 64 :=
.seq loopBody717_41 loopBody717_123

def loopBody717_125 : HolLoopProg 64 :=
.mark loopBody717_124

def loopBody717_126 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_125

def loopBody717_127 : HolLoopProg 64 :=
.mark loopBody717_126

def loopBody717_128 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_127

def loopBody717_129 : HolLoopProg 64 :=
.mark loopBody717_128

def loopBody717_130 : HolLoopProg 64 :=
.seq loopBody717_111 loopBody717_129

def loopBody717_131 : HolLoopProg 64 :=
.mark loopBody717_130

def loopBody717_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody717_133 : HolLoopProg 64 :=
.mark loopBody717_132

def loopBody717_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64])

def loopBody717_135 : HolLoopProg 64 :=
.mark loopBody717_134

def loopBody717_136 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 735) ([6, 7, 8]) (some (6, loopBody717_45, loopBody717_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody717_137 : HolLoopProg 64 :=
.mark loopBody717_136

def loopBody717_138 : HolLoopProg 64 :=
.seq loopBody717_137 loopBody717_1

def loopBody717_139 : HolLoopProg 64 :=
.mark loopBody717_138

def loopBody717_140 : HolLoopProg 64 :=
.seq loopBody717_115 loopBody717_139

def loopBody717_141 : HolLoopProg 64 :=
.mark loopBody717_140

def loopBody717_142 : HolLoopProg 64 :=
.seq loopBody717_135 loopBody717_141

def loopBody717_143 : HolLoopProg 64 :=
.mark loopBody717_142

def loopBody717_144 : HolLoopProg 64 :=
.seq loopBody717_133 loopBody717_143

def loopBody717_145 : HolLoopProg 64 :=
.mark loopBody717_144

def loopBody717_146 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_145

def loopBody717_147 : HolLoopProg 64 :=
.mark loopBody717_146

def loopBody717_148 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_147

def loopBody717_149 : HolLoopProg 64 :=
.mark loopBody717_148

def loopBody717_150 : HolLoopProg 64 :=
.seq loopBody717_131 loopBody717_149

def loopBody717_151 : HolLoopProg 64 :=
.mark loopBody717_150

def loopBody717_152 : HolLoopProg 64 :=
.seq loopBody717_151 loopBody717_69

def loopBody717_153 : HolLoopProg 64 :=
.mark loopBody717_152

def loopBody717_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody717_155 : HolLoopProg 64 :=
.mark loopBody717_154

def loopBody717_156 : HolLoopProg 64 :=
.seq loopBody717_155 loopBody717_77

def loopBody717_157 : HolLoopProg 64 :=
.mark loopBody717_156

def loopBody717_158 : HolLoopProg 64 :=
.seq loopBody717_153 loopBody717_157

def loopBody717_159 : HolLoopProg 64 :=
.mark loopBody717_158

def loopBody717_160 : HolLoopProg 64 :=
.seq loopBody717_27 loopBody717_159

def loopBody717_161 : HolLoopProg 64 :=
.mark loopBody717_160

def loopBody717_162 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_161

def loopBody717_163 : HolLoopProg 64 :=
.mark loopBody717_162

def loopBody717_164 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_163

def loopBody717_165 : HolLoopProg 64 :=
.mark loopBody717_164

def loopBody717_166 : HolLoopProg 64 :=
.seq loopBody717_17 loopBody717_165

def loopBody717_167 : HolLoopProg 64 :=
.mark loopBody717_166

def loopBody717_168 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_167

def loopBody717_169 : HolLoopProg 64 :=
.mark loopBody717_168

def loopBody717_170 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_169

def loopBody717_171 : HolLoopProg 64 :=
.mark loopBody717_170

def loopBody717_172 : HolLoopProg 64 :=
.seq loopBody717_7 loopBody717_171

def loopBody717_173 : HolLoopProg 64 :=
.mark loopBody717_172

def loopBody717_174 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_173

def loopBody717_175 : HolLoopProg 64 :=
.mark loopBody717_174

def loopBody717_176 : HolLoopProg 64 :=
.seq loopBody717_1 loopBody717_175

def loopBody717_177 : HolLoopProg 64 :=
.mark loopBody717_176

def output717 : Nat × List Nat × HolLoopProg 64 :=
  (781, [0, 1], loopBody717_177)
end InitECandidate.Proofs.FrontendStages.Loop
