import InitECandidate.Proofs.FrontendStages.Loop.Translate507
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody523_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody523_1 : HolLoopProg 64 :=
.mark loopBody523_0

def loopBody523_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody523_3 : HolLoopProg 64 :=
.mark loopBody523_2

def loopBody523_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody523_5 : HolLoopProg 64 :=
.mark loopBody523_4

def loopBody523_6 : HolLoopProg 64 :=
.call (some ([1, 2], Flapjack.Spt.ls PUnit.unit)) (some 561) ([3]) (some (3, loopBody523_5, loopBody523_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody523_7 : HolLoopProg 64 :=
.mark loopBody523_6

def loopBody523_8 : HolLoopProg 64 :=
.seq loopBody523_7 loopBody523_1

def loopBody523_9 : HolLoopProg 64 :=
.mark loopBody523_8

def loopBody523_10 : HolLoopProg 64 :=
.seq loopBody523_3 loopBody523_9

def loopBody523_11 : HolLoopProg 64 :=
.mark loopBody523_10

def loopBody523_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody523_13 : HolLoopProg 64 :=
.mark loopBody523_12

def loopBody523_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody523_15 : HolLoopProg 64 :=
.mark loopBody523_14

def loopBody523_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody523_17 : HolLoopProg 64 :=
.mark loopBody523_16

def loopBody523_18 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 464) ([4, 5]) (some (4, loopBody523_17, loopBody523_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody523_19 : HolLoopProg 64 :=
.mark loopBody523_18

def loopBody523_20 : HolLoopProg 64 :=
.seq loopBody523_19 loopBody523_1

def loopBody523_21 : HolLoopProg 64 :=
.mark loopBody523_20

def loopBody523_22 : HolLoopProg 64 :=
.seq loopBody523_15 loopBody523_21

def loopBody523_23 : HolLoopProg 64 :=
.mark loopBody523_22

def loopBody523_24 : HolLoopProg 64 :=
.seq loopBody523_13 loopBody523_23

def loopBody523_25 : HolLoopProg 64 :=
.mark loopBody523_24

def loopBody523_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody523_27 : HolLoopProg 64 :=
.mark loopBody523_26

def loopBody523_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody523_29 : HolLoopProg 64 :=
.mark loopBody523_28

def loopBody523_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody523_31 : HolLoopProg 64 :=
.mark loopBody523_30

def loopBody523_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody523_33 : HolLoopProg 64 :=
.mark loopBody523_32

def loopBody523_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody523_31 loopBody523_33 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))

def loopBody523_35 : HolLoopProg 64 :=
.mark loopBody523_34

def loopBody523_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody523_37 : HolLoopProg 64 :=
.mark loopBody523_36

def loopBody523_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody523_39 : HolLoopProg 64 :=
.mark loopBody523_38

def loopBody523_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody523_41 : HolLoopProg 64 :=
.mark loopBody523_40

def loopBody523_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4, 5, 6]

def loopBody523_43 : HolLoopProg 64 :=
.mark loopBody523_42

def loopBody523_44 : HolLoopProg 64 :=
.seq loopBody523_43 loopBody523_1

def loopBody523_45 : HolLoopProg 64 :=
.mark loopBody523_44

def loopBody523_46 : HolLoopProg 64 :=
.seq loopBody523_29 loopBody523_45

def loopBody523_47 : HolLoopProg 64 :=
.mark loopBody523_46

def loopBody523_48 : HolLoopProg 64 :=
.seq loopBody523_41 loopBody523_47

def loopBody523_49 : HolLoopProg 64 :=
.mark loopBody523_48

def loopBody523_50 : HolLoopProg 64 :=
.seq loopBody523_39 loopBody523_49

def loopBody523_51 : HolLoopProg 64 :=
.mark loopBody523_50

def loopBody523_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody523_51 loopBody523_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody523_53 : HolLoopProg 64 :=
.mark loopBody523_52

def loopBody523_54 : HolLoopProg 64 :=
.seq loopBody523_53 loopBody523_1

def loopBody523_55 : HolLoopProg 64 :=
.mark loopBody523_54

def loopBody523_56 : HolLoopProg 64 :=
.seq loopBody523_37 loopBody523_55

def loopBody523_57 : HolLoopProg 64 :=
.mark loopBody523_56

def loopBody523_58 : HolLoopProg 64 :=
.seq loopBody523_35 loopBody523_57

def loopBody523_59 : HolLoopProg 64 :=
.mark loopBody523_58

def loopBody523_60 : HolLoopProg 64 :=
.seq loopBody523_29 loopBody523_59

def loopBody523_61 : HolLoopProg 64 :=
.mark loopBody523_60

def loopBody523_62 : HolLoopProg 64 :=
.seq loopBody523_27 loopBody523_61

def loopBody523_63 : HolLoopProg 64 :=
.mark loopBody523_62

def loopBody523_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 24#64)

def loopBody523_65 : HolLoopProg 64 :=
.mark loopBody523_64

def loopBody523_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody523_67 : HolLoopProg 64 :=
.mark loopBody523_66

def loopBody523_68 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 68) ([5]) (some (5, loopBody523_67, loopBody523_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))

def loopBody523_69 : HolLoopProg 64 :=
.mark loopBody523_68

def loopBody523_70 : HolLoopProg 64 :=
.seq loopBody523_69 loopBody523_1

def loopBody523_71 : HolLoopProg 64 :=
.mark loopBody523_70

def loopBody523_72 : HolLoopProg 64 :=
.seq loopBody523_65 loopBody523_71

def loopBody523_73 : HolLoopProg 64 :=
.mark loopBody523_72

def loopBody523_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody523_75 : HolLoopProg 64 :=
.mark loopBody523_74

def loopBody523_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 3#64])

def loopBody523_77 : HolLoopProg 64 :=
.mark loopBody523_76

def loopBody523_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 20#64)

def loopBody523_79 : HolLoopProg 64 :=
.mark loopBody523_78

def loopBody523_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody523_81 : HolLoopProg 64 :=
.mark loopBody523_80

def loopBody523_82 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 77) ([6, 7, 8]) (some (6, loopBody523_81, loopBody523_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody523_83 : HolLoopProg 64 :=
.mark loopBody523_82

def loopBody523_84 : HolLoopProg 64 :=
.seq loopBody523_83 loopBody523_1

def loopBody523_85 : HolLoopProg 64 :=
.mark loopBody523_84

def loopBody523_86 : HolLoopProg 64 :=
.seq loopBody523_79 loopBody523_85

def loopBody523_87 : HolLoopProg 64 :=
.mark loopBody523_86

def loopBody523_88 : HolLoopProg 64 :=
.seq loopBody523_77 loopBody523_87

def loopBody523_89 : HolLoopProg 64 :=
.mark loopBody523_88

def loopBody523_90 : HolLoopProg 64 :=
.seq loopBody523_75 loopBody523_89

def loopBody523_91 : HolLoopProg 64 :=
.mark loopBody523_90

def loopBody523_92 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_91

def loopBody523_93 : HolLoopProg 64 :=
.mark loopBody523_92

def loopBody523_94 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_93

def loopBody523_95 : HolLoopProg 64 :=
.mark loopBody523_94

def loopBody523_96 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 489) ([6]) (some (6, loopBody523_81, loopBody523_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody523_97 : HolLoopProg 64 :=
.mark loopBody523_96

def loopBody523_98 : HolLoopProg 64 :=
.seq loopBody523_97 loopBody523_1

def loopBody523_99 : HolLoopProg 64 :=
.mark loopBody523_98

def loopBody523_100 : HolLoopProg 64 :=
.seq loopBody523_75 loopBody523_99

def loopBody523_101 : HolLoopProg 64 :=
.mark loopBody523_100

def loopBody523_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody523_103 : HolLoopProg 64 :=
.mark loopBody523_102

def loopBody523_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody523_105 : HolLoopProg 64 :=
.mark loopBody523_104

def loopBody523_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody523_107 : HolLoopProg 64 :=
.mark loopBody523_106

def loopBody523_108 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.reg 8) loopBody523_105 loopBody523_107 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody523_109 : HolLoopProg 64 :=
.mark loopBody523_108

def loopBody523_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody523_111 : HolLoopProg 64 :=
.mark loopBody523_110

def loopBody523_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody523_113 : HolLoopProg 64 :=
.mark loopBody523_112

def loopBody523_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody523_115 : HolLoopProg 64 :=
.mark loopBody523_114

def loopBody523_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 100#64)

def loopBody523_117 : HolLoopProg 64 :=
.mark loopBody523_116

def loopBody523_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6, 7, 8]

def loopBody523_119 : HolLoopProg 64 :=
.mark loopBody523_118

def loopBody523_120 : HolLoopProg 64 :=
.seq loopBody523_119 loopBody523_1

def loopBody523_121 : HolLoopProg 64 :=
.mark loopBody523_120

def loopBody523_122 : HolLoopProg 64 :=
.seq loopBody523_117 loopBody523_121

def loopBody523_123 : HolLoopProg 64 :=
.mark loopBody523_122

def loopBody523_124 : HolLoopProg 64 :=
.seq loopBody523_115 loopBody523_123

def loopBody523_125 : HolLoopProg 64 :=
.mark loopBody523_124

def loopBody523_126 : HolLoopProg 64 :=
.seq loopBody523_113 loopBody523_125

def loopBody523_127 : HolLoopProg 64 :=
.mark loopBody523_126

def loopBody523_128 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody523_127 loopBody523_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody523_129 : HolLoopProg 64 :=
.mark loopBody523_128

def loopBody523_130 : HolLoopProg 64 :=
.seq loopBody523_129 loopBody523_1

def loopBody523_131 : HolLoopProg 64 :=
.mark loopBody523_130

def loopBody523_132 : HolLoopProg 64 :=
.seq loopBody523_111 loopBody523_131

def loopBody523_133 : HolLoopProg 64 :=
.mark loopBody523_132

def loopBody523_134 : HolLoopProg 64 :=
.seq loopBody523_109 loopBody523_133

def loopBody523_135 : HolLoopProg 64 :=
.mark loopBody523_134

def loopBody523_136 : HolLoopProg 64 :=
.seq loopBody523_103 loopBody523_135

def loopBody523_137 : HolLoopProg 64 :=
.mark loopBody523_136

def loopBody523_138 : HolLoopProg 64 :=
.seq loopBody523_37 loopBody523_137

def loopBody523_139 : HolLoopProg 64 :=
.mark loopBody523_138

def loopBody523_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 3000#64)

def loopBody523_141 : HolLoopProg 64 :=
.mark loopBody523_140

def loopBody523_142 : HolLoopProg 64 :=
.seq loopBody523_141 loopBody523_121

def loopBody523_143 : HolLoopProg 64 :=
.mark loopBody523_142

def loopBody523_144 : HolLoopProg 64 :=
.seq loopBody523_115 loopBody523_143

def loopBody523_145 : HolLoopProg 64 :=
.mark loopBody523_144

def loopBody523_146 : HolLoopProg 64 :=
.seq loopBody523_113 loopBody523_145

def loopBody523_147 : HolLoopProg 64 :=
.mark loopBody523_146

def loopBody523_148 : HolLoopProg 64 :=
.seq loopBody523_139 loopBody523_147

def loopBody523_149 : HolLoopProg 64 :=
.mark loopBody523_148

def loopBody523_150 : HolLoopProg 64 :=
.seq loopBody523_101 loopBody523_149

def loopBody523_151 : HolLoopProg 64 :=
.mark loopBody523_150

def loopBody523_152 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_151

def loopBody523_153 : HolLoopProg 64 :=
.mark loopBody523_152

def loopBody523_154 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_153

def loopBody523_155 : HolLoopProg 64 :=
.mark loopBody523_154

def loopBody523_156 : HolLoopProg 64 :=
.seq loopBody523_95 loopBody523_155

def loopBody523_157 : HolLoopProg 64 :=
.mark loopBody523_156

def loopBody523_158 : HolLoopProg 64 :=
.seq loopBody523_73 loopBody523_157

def loopBody523_159 : HolLoopProg 64 :=
.mark loopBody523_158

def loopBody523_160 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_159

def loopBody523_161 : HolLoopProg 64 :=
.mark loopBody523_160

def loopBody523_162 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_161

def loopBody523_163 : HolLoopProg 64 :=
.mark loopBody523_162

def loopBody523_164 : HolLoopProg 64 :=
.seq loopBody523_63 loopBody523_163

def loopBody523_165 : HolLoopProg 64 :=
.mark loopBody523_164

def loopBody523_166 : HolLoopProg 64 :=
.seq loopBody523_25 loopBody523_165

def loopBody523_167 : HolLoopProg 64 :=
.mark loopBody523_166

def loopBody523_168 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_167

def loopBody523_169 : HolLoopProg 64 :=
.mark loopBody523_168

def loopBody523_170 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_169

def loopBody523_171 : HolLoopProg 64 :=
.mark loopBody523_170

def loopBody523_172 : HolLoopProg 64 :=
.seq loopBody523_11 loopBody523_171

def loopBody523_173 : HolLoopProg 64 :=
.mark loopBody523_172

def loopBody523_174 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_173

def loopBody523_175 : HolLoopProg 64 :=
.mark loopBody523_174

def loopBody523_176 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_175

def loopBody523_177 : HolLoopProg 64 :=
.mark loopBody523_176

def loopBody523_178 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_177

def loopBody523_179 : HolLoopProg 64 :=
.mark loopBody523_178

def loopBody523_180 : HolLoopProg 64 :=
.seq loopBody523_1 loopBody523_179

def loopBody523_181 : HolLoopProg 64 :=
.mark loopBody523_180

def output523 : Nat × List Nat × HolLoopProg 64 :=
  (587, [0], loopBody523_181)
end InitECandidate.Proofs.FrontendStages.Loop
