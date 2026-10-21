import InitECandidate.Proofs.FrontendStages.Loop.Translate586
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody602_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody602_1 : HolLoopProg 64 :=
.mark loopBody602_0

def loopBody602_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody602_3 : HolLoopProg 64 :=
.mark loopBody602_2

def loopBody602_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody602_5 : HolLoopProg 64 :=
.mark loopBody602_4

def loopBody602_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody602_7 : HolLoopProg 64 :=
.mark loopBody602_6

def loopBody602_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody602_5 loopBody602_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody602_9 : HolLoopProg 64 :=
.mark loopBody602_8

def loopBody602_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody602_11 : HolLoopProg 64 :=
.mark loopBody602_10

def loopBody602_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody602_13 : HolLoopProg 64 :=
.mark loopBody602_12

def loopBody602_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 2))

def loopBody602_15 : HolLoopProg 64 :=
.mark loopBody602_14

def loopBody602_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64]))

def loopBody602_17 : HolLoopProg 64 :=
.mark loopBody602_16

def loopBody602_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 16#64]))

def loopBody602_19 : HolLoopProg 64 :=
.mark loopBody602_18

def loopBody602_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 24#64]))

def loopBody602_21 : HolLoopProg 64 :=
.mark loopBody602_20

def loopBody602_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 3))

def loopBody602_23 : HolLoopProg 64 :=
.mark loopBody602_22

def loopBody602_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 8#64]))

def loopBody602_25 : HolLoopProg 64 :=
.mark loopBody602_24

def loopBody602_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 16#64]))

def loopBody602_27 : HolLoopProg 64 :=
.mark loopBody602_26

def loopBody602_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 24#64]))

def loopBody602_29 : HolLoopProg 64 :=
.mark loopBody602_28

def loopBody602_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody602_31 : HolLoopProg 64 :=
.mark loopBody602_30

def loopBody602_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody602_33 : HolLoopProg 64 :=
.mark loopBody602_32

def loopBody602_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 6)

def loopBody602_35 : HolLoopProg 64 :=
.mark loopBody602_34

def loopBody602_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 7)

def loopBody602_37 : HolLoopProg 64 :=
.mark loopBody602_36

def loopBody602_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 8)

def loopBody602_39 : HolLoopProg 64 :=
.mark loopBody602_38

def loopBody602_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 9)

def loopBody602_41 : HolLoopProg 64 :=
.mark loopBody602_40

def loopBody602_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 10)

def loopBody602_43 : HolLoopProg 64 :=
.mark loopBody602_42

def loopBody602_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 23 (Flapjack.HolLoopExp.var 11)

def loopBody602_45 : HolLoopProg 64 :=
.mark loopBody602_44

def loopBody602_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 16

def loopBody602_47 : HolLoopProg 64 :=
.mark loopBody602_46

def loopBody602_48 : HolLoopProg 64 :=
.call (some ([12, 13, 14, 15], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 657) ([16, 17, 18, 19, 20, 21, 22, 23]) (some (16, loopBody602_47, loopBody602_13, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))

def loopBody602_49 : HolLoopProg 64 :=
.mark loopBody602_48

def loopBody602_50 : HolLoopProg 64 :=
.seq loopBody602_49 loopBody602_13

def loopBody602_51 : HolLoopProg 64 :=
.mark loopBody602_50

def loopBody602_52 : HolLoopProg 64 :=
.seq loopBody602_45 loopBody602_51

def loopBody602_53 : HolLoopProg 64 :=
.mark loopBody602_52

def loopBody602_54 : HolLoopProg 64 :=
.seq loopBody602_43 loopBody602_53

def loopBody602_55 : HolLoopProg 64 :=
.mark loopBody602_54

def loopBody602_56 : HolLoopProg 64 :=
.seq loopBody602_41 loopBody602_55

def loopBody602_57 : HolLoopProg 64 :=
.mark loopBody602_56

def loopBody602_58 : HolLoopProg 64 :=
.seq loopBody602_39 loopBody602_57

def loopBody602_59 : HolLoopProg 64 :=
.mark loopBody602_58

def loopBody602_60 : HolLoopProg 64 :=
.seq loopBody602_37 loopBody602_59

def loopBody602_61 : HolLoopProg 64 :=
.mark loopBody602_60

def loopBody602_62 : HolLoopProg 64 :=
.seq loopBody602_35 loopBody602_61

def loopBody602_63 : HolLoopProg 64 :=
.mark loopBody602_62

def loopBody602_64 : HolLoopProg 64 :=
.seq loopBody602_33 loopBody602_63

def loopBody602_65 : HolLoopProg 64 :=
.mark loopBody602_64

def loopBody602_66 : HolLoopProg 64 :=
.seq loopBody602_31 loopBody602_65

def loopBody602_67 : HolLoopProg 64 :=
.mark loopBody602_66

def loopBody602_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 1)

def loopBody602_69 : HolLoopProg 64 :=
.mark loopBody602_68

def loopBody602_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 12)

def loopBody602_71 : HolLoopProg 64 :=
.mark loopBody602_70

def loopBody602_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 13)

def loopBody602_73 : HolLoopProg 64 :=
.mark loopBody602_72

def loopBody602_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 14)

def loopBody602_75 : HolLoopProg 64 :=
.mark loopBody602_74

def loopBody602_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 15)

def loopBody602_77 : HolLoopProg 64 :=
.mark loopBody602_76

def loopBody602_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 17)

def loopBody602_79 : HolLoopProg 64 :=
.mark loopBody602_78

def loopBody602_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 16) 21

def loopBody602_81 : HolLoopProg 64 :=
.mark loopBody602_80

def loopBody602_82 : HolLoopProg 64 :=
.seq loopBody602_81 loopBody602_13

def loopBody602_83 : HolLoopProg 64 :=
.mark loopBody602_82

def loopBody602_84 : HolLoopProg 64 :=
.seq loopBody602_79 loopBody602_83

def loopBody602_85 : HolLoopProg 64 :=
.mark loopBody602_84

def loopBody602_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 18)

def loopBody602_87 : HolLoopProg 64 :=
.mark loopBody602_86

def loopBody602_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 16, Flapjack.HolLoopExp.const 8#64]) 21

def loopBody602_89 : HolLoopProg 64 :=
.mark loopBody602_88

def loopBody602_90 : HolLoopProg 64 :=
.seq loopBody602_89 loopBody602_13

def loopBody602_91 : HolLoopProg 64 :=
.mark loopBody602_90

def loopBody602_92 : HolLoopProg 64 :=
.seq loopBody602_87 loopBody602_91

def loopBody602_93 : HolLoopProg 64 :=
.mark loopBody602_92

def loopBody602_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 19)

def loopBody602_95 : HolLoopProg 64 :=
.mark loopBody602_94

def loopBody602_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 16, Flapjack.HolLoopExp.const 16#64]) 21

def loopBody602_97 : HolLoopProg 64 :=
.mark loopBody602_96

def loopBody602_98 : HolLoopProg 64 :=
.seq loopBody602_97 loopBody602_13

def loopBody602_99 : HolLoopProg 64 :=
.mark loopBody602_98

def loopBody602_100 : HolLoopProg 64 :=
.seq loopBody602_95 loopBody602_99

def loopBody602_101 : HolLoopProg 64 :=
.mark loopBody602_100

def loopBody602_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 20)

def loopBody602_103 : HolLoopProg 64 :=
.mark loopBody602_102

def loopBody602_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 16, Flapjack.HolLoopExp.const 24#64]) 21

def loopBody602_105 : HolLoopProg 64 :=
.mark loopBody602_104

def loopBody602_106 : HolLoopProg 64 :=
.seq loopBody602_105 loopBody602_13

def loopBody602_107 : HolLoopProg 64 :=
.mark loopBody602_106

def loopBody602_108 : HolLoopProg 64 :=
.seq loopBody602_103 loopBody602_107

def loopBody602_109 : HolLoopProg 64 :=
.mark loopBody602_108

def loopBody602_110 : HolLoopProg 64 :=
.seq loopBody602_109 loopBody602_13

def loopBody602_111 : HolLoopProg 64 :=
.mark loopBody602_110

def loopBody602_112 : HolLoopProg 64 :=
.seq loopBody602_101 loopBody602_111

def loopBody602_113 : HolLoopProg 64 :=
.mark loopBody602_112

def loopBody602_114 : HolLoopProg 64 :=
.seq loopBody602_93 loopBody602_113

def loopBody602_115 : HolLoopProg 64 :=
.mark loopBody602_114

def loopBody602_116 : HolLoopProg 64 :=
.seq loopBody602_85 loopBody602_115

def loopBody602_117 : HolLoopProg 64 :=
.mark loopBody602_116

def loopBody602_118 : HolLoopProg 64 :=
.seq loopBody602_77 loopBody602_117

def loopBody602_119 : HolLoopProg 64 :=
.mark loopBody602_118

def loopBody602_120 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_119

def loopBody602_121 : HolLoopProg 64 :=
.mark loopBody602_120

def loopBody602_122 : HolLoopProg 64 :=
.seq loopBody602_75 loopBody602_121

def loopBody602_123 : HolLoopProg 64 :=
.mark loopBody602_122

def loopBody602_124 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_123

def loopBody602_125 : HolLoopProg 64 :=
.mark loopBody602_124

def loopBody602_126 : HolLoopProg 64 :=
.seq loopBody602_73 loopBody602_125

def loopBody602_127 : HolLoopProg 64 :=
.mark loopBody602_126

def loopBody602_128 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_127

def loopBody602_129 : HolLoopProg 64 :=
.mark loopBody602_128

def loopBody602_130 : HolLoopProg 64 :=
.seq loopBody602_71 loopBody602_129

def loopBody602_131 : HolLoopProg 64 :=
.mark loopBody602_130

def loopBody602_132 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_131

def loopBody602_133 : HolLoopProg 64 :=
.mark loopBody602_132

def loopBody602_134 : HolLoopProg 64 :=
.seq loopBody602_69 loopBody602_133

def loopBody602_135 : HolLoopProg 64 :=
.mark loopBody602_134

def loopBody602_136 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_135

def loopBody602_137 : HolLoopProg 64 :=
.mark loopBody602_136

def loopBody602_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 0#64)

def loopBody602_139 : HolLoopProg 64 :=
.mark loopBody602_138

def loopBody602_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [16]

def loopBody602_141 : HolLoopProg 64 :=
.mark loopBody602_140

def loopBody602_142 : HolLoopProg 64 :=
.seq loopBody602_141 loopBody602_13

def loopBody602_143 : HolLoopProg 64 :=
.mark loopBody602_142

def loopBody602_144 : HolLoopProg 64 :=
.seq loopBody602_139 loopBody602_143

def loopBody602_145 : HolLoopProg 64 :=
.mark loopBody602_144

def loopBody602_146 : HolLoopProg 64 :=
.seq loopBody602_137 loopBody602_145

def loopBody602_147 : HolLoopProg 64 :=
.mark loopBody602_146

def loopBody602_148 : HolLoopProg 64 :=
.seq loopBody602_67 loopBody602_147

def loopBody602_149 : HolLoopProg 64 :=
.mark loopBody602_148

def loopBody602_150 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_149

def loopBody602_151 : HolLoopProg 64 :=
.mark loopBody602_150

def loopBody602_152 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_151

def loopBody602_153 : HolLoopProg 64 :=
.mark loopBody602_152

def loopBody602_154 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_153

def loopBody602_155 : HolLoopProg 64 :=
.mark loopBody602_154

def loopBody602_156 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_155

def loopBody602_157 : HolLoopProg 64 :=
.mark loopBody602_156

def loopBody602_158 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_157

def loopBody602_159 : HolLoopProg 64 :=
.mark loopBody602_158

def loopBody602_160 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_159

def loopBody602_161 : HolLoopProg 64 :=
.mark loopBody602_160

def loopBody602_162 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_161

def loopBody602_163 : HolLoopProg 64 :=
.mark loopBody602_162

def loopBody602_164 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_163

def loopBody602_165 : HolLoopProg 64 :=
.mark loopBody602_164

def loopBody602_166 : HolLoopProg 64 :=
.seq loopBody602_29 loopBody602_165

def loopBody602_167 : HolLoopProg 64 :=
.mark loopBody602_166

def loopBody602_168 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_167

def loopBody602_169 : HolLoopProg 64 :=
.mark loopBody602_168

def loopBody602_170 : HolLoopProg 64 :=
.seq loopBody602_27 loopBody602_169

def loopBody602_171 : HolLoopProg 64 :=
.mark loopBody602_170

def loopBody602_172 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_171

def loopBody602_173 : HolLoopProg 64 :=
.mark loopBody602_172

def loopBody602_174 : HolLoopProg 64 :=
.seq loopBody602_25 loopBody602_173

def loopBody602_175 : HolLoopProg 64 :=
.mark loopBody602_174

def loopBody602_176 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_175

def loopBody602_177 : HolLoopProg 64 :=
.mark loopBody602_176

def loopBody602_178 : HolLoopProg 64 :=
.seq loopBody602_23 loopBody602_177

def loopBody602_179 : HolLoopProg 64 :=
.mark loopBody602_178

def loopBody602_180 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_179

def loopBody602_181 : HolLoopProg 64 :=
.mark loopBody602_180

def loopBody602_182 : HolLoopProg 64 :=
.seq loopBody602_21 loopBody602_181

def loopBody602_183 : HolLoopProg 64 :=
.mark loopBody602_182

def loopBody602_184 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_183

def loopBody602_185 : HolLoopProg 64 :=
.mark loopBody602_184

def loopBody602_186 : HolLoopProg 64 :=
.seq loopBody602_19 loopBody602_185

def loopBody602_187 : HolLoopProg 64 :=
.mark loopBody602_186

def loopBody602_188 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_187

def loopBody602_189 : HolLoopProg 64 :=
.mark loopBody602_188

def loopBody602_190 : HolLoopProg 64 :=
.seq loopBody602_17 loopBody602_189

def loopBody602_191 : HolLoopProg 64 :=
.mark loopBody602_190

def loopBody602_192 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_191

def loopBody602_193 : HolLoopProg 64 :=
.mark loopBody602_192

def loopBody602_194 : HolLoopProg 64 :=
.seq loopBody602_15 loopBody602_193

def loopBody602_195 : HolLoopProg 64 :=
.mark loopBody602_194

def loopBody602_196 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_195

def loopBody602_197 : HolLoopProg 64 :=
.mark loopBody602_196

def loopBody602_198 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody602_197 loopBody602_13 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody602_199 : HolLoopProg 64 :=
.mark loopBody602_198

def loopBody602_200 : HolLoopProg 64 :=
.seq loopBody602_199 loopBody602_13

def loopBody602_201 : HolLoopProg 64 :=
.mark loopBody602_200

def loopBody602_202 : HolLoopProg 64 :=
.seq loopBody602_11 loopBody602_201

def loopBody602_203 : HolLoopProg 64 :=
.mark loopBody602_202

def loopBody602_204 : HolLoopProg 64 :=
.seq loopBody602_9 loopBody602_203

def loopBody602_205 : HolLoopProg 64 :=
.mark loopBody602_204

def loopBody602_206 : HolLoopProg 64 :=
.seq loopBody602_3 loopBody602_205

def loopBody602_207 : HolLoopProg 64 :=
.mark loopBody602_206

def loopBody602_208 : HolLoopProg 64 :=
.seq loopBody602_1 loopBody602_207

def loopBody602_209 : HolLoopProg 64 :=
.mark loopBody602_208

def loopBody602_210 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 2#64)

def loopBody602_211 : HolLoopProg 64 :=
.mark loopBody602_210

def loopBody602_212 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody602_5 loopBody602_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody602_213 : HolLoopProg 64 :=
.mark loopBody602_212

def loopBody602_214 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody602_215 : HolLoopProg 64 :=
.mark loopBody602_214

def loopBody602_216 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody602_217 : HolLoopProg 64 :=
.mark loopBody602_216

def loopBody602_218 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody602_219 : HolLoopProg 64 :=
.mark loopBody602_218

def loopBody602_220 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody602_221 : HolLoopProg 64 :=
.mark loopBody602_220

def loopBody602_222 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 662) ([5, 6, 7]) (some (5, loopBody602_221, loopBody602_13, (Flapjack.Spt.ln)))

def loopBody602_223 : HolLoopProg 64 :=
.mark loopBody602_222

def loopBody602_224 : HolLoopProg 64 :=
.seq loopBody602_223 loopBody602_13

def loopBody602_225 : HolLoopProg 64 :=
.mark loopBody602_224

def loopBody602_226 : HolLoopProg 64 :=
.seq loopBody602_219 loopBody602_225

def loopBody602_227 : HolLoopProg 64 :=
.mark loopBody602_226

def loopBody602_228 : HolLoopProg 64 :=
.seq loopBody602_217 loopBody602_227

def loopBody602_229 : HolLoopProg 64 :=
.mark loopBody602_228

def loopBody602_230 : HolLoopProg 64 :=
.seq loopBody602_215 loopBody602_229

def loopBody602_231 : HolLoopProg 64 :=
.mark loopBody602_230

def loopBody602_232 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_231

def loopBody602_233 : HolLoopProg 64 :=
.mark loopBody602_232

def loopBody602_234 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_233

def loopBody602_235 : HolLoopProg 64 :=
.mark loopBody602_234

def loopBody602_236 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody602_237 : HolLoopProg 64 :=
.mark loopBody602_236

def loopBody602_238 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody602_239 : HolLoopProg 64 :=
.mark loopBody602_238

def loopBody602_240 : HolLoopProg 64 :=
.seq loopBody602_239 loopBody602_13

def loopBody602_241 : HolLoopProg 64 :=
.mark loopBody602_240

def loopBody602_242 : HolLoopProg 64 :=
.seq loopBody602_237 loopBody602_241

def loopBody602_243 : HolLoopProg 64 :=
.mark loopBody602_242

def loopBody602_244 : HolLoopProg 64 :=
.seq loopBody602_235 loopBody602_243

def loopBody602_245 : HolLoopProg 64 :=
.mark loopBody602_244

def loopBody602_246 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody602_245 loopBody602_13 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody602_247 : HolLoopProg 64 :=
.mark loopBody602_246

def loopBody602_248 : HolLoopProg 64 :=
.seq loopBody602_247 loopBody602_13

def loopBody602_249 : HolLoopProg 64 :=
.mark loopBody602_248

def loopBody602_250 : HolLoopProg 64 :=
.seq loopBody602_11 loopBody602_249

def loopBody602_251 : HolLoopProg 64 :=
.mark loopBody602_250

def loopBody602_252 : HolLoopProg 64 :=
.seq loopBody602_213 loopBody602_251

def loopBody602_253 : HolLoopProg 64 :=
.mark loopBody602_252

def loopBody602_254 : HolLoopProg 64 :=
.seq loopBody602_211 loopBody602_253

def loopBody602_255 : HolLoopProg 64 :=
.mark loopBody602_254

def loopBody602_256 : HolLoopProg 64 :=
.seq loopBody602_1 loopBody602_255

def loopBody602_257 : HolLoopProg 64 :=
.mark loopBody602_256

def loopBody602_258 : HolLoopProg 64 :=
.seq loopBody602_209 loopBody602_257

def loopBody602_259 : HolLoopProg 64 :=
.mark loopBody602_258

def loopBody602_260 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 664) ([5, 6, 7]) (some (5, loopBody602_221, loopBody602_13, (Flapjack.Spt.ln)))

def loopBody602_261 : HolLoopProg 64 :=
.mark loopBody602_260

def loopBody602_262 : HolLoopProg 64 :=
.seq loopBody602_261 loopBody602_13

def loopBody602_263 : HolLoopProg 64 :=
.mark loopBody602_262

def loopBody602_264 : HolLoopProg 64 :=
.seq loopBody602_219 loopBody602_263

def loopBody602_265 : HolLoopProg 64 :=
.mark loopBody602_264

def loopBody602_266 : HolLoopProg 64 :=
.seq loopBody602_217 loopBody602_265

def loopBody602_267 : HolLoopProg 64 :=
.mark loopBody602_266

def loopBody602_268 : HolLoopProg 64 :=
.seq loopBody602_215 loopBody602_267

def loopBody602_269 : HolLoopProg 64 :=
.mark loopBody602_268

def loopBody602_270 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_269

def loopBody602_271 : HolLoopProg 64 :=
.mark loopBody602_270

def loopBody602_272 : HolLoopProg 64 :=
.seq loopBody602_13 loopBody602_271

def loopBody602_273 : HolLoopProg 64 :=
.mark loopBody602_272

def loopBody602_274 : HolLoopProg 64 :=
.seq loopBody602_259 loopBody602_273

def loopBody602_275 : HolLoopProg 64 :=
.mark loopBody602_274

def loopBody602_276 : HolLoopProg 64 :=
.seq loopBody602_275 loopBody602_243

def loopBody602_277 : HolLoopProg 64 :=
.mark loopBody602_276

def output602 : Nat × List Nat × HolLoopProg 64 :=
  (666, [0, 1, 2, 3], loopBody602_277)
end InitECandidate.Proofs.FrontendStages.Loop
