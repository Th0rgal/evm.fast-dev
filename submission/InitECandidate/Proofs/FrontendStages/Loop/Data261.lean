import InitECandidate.Proofs.FrontendStages.Loop.Translate245
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody261_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody261_1 : HolLoopProg 64 :=
.mark loopBody261_0

def loopBody261_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody261_3 : HolLoopProg 64 :=
.mark loopBody261_2

def loopBody261_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody261_5 : HolLoopProg 64 :=
.mark loopBody261_4

def loopBody261_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody261_7 : HolLoopProg 64 :=
.mark loopBody261_6

def loopBody261_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody261_5 loopBody261_7 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody261_9 : HolLoopProg 64 :=
.mark loopBody261_8

def loopBody261_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody261_11 : HolLoopProg 64 :=
.mark loopBody261_10

def loopBody261_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody261_13 : HolLoopProg 64 :=
.mark loopBody261_12

def loopBody261_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 128#64)

def loopBody261_15 : HolLoopProg 64 :=
.mark loopBody261_14

def loopBody261_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 2 3

def loopBody261_17 : HolLoopProg 64 :=
.mark loopBody261_16

def loopBody261_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody261_19 : HolLoopProg 64 :=
.mark loopBody261_18

def loopBody261_20 : HolLoopProg 64 :=
.seq loopBody261_17 loopBody261_19

def loopBody261_21 : HolLoopProg 64 :=
.mark loopBody261_20

def loopBody261_22 : HolLoopProg 64 :=
.seq loopBody261_15 loopBody261_21

def loopBody261_23 : HolLoopProg 64 :=
.mark loopBody261_22

def loopBody261_24 : HolLoopProg 64 :=
.seq loopBody261_13 loopBody261_23

def loopBody261_25 : HolLoopProg 64 :=
.mark loopBody261_24

def loopBody261_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody261_27 : HolLoopProg 64 :=
.mark loopBody261_26

def loopBody261_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody261_29 : HolLoopProg 64 :=
.mark loopBody261_28

def loopBody261_30 : HolLoopProg 64 :=
.seq loopBody261_29 loopBody261_19

def loopBody261_31 : HolLoopProg 64 :=
.mark loopBody261_30

def loopBody261_32 : HolLoopProg 64 :=
.seq loopBody261_27 loopBody261_31

def loopBody261_33 : HolLoopProg 64 :=
.mark loopBody261_32

def loopBody261_34 : HolLoopProg 64 :=
.seq loopBody261_25 loopBody261_33

def loopBody261_35 : HolLoopProg 64 :=
.mark loopBody261_34

def loopBody261_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody261_35 loopBody261_19 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody261_37 : HolLoopProg 64 :=
.mark loopBody261_36

def loopBody261_38 : HolLoopProg 64 :=
.seq loopBody261_37 loopBody261_19

def loopBody261_39 : HolLoopProg 64 :=
.mark loopBody261_38

def loopBody261_40 : HolLoopProg 64 :=
.seq loopBody261_11 loopBody261_39

def loopBody261_41 : HolLoopProg 64 :=
.mark loopBody261_40

def loopBody261_42 : HolLoopProg 64 :=
.seq loopBody261_9 loopBody261_41

def loopBody261_43 : HolLoopProg 64 :=
.mark loopBody261_42

def loopBody261_44 : HolLoopProg 64 :=
.seq loopBody261_3 loopBody261_43

def loopBody261_45 : HolLoopProg 64 :=
.mark loopBody261_44

def loopBody261_46 : HolLoopProg 64 :=
.seq loopBody261_1 loopBody261_45

def loopBody261_47 : HolLoopProg 64 :=
.mark loopBody261_46

def loopBody261_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody261_49 : HolLoopProg 64 :=
.mark loopBody261_48

def loopBody261_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 160#64)

def loopBody261_51 : HolLoopProg 64 :=
.mark loopBody261_50

def loopBody261_52 : HolLoopProg 64 :=
.seq loopBody261_51 loopBody261_21

def loopBody261_53 : HolLoopProg 64 :=
.mark loopBody261_52

def loopBody261_54 : HolLoopProg 64 :=
.seq loopBody261_13 loopBody261_53

def loopBody261_55 : HolLoopProg 64 :=
.mark loopBody261_54

def loopBody261_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64])

def loopBody261_57 : HolLoopProg 64 :=
.mark loopBody261_56

def loopBody261_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 24#64]))

def loopBody261_59 : HolLoopProg 64 :=
.mark loopBody261_58

def loopBody261_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody261_61 : HolLoopProg 64 :=
.mark loopBody261_60

def loopBody261_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody261_63 : HolLoopProg 64 :=
.mark loopBody261_62

def loopBody261_64 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 77) ([3, 4, 5]) (some (3, loopBody261_63, loopBody261_19, (Flapjack.Spt.ln)))

def loopBody261_65 : HolLoopProg 64 :=
.mark loopBody261_64

def loopBody261_66 : HolLoopProg 64 :=
.seq loopBody261_65 loopBody261_19

def loopBody261_67 : HolLoopProg 64 :=
.mark loopBody261_66

def loopBody261_68 : HolLoopProg 64 :=
.seq loopBody261_61 loopBody261_67

def loopBody261_69 : HolLoopProg 64 :=
.mark loopBody261_68

def loopBody261_70 : HolLoopProg 64 :=
.seq loopBody261_59 loopBody261_69

def loopBody261_71 : HolLoopProg 64 :=
.mark loopBody261_70

def loopBody261_72 : HolLoopProg 64 :=
.seq loopBody261_57 loopBody261_71

def loopBody261_73 : HolLoopProg 64 :=
.mark loopBody261_72

def loopBody261_74 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_73

def loopBody261_75 : HolLoopProg 64 :=
.mark loopBody261_74

def loopBody261_76 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_75

def loopBody261_77 : HolLoopProg 64 :=
.mark loopBody261_76

def loopBody261_78 : HolLoopProg 64 :=
.seq loopBody261_55 loopBody261_77

def loopBody261_79 : HolLoopProg 64 :=
.mark loopBody261_78

def loopBody261_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 33#64)

def loopBody261_81 : HolLoopProg 64 :=
.mark loopBody261_80

def loopBody261_82 : HolLoopProg 64 :=
.seq loopBody261_81 loopBody261_31

def loopBody261_83 : HolLoopProg 64 :=
.mark loopBody261_82

def loopBody261_84 : HolLoopProg 64 :=
.seq loopBody261_79 loopBody261_83

def loopBody261_85 : HolLoopProg 64 :=
.mark loopBody261_84

def loopBody261_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody261_85 loopBody261_19 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody261_87 : HolLoopProg 64 :=
.mark loopBody261_86

def loopBody261_88 : HolLoopProg 64 :=
.seq loopBody261_87 loopBody261_19

def loopBody261_89 : HolLoopProg 64 :=
.mark loopBody261_88

def loopBody261_90 : HolLoopProg 64 :=
.seq loopBody261_11 loopBody261_89

def loopBody261_91 : HolLoopProg 64 :=
.mark loopBody261_90

def loopBody261_92 : HolLoopProg 64 :=
.seq loopBody261_9 loopBody261_91

def loopBody261_93 : HolLoopProg 64 :=
.mark loopBody261_92

def loopBody261_94 : HolLoopProg 64 :=
.seq loopBody261_3 loopBody261_93

def loopBody261_95 : HolLoopProg 64 :=
.mark loopBody261_94

def loopBody261_96 : HolLoopProg 64 :=
.seq loopBody261_49 loopBody261_95

def loopBody261_97 : HolLoopProg 64 :=
.mark loopBody261_96

def loopBody261_98 : HolLoopProg 64 :=
.seq loopBody261_47 loopBody261_97

def loopBody261_99 : HolLoopProg 64 :=
.mark loopBody261_98

def loopBody261_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody261_101 : HolLoopProg 64 :=
.mark loopBody261_100

def loopBody261_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 13#64)

def loopBody261_103 : HolLoopProg 64 :=
.mark loopBody261_102

def loopBody261_104 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 282) ([3]) (some (3, loopBody261_63, loopBody261_19, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody261_105 : HolLoopProg 64 :=
.mark loopBody261_104

def loopBody261_106 : HolLoopProg 64 :=
.seq loopBody261_105 loopBody261_19

def loopBody261_107 : HolLoopProg 64 :=
.mark loopBody261_106

def loopBody261_108 : HolLoopProg 64 :=
.seq loopBody261_103 loopBody261_107

def loopBody261_109 : HolLoopProg 64 :=
.mark loopBody261_108

def loopBody261_110 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_109

def loopBody261_111 : HolLoopProg 64 :=
.mark loopBody261_110

def loopBody261_112 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_111

def loopBody261_113 : HolLoopProg 64 :=
.mark loopBody261_112

def loopBody261_114 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody261_113 loopBody261_19 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody261_115 : HolLoopProg 64 :=
.mark loopBody261_114

def loopBody261_116 : HolLoopProg 64 :=
.seq loopBody261_115 loopBody261_19

def loopBody261_117 : HolLoopProg 64 :=
.mark loopBody261_116

def loopBody261_118 : HolLoopProg 64 :=
.seq loopBody261_11 loopBody261_117

def loopBody261_119 : HolLoopProg 64 :=
.mark loopBody261_118

def loopBody261_120 : HolLoopProg 64 :=
.seq loopBody261_9 loopBody261_119

def loopBody261_121 : HolLoopProg 64 :=
.mark loopBody261_120

def loopBody261_122 : HolLoopProg 64 :=
.seq loopBody261_3 loopBody261_121

def loopBody261_123 : HolLoopProg 64 :=
.mark loopBody261_122

def loopBody261_124 : HolLoopProg 64 :=
.seq loopBody261_101 loopBody261_123

def loopBody261_125 : HolLoopProg 64 :=
.mark loopBody261_124

def loopBody261_126 : HolLoopProg 64 :=
.seq loopBody261_99 loopBody261_125

def loopBody261_127 : HolLoopProg 64 :=
.mark loopBody261_126

def loopBody261_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody261_129 : HolLoopProg 64 :=
.mark loopBody261_128

def loopBody261_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody261_131 : HolLoopProg 64 :=
.mark loopBody261_130

def loopBody261_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 32#64)

def loopBody261_133 : HolLoopProg 64 :=
.mark loopBody261_132

def loopBody261_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody261_135 : HolLoopProg 64 :=
.mark loopBody261_134

def loopBody261_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody261_137 : HolLoopProg 64 :=
.mark loopBody261_136

def loopBody261_138 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 5 (Flapjack.RegImm.reg 6) loopBody261_135 loopBody261_137 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody261_139 : HolLoopProg 64 :=
.mark loopBody261_138

def loopBody261_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody261_141 : HolLoopProg 64 :=
.mark loopBody261_140

def loopBody261_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody261_143 : HolLoopProg 64 :=
.mark loopBody261_142

def loopBody261_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody261_145 : HolLoopProg 64 :=
.mark loopBody261_144

def loopBody261_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody261_147 : HolLoopProg 64 :=
.mark loopBody261_146

def loopBody261_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody261_149 : HolLoopProg 64 :=
.mark loopBody261_148

def loopBody261_150 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([5, 6, 7]) (some (5, loopBody261_149, loopBody261_19, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody261_151 : HolLoopProg 64 :=
.mark loopBody261_150

def loopBody261_152 : HolLoopProg 64 :=
.seq loopBody261_151 loopBody261_19

def loopBody261_153 : HolLoopProg 64 :=
.mark loopBody261_152

def loopBody261_154 : HolLoopProg 64 :=
.seq loopBody261_147 loopBody261_153

def loopBody261_155 : HolLoopProg 64 :=
.mark loopBody261_154

def loopBody261_156 : HolLoopProg 64 :=
.seq loopBody261_145 loopBody261_155

def loopBody261_157 : HolLoopProg 64 :=
.mark loopBody261_156

def loopBody261_158 : HolLoopProg 64 :=
.seq loopBody261_143 loopBody261_157

def loopBody261_159 : HolLoopProg 64 :=
.mark loopBody261_158

def loopBody261_160 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_159

def loopBody261_161 : HolLoopProg 64 :=
.mark loopBody261_160

def loopBody261_162 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_161

def loopBody261_163 : HolLoopProg 64 :=
.mark loopBody261_162

def loopBody261_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody261_165 : HolLoopProg 64 :=
.mark loopBody261_164

def loopBody261_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody261_167 : HolLoopProg 64 :=
.mark loopBody261_166

def loopBody261_168 : HolLoopProg 64 :=
.seq loopBody261_167 loopBody261_19

def loopBody261_169 : HolLoopProg 64 :=
.mark loopBody261_168

def loopBody261_170 : HolLoopProg 64 :=
.seq loopBody261_165 loopBody261_169

def loopBody261_171 : HolLoopProg 64 :=
.mark loopBody261_170

def loopBody261_172 : HolLoopProg 64 :=
.seq loopBody261_163 loopBody261_171

def loopBody261_173 : HolLoopProg 64 :=
.mark loopBody261_172

def loopBody261_174 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody261_173 loopBody261_19 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody261_175 : HolLoopProg 64 :=
.mark loopBody261_174

def loopBody261_176 : HolLoopProg 64 :=
.seq loopBody261_175 loopBody261_19

def loopBody261_177 : HolLoopProg 64 :=
.mark loopBody261_176

def loopBody261_178 : HolLoopProg 64 :=
.seq loopBody261_141 loopBody261_177

def loopBody261_179 : HolLoopProg 64 :=
.mark loopBody261_178

def loopBody261_180 : HolLoopProg 64 :=
.seq loopBody261_139 loopBody261_179

def loopBody261_181 : HolLoopProg 64 :=
.mark loopBody261_180

def loopBody261_182 : HolLoopProg 64 :=
.seq loopBody261_133 loopBody261_181

def loopBody261_183 : HolLoopProg 64 :=
.mark loopBody261_182

def loopBody261_184 : HolLoopProg 64 :=
.seq loopBody261_11 loopBody261_183

def loopBody261_185 : HolLoopProg 64 :=
.mark loopBody261_184

def loopBody261_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody261_187 : HolLoopProg 64 :=
.mark loopBody261_186

def loopBody261_188 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 324) ([5]) (some (5, loopBody261_149, loopBody261_19, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))

def loopBody261_189 : HolLoopProg 64 :=
.mark loopBody261_188

def loopBody261_190 : HolLoopProg 64 :=
.seq loopBody261_189 loopBody261_19

def loopBody261_191 : HolLoopProg 64 :=
.mark loopBody261_190

def loopBody261_192 : HolLoopProg 64 :=
.seq loopBody261_187 loopBody261_191

def loopBody261_193 : HolLoopProg 64 :=
.mark loopBody261_192

def loopBody261_194 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 160#64)

def loopBody261_195 : HolLoopProg 64 :=
.mark loopBody261_194

def loopBody261_196 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 5 6

def loopBody261_197 : HolLoopProg 64 :=
.mark loopBody261_196

def loopBody261_198 : HolLoopProg 64 :=
.seq loopBody261_197 loopBody261_19

def loopBody261_199 : HolLoopProg 64 :=
.mark loopBody261_198

def loopBody261_200 : HolLoopProg 64 :=
.seq loopBody261_195 loopBody261_199

def loopBody261_201 : HolLoopProg 64 :=
.mark loopBody261_200

def loopBody261_202 : HolLoopProg 64 :=
.seq loopBody261_143 loopBody261_201

def loopBody261_203 : HolLoopProg 64 :=
.mark loopBody261_202

def loopBody261_204 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64])

def loopBody261_205 : HolLoopProg 64 :=
.mark loopBody261_204

def loopBody261_206 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody261_207 : HolLoopProg 64 :=
.mark loopBody261_206

def loopBody261_208 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 32#64)

def loopBody261_209 : HolLoopProg 64 :=
.mark loopBody261_208

def loopBody261_210 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody261_211 : HolLoopProg 64 :=
.mark loopBody261_210

def loopBody261_212 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 77) ([6, 7, 8]) (some (6, loopBody261_211, loopBody261_19, (Flapjack.Spt.ln)))

def loopBody261_213 : HolLoopProg 64 :=
.mark loopBody261_212

def loopBody261_214 : HolLoopProg 64 :=
.seq loopBody261_213 loopBody261_19

def loopBody261_215 : HolLoopProg 64 :=
.mark loopBody261_214

def loopBody261_216 : HolLoopProg 64 :=
.seq loopBody261_209 loopBody261_215

def loopBody261_217 : HolLoopProg 64 :=
.mark loopBody261_216

def loopBody261_218 : HolLoopProg 64 :=
.seq loopBody261_207 loopBody261_217

def loopBody261_219 : HolLoopProg 64 :=
.mark loopBody261_218

def loopBody261_220 : HolLoopProg 64 :=
.seq loopBody261_205 loopBody261_219

def loopBody261_221 : HolLoopProg 64 :=
.mark loopBody261_220

def loopBody261_222 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_221

def loopBody261_223 : HolLoopProg 64 :=
.mark loopBody261_222

def loopBody261_224 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_223

def loopBody261_225 : HolLoopProg 64 :=
.mark loopBody261_224

def loopBody261_226 : HolLoopProg 64 :=
.seq loopBody261_203 loopBody261_225

def loopBody261_227 : HolLoopProg 64 :=
.mark loopBody261_226

def loopBody261_228 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 33#64)

def loopBody261_229 : HolLoopProg 64 :=
.mark loopBody261_228

def loopBody261_230 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody261_231 : HolLoopProg 64 :=
.mark loopBody261_230

def loopBody261_232 : HolLoopProg 64 :=
.seq loopBody261_231 loopBody261_19

def loopBody261_233 : HolLoopProg 64 :=
.mark loopBody261_232

def loopBody261_234 : HolLoopProg 64 :=
.seq loopBody261_229 loopBody261_233

def loopBody261_235 : HolLoopProg 64 :=
.mark loopBody261_234

def loopBody261_236 : HolLoopProg 64 :=
.seq loopBody261_227 loopBody261_235

def loopBody261_237 : HolLoopProg 64 :=
.mark loopBody261_236

def loopBody261_238 : HolLoopProg 64 :=
.seq loopBody261_193 loopBody261_237

def loopBody261_239 : HolLoopProg 64 :=
.mark loopBody261_238

def loopBody261_240 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_239

def loopBody261_241 : HolLoopProg 64 :=
.mark loopBody261_240

def loopBody261_242 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_241

def loopBody261_243 : HolLoopProg 64 :=
.mark loopBody261_242

def loopBody261_244 : HolLoopProg 64 :=
.seq loopBody261_185 loopBody261_243

def loopBody261_245 : HolLoopProg 64 :=
.mark loopBody261_244

def loopBody261_246 : HolLoopProg 64 :=
.seq loopBody261_131 loopBody261_245

def loopBody261_247 : HolLoopProg 64 :=
.mark loopBody261_246

def loopBody261_248 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_247

def loopBody261_249 : HolLoopProg 64 :=
.mark loopBody261_248

def loopBody261_250 : HolLoopProg 64 :=
.seq loopBody261_129 loopBody261_249

def loopBody261_251 : HolLoopProg 64 :=
.mark loopBody261_250

def loopBody261_252 : HolLoopProg 64 :=
.seq loopBody261_19 loopBody261_251

def loopBody261_253 : HolLoopProg 64 :=
.mark loopBody261_252

def loopBody261_254 : HolLoopProg 64 :=
.seq loopBody261_127 loopBody261_253

def loopBody261_255 : HolLoopProg 64 :=
.mark loopBody261_254

def output261 : Nat × List Nat × HolLoopProg 64 :=
  (325, [0, 1], loopBody261_255)
end InitECandidate.Proofs.FrontendStages.Loop
