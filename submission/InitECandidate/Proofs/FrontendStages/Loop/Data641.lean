import InitECandidate.Proofs.FrontendStages.Loop.Translate625
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody641_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody641_1 : HolLoopProg 64 :=
.mark loopBody641_0

def loopBody641_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 0)

def loopBody641_3 : HolLoopProg 64 :=
.mark loopBody641_2

def loopBody641_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 6,
      Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 0#64, Flapjack.HolLoopExp.const 1#64]])

def loopBody641_5 : HolLoopProg 64 :=
.mark loopBody641_4

def loopBody641_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 1#64)

def loopBody641_7 : HolLoopProg 64 :=
.mark loopBody641_6

def loopBody641_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.primitive [12, 13] Flapjack.PrimOp.addCarry [14, 15, 16]

def loopBody641_9 : HolLoopProg 64 :=
.mark loopBody641_8

def loopBody641_10 : HolLoopProg 64 :=
.seq loopBody641_7 loopBody641_9

def loopBody641_11 : HolLoopProg 64 :=
.mark loopBody641_10

def loopBody641_12 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_11

def loopBody641_13 : HolLoopProg 64 :=
.mark loopBody641_12

def loopBody641_14 : HolLoopProg 64 :=
.seq loopBody641_5 loopBody641_13

def loopBody641_15 : HolLoopProg 64 :=
.mark loopBody641_14

def loopBody641_16 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_15

def loopBody641_17 : HolLoopProg 64 :=
.mark loopBody641_16

def loopBody641_18 : HolLoopProg 64 :=
.seq loopBody641_3 loopBody641_17

def loopBody641_19 : HolLoopProg 64 :=
.mark loopBody641_18

def loopBody641_20 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_19

def loopBody641_21 : HolLoopProg 64 :=
.mark loopBody641_20

def loopBody641_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 1)

def loopBody641_23 : HolLoopProg 64 :=
.mark loopBody641_22

def loopBody641_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 7,
      Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 0#64, Flapjack.HolLoopExp.const 1#64]])

def loopBody641_25 : HolLoopProg 64 :=
.mark loopBody641_24

def loopBody641_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 13)

def loopBody641_27 : HolLoopProg 64 :=
.mark loopBody641_26

def loopBody641_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.primitive [14, 15] Flapjack.PrimOp.addCarry [16, 17, 18]

def loopBody641_29 : HolLoopProg 64 :=
.mark loopBody641_28

def loopBody641_30 : HolLoopProg 64 :=
.seq loopBody641_27 loopBody641_29

def loopBody641_31 : HolLoopProg 64 :=
.mark loopBody641_30

def loopBody641_32 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_31

def loopBody641_33 : HolLoopProg 64 :=
.mark loopBody641_32

def loopBody641_34 : HolLoopProg 64 :=
.seq loopBody641_25 loopBody641_33

def loopBody641_35 : HolLoopProg 64 :=
.mark loopBody641_34

def loopBody641_36 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_35

def loopBody641_37 : HolLoopProg 64 :=
.mark loopBody641_36

def loopBody641_38 : HolLoopProg 64 :=
.seq loopBody641_23 loopBody641_37

def loopBody641_39 : HolLoopProg 64 :=
.mark loopBody641_38

def loopBody641_40 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_39

def loopBody641_41 : HolLoopProg 64 :=
.mark loopBody641_40

def loopBody641_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 2)

def loopBody641_43 : HolLoopProg 64 :=
.mark loopBody641_42

def loopBody641_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 8,
      Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 0#64, Flapjack.HolLoopExp.const 1#64]])

def loopBody641_45 : HolLoopProg 64 :=
.mark loopBody641_44

def loopBody641_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 15)

def loopBody641_47 : HolLoopProg 64 :=
.mark loopBody641_46

def loopBody641_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.primitive [16, 17] Flapjack.PrimOp.addCarry [18, 19, 20]

def loopBody641_49 : HolLoopProg 64 :=
.mark loopBody641_48

def loopBody641_50 : HolLoopProg 64 :=
.seq loopBody641_47 loopBody641_49

def loopBody641_51 : HolLoopProg 64 :=
.mark loopBody641_50

def loopBody641_52 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_51

def loopBody641_53 : HolLoopProg 64 :=
.mark loopBody641_52

def loopBody641_54 : HolLoopProg 64 :=
.seq loopBody641_45 loopBody641_53

def loopBody641_55 : HolLoopProg 64 :=
.mark loopBody641_54

def loopBody641_56 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_55

def loopBody641_57 : HolLoopProg 64 :=
.mark loopBody641_56

def loopBody641_58 : HolLoopProg 64 :=
.seq loopBody641_43 loopBody641_57

def loopBody641_59 : HolLoopProg 64 :=
.mark loopBody641_58

def loopBody641_60 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_59

def loopBody641_61 : HolLoopProg 64 :=
.mark loopBody641_60

def loopBody641_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 3)

def loopBody641_63 : HolLoopProg 64 :=
.mark loopBody641_62

def loopBody641_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 9,
      Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 0#64, Flapjack.HolLoopExp.const 1#64]])

def loopBody641_65 : HolLoopProg 64 :=
.mark loopBody641_64

def loopBody641_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 17)

def loopBody641_67 : HolLoopProg 64 :=
.mark loopBody641_66

def loopBody641_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.primitive [18, 19] Flapjack.PrimOp.addCarry [20, 21, 22]

def loopBody641_69 : HolLoopProg 64 :=
.mark loopBody641_68

def loopBody641_70 : HolLoopProg 64 :=
.seq loopBody641_67 loopBody641_69

def loopBody641_71 : HolLoopProg 64 :=
.mark loopBody641_70

def loopBody641_72 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_71

def loopBody641_73 : HolLoopProg 64 :=
.mark loopBody641_72

def loopBody641_74 : HolLoopProg 64 :=
.seq loopBody641_65 loopBody641_73

def loopBody641_75 : HolLoopProg 64 :=
.mark loopBody641_74

def loopBody641_76 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_75

def loopBody641_77 : HolLoopProg 64 :=
.mark loopBody641_76

def loopBody641_78 : HolLoopProg 64 :=
.seq loopBody641_63 loopBody641_77

def loopBody641_79 : HolLoopProg 64 :=
.mark loopBody641_78

def loopBody641_80 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_79

def loopBody641_81 : HolLoopProg 64 :=
.mark loopBody641_80

def loopBody641_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 4)

def loopBody641_83 : HolLoopProg 64 :=
.mark loopBody641_82

def loopBody641_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 23
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 10,
      Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 0#64, Flapjack.HolLoopExp.const 1#64]])

def loopBody641_85 : HolLoopProg 64 :=
.mark loopBody641_84

def loopBody641_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 24 (Flapjack.HolLoopExp.var 19)

def loopBody641_87 : HolLoopProg 64 :=
.mark loopBody641_86

def loopBody641_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.primitive [20, 21] Flapjack.PrimOp.addCarry [22, 23, 24]

def loopBody641_89 : HolLoopProg 64 :=
.mark loopBody641_88

def loopBody641_90 : HolLoopProg 64 :=
.seq loopBody641_87 loopBody641_89

def loopBody641_91 : HolLoopProg 64 :=
.mark loopBody641_90

def loopBody641_92 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_91

def loopBody641_93 : HolLoopProg 64 :=
.mark loopBody641_92

def loopBody641_94 : HolLoopProg 64 :=
.seq loopBody641_85 loopBody641_93

def loopBody641_95 : HolLoopProg 64 :=
.mark loopBody641_94

def loopBody641_96 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_95

def loopBody641_97 : HolLoopProg 64 :=
.mark loopBody641_96

def loopBody641_98 : HolLoopProg 64 :=
.seq loopBody641_83 loopBody641_97

def loopBody641_99 : HolLoopProg 64 :=
.mark loopBody641_98

def loopBody641_100 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_99

def loopBody641_101 : HolLoopProg 64 :=
.mark loopBody641_100

def loopBody641_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 24 (Flapjack.HolLoopExp.var 5)

def loopBody641_103 : HolLoopProg 64 :=
.mark loopBody641_102

def loopBody641_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 25
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 11,
      Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 0#64, Flapjack.HolLoopExp.const 1#64]])

def loopBody641_105 : HolLoopProg 64 :=
.mark loopBody641_104

def loopBody641_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 26 (Flapjack.HolLoopExp.var 21)

def loopBody641_107 : HolLoopProg 64 :=
.mark loopBody641_106

def loopBody641_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.primitive [22, 23] Flapjack.PrimOp.addCarry [24, 25, 26]

def loopBody641_109 : HolLoopProg 64 :=
.mark loopBody641_108

def loopBody641_110 : HolLoopProg 64 :=
.seq loopBody641_107 loopBody641_109

def loopBody641_111 : HolLoopProg 64 :=
.mark loopBody641_110

def loopBody641_112 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_111

def loopBody641_113 : HolLoopProg 64 :=
.mark loopBody641_112

def loopBody641_114 : HolLoopProg 64 :=
.seq loopBody641_105 loopBody641_113

def loopBody641_115 : HolLoopProg 64 :=
.mark loopBody641_114

def loopBody641_116 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_115

def loopBody641_117 : HolLoopProg 64 :=
.mark loopBody641_116

def loopBody641_118 : HolLoopProg 64 :=
.seq loopBody641_103 loopBody641_117

def loopBody641_119 : HolLoopProg 64 :=
.mark loopBody641_118

def loopBody641_120 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_119

def loopBody641_121 : HolLoopProg 64 :=
.mark loopBody641_120

def loopBody641_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 24 (Flapjack.HolLoopExp.var 12)

def loopBody641_123 : HolLoopProg 64 :=
.mark loopBody641_122

def loopBody641_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 25 (Flapjack.HolLoopExp.var 14)

def loopBody641_125 : HolLoopProg 64 :=
.mark loopBody641_124

def loopBody641_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 26 (Flapjack.HolLoopExp.var 16)

def loopBody641_127 : HolLoopProg 64 :=
.mark loopBody641_126

def loopBody641_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 27 (Flapjack.HolLoopExp.var 18)

def loopBody641_129 : HolLoopProg 64 :=
.mark loopBody641_128

def loopBody641_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 28 (Flapjack.HolLoopExp.var 20)

def loopBody641_131 : HolLoopProg 64 :=
.mark loopBody641_130

def loopBody641_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 29 (Flapjack.HolLoopExp.var 22)

def loopBody641_133 : HolLoopProg 64 :=
.mark loopBody641_132

def loopBody641_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 30 (Flapjack.HolLoopExp.var 23)

def loopBody641_135 : HolLoopProg 64 :=
.mark loopBody641_134

def loopBody641_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [24, 25, 26, 27, 28, 29, 30]

def loopBody641_137 : HolLoopProg 64 :=
.mark loopBody641_136

def loopBody641_138 : HolLoopProg 64 :=
.seq loopBody641_137 loopBody641_1

def loopBody641_139 : HolLoopProg 64 :=
.mark loopBody641_138

def loopBody641_140 : HolLoopProg 64 :=
.seq loopBody641_135 loopBody641_139

def loopBody641_141 : HolLoopProg 64 :=
.mark loopBody641_140

def loopBody641_142 : HolLoopProg 64 :=
.seq loopBody641_133 loopBody641_141

def loopBody641_143 : HolLoopProg 64 :=
.mark loopBody641_142

def loopBody641_144 : HolLoopProg 64 :=
.seq loopBody641_131 loopBody641_143

def loopBody641_145 : HolLoopProg 64 :=
.mark loopBody641_144

def loopBody641_146 : HolLoopProg 64 :=
.seq loopBody641_129 loopBody641_145

def loopBody641_147 : HolLoopProg 64 :=
.mark loopBody641_146

def loopBody641_148 : HolLoopProg 64 :=
.seq loopBody641_127 loopBody641_147

def loopBody641_149 : HolLoopProg 64 :=
.mark loopBody641_148

def loopBody641_150 : HolLoopProg 64 :=
.seq loopBody641_125 loopBody641_149

def loopBody641_151 : HolLoopProg 64 :=
.mark loopBody641_150

def loopBody641_152 : HolLoopProg 64 :=
.seq loopBody641_123 loopBody641_151

def loopBody641_153 : HolLoopProg 64 :=
.mark loopBody641_152

def loopBody641_154 : HolLoopProg 64 :=
.seq loopBody641_121 loopBody641_153

def loopBody641_155 : HolLoopProg 64 :=
.mark loopBody641_154

def loopBody641_156 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_155

def loopBody641_157 : HolLoopProg 64 :=
.mark loopBody641_156

def loopBody641_158 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_157

def loopBody641_159 : HolLoopProg 64 :=
.mark loopBody641_158

def loopBody641_160 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_159

def loopBody641_161 : HolLoopProg 64 :=
.mark loopBody641_160

def loopBody641_162 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_161

def loopBody641_163 : HolLoopProg 64 :=
.mark loopBody641_162

def loopBody641_164 : HolLoopProg 64 :=
.seq loopBody641_101 loopBody641_163

def loopBody641_165 : HolLoopProg 64 :=
.mark loopBody641_164

def loopBody641_166 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_165

def loopBody641_167 : HolLoopProg 64 :=
.mark loopBody641_166

def loopBody641_168 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_167

def loopBody641_169 : HolLoopProg 64 :=
.mark loopBody641_168

def loopBody641_170 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_169

def loopBody641_171 : HolLoopProg 64 :=
.mark loopBody641_170

def loopBody641_172 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_171

def loopBody641_173 : HolLoopProg 64 :=
.mark loopBody641_172

def loopBody641_174 : HolLoopProg 64 :=
.seq loopBody641_81 loopBody641_173

def loopBody641_175 : HolLoopProg 64 :=
.mark loopBody641_174

def loopBody641_176 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_175

def loopBody641_177 : HolLoopProg 64 :=
.mark loopBody641_176

def loopBody641_178 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_177

def loopBody641_179 : HolLoopProg 64 :=
.mark loopBody641_178

def loopBody641_180 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_179

def loopBody641_181 : HolLoopProg 64 :=
.mark loopBody641_180

def loopBody641_182 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_181

def loopBody641_183 : HolLoopProg 64 :=
.mark loopBody641_182

def loopBody641_184 : HolLoopProg 64 :=
.seq loopBody641_61 loopBody641_183

def loopBody641_185 : HolLoopProg 64 :=
.mark loopBody641_184

def loopBody641_186 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_185

def loopBody641_187 : HolLoopProg 64 :=
.mark loopBody641_186

def loopBody641_188 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_187

def loopBody641_189 : HolLoopProg 64 :=
.mark loopBody641_188

def loopBody641_190 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_189

def loopBody641_191 : HolLoopProg 64 :=
.mark loopBody641_190

def loopBody641_192 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_191

def loopBody641_193 : HolLoopProg 64 :=
.mark loopBody641_192

def loopBody641_194 : HolLoopProg 64 :=
.seq loopBody641_41 loopBody641_193

def loopBody641_195 : HolLoopProg 64 :=
.mark loopBody641_194

def loopBody641_196 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_195

def loopBody641_197 : HolLoopProg 64 :=
.mark loopBody641_196

def loopBody641_198 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_197

def loopBody641_199 : HolLoopProg 64 :=
.mark loopBody641_198

def loopBody641_200 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_199

def loopBody641_201 : HolLoopProg 64 :=
.mark loopBody641_200

def loopBody641_202 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_201

def loopBody641_203 : HolLoopProg 64 :=
.mark loopBody641_202

def loopBody641_204 : HolLoopProg 64 :=
.seq loopBody641_21 loopBody641_203

def loopBody641_205 : HolLoopProg 64 :=
.mark loopBody641_204

def loopBody641_206 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_205

def loopBody641_207 : HolLoopProg 64 :=
.mark loopBody641_206

def loopBody641_208 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_207

def loopBody641_209 : HolLoopProg 64 :=
.mark loopBody641_208

def loopBody641_210 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_209

def loopBody641_211 : HolLoopProg 64 :=
.mark loopBody641_210

def loopBody641_212 : HolLoopProg 64 :=
.seq loopBody641_1 loopBody641_211

def loopBody641_213 : HolLoopProg 64 :=
.mark loopBody641_212

def output641 : Nat × List Nat × HolLoopProg 64 :=
  (705, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], loopBody641_213)
end InitECandidate.Proofs.FrontendStages.Loop
