import InitECandidate.Proofs.FrontendStages.Loop.Translate739
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody755_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody755_1 : HolLoopProg 64 :=
.mark loopBody755_0

def loopBody755_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody755_3 : HolLoopProg 64 :=
.mark loopBody755_2

def loopBody755_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64]))

def loopBody755_5 : HolLoopProg 64 :=
.mark loopBody755_4

def loopBody755_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody755_7 : HolLoopProg 64 :=
.mark loopBody755_6

def loopBody755_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 512#64)

def loopBody755_9 : HolLoopProg 64 :=
.mark loopBody755_8

def loopBody755_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody755_11 : HolLoopProg 64 :=
.mark loopBody755_10

def loopBody755_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody755_13 : HolLoopProg 64 :=
.mark loopBody755_12

def loopBody755_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody755_11 loopBody755_13 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody755_15 : HolLoopProg 64 :=
.mark loopBody755_14

def loopBody755_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody755_17 : HolLoopProg 64 :=
.mark loopBody755_16

def loopBody755_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 10#64)

def loopBody755_19 : HolLoopProg 64 :=
.mark loopBody755_18

def loopBody755_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody755_21 : HolLoopProg 64 :=
.mark loopBody755_20

def loopBody755_22 : HolLoopProg 64 :=
.seq loopBody755_21 loopBody755_1

def loopBody755_23 : HolLoopProg 64 :=
.mark loopBody755_22

def loopBody755_24 : HolLoopProg 64 :=
.seq loopBody755_23 loopBody755_1

def loopBody755_25 : HolLoopProg 64 :=
.mark loopBody755_24

def loopBody755_26 : HolLoopProg 64 :=
.seq loopBody755_19 loopBody755_25

def loopBody755_27 : HolLoopProg 64 :=
.mark loopBody755_26

def loopBody755_28 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_27

def loopBody755_29 : HolLoopProg 64 :=
.mark loopBody755_28

def loopBody755_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 8#64)

def loopBody755_31 : HolLoopProg 64 :=
.mark loopBody755_30

def loopBody755_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody755_33 : HolLoopProg 64 :=
.mark loopBody755_32

def loopBody755_34 : HolLoopProg 64 :=
.seq loopBody755_31 loopBody755_33

def loopBody755_35 : HolLoopProg 64 :=
.mark loopBody755_34

def loopBody755_36 : HolLoopProg 64 :=
.seq loopBody755_29 loopBody755_35

def loopBody755_37 : HolLoopProg 64 :=
.mark loopBody755_36

def loopBody755_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody755_37 loopBody755_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody755_39 : HolLoopProg 64 :=
.mark loopBody755_38

def loopBody755_40 : HolLoopProg 64 :=
.seq loopBody755_39 loopBody755_1

def loopBody755_41 : HolLoopProg 64 :=
.mark loopBody755_40

def loopBody755_42 : HolLoopProg 64 :=
.seq loopBody755_17 loopBody755_41

def loopBody755_43 : HolLoopProg 64 :=
.mark loopBody755_42

def loopBody755_44 : HolLoopProg 64 :=
.seq loopBody755_15 loopBody755_43

def loopBody755_45 : HolLoopProg 64 :=
.mark loopBody755_44

def loopBody755_46 : HolLoopProg 64 :=
.seq loopBody755_9 loopBody755_45

def loopBody755_47 : HolLoopProg 64 :=
.mark loopBody755_46

def loopBody755_48 : HolLoopProg 64 :=
.seq loopBody755_7 loopBody755_47

def loopBody755_49 : HolLoopProg 64 :=
.mark loopBody755_48

def loopBody755_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 600#64)

def loopBody755_51 : HolLoopProg 64 :=
.mark loopBody755_50

def loopBody755_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody755_53 : HolLoopProg 64 :=
.mark loopBody755_52

def loopBody755_54 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 466) ([4]) (some (4, loopBody755_53, loopBody755_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody755_55 : HolLoopProg 64 :=
.mark loopBody755_54

def loopBody755_56 : HolLoopProg 64 :=
.seq loopBody755_55 loopBody755_1

def loopBody755_57 : HolLoopProg 64 :=
.mark loopBody755_56

def loopBody755_58 : HolLoopProg 64 :=
.seq loopBody755_51 loopBody755_57

def loopBody755_59 : HolLoopProg 64 :=
.mark loopBody755_58

def loopBody755_60 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_59

def loopBody755_61 : HolLoopProg 64 :=
.mark loopBody755_60

def loopBody755_62 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_61

def loopBody755_63 : HolLoopProg 64 :=
.mark loopBody755_62

def loopBody755_64 : HolLoopProg 64 :=
.seq loopBody755_49 loopBody755_63

def loopBody755_65 : HolLoopProg 64 :=
.mark loopBody755_64

def loopBody755_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 256#64)

def loopBody755_67 : HolLoopProg 64 :=
.mark loopBody755_66

def loopBody755_68 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody755_53, loopBody755_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody755_69 : HolLoopProg 64 :=
.mark loopBody755_68

def loopBody755_70 : HolLoopProg 64 :=
.seq loopBody755_69 loopBody755_1

def loopBody755_71 : HolLoopProg 64 :=
.mark loopBody755_70

def loopBody755_72 : HolLoopProg 64 :=
.seq loopBody755_67 loopBody755_71

def loopBody755_73 : HolLoopProg 64 :=
.mark loopBody755_72

def loopBody755_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 88#64]))

def loopBody755_75 : HolLoopProg 64 :=
.mark loopBody755_74

def loopBody755_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody755_77 : HolLoopProg 64 :=
.mark loopBody755_76

def loopBody755_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody755_79 : HolLoopProg 64 :=
.mark loopBody755_78

def loopBody755_80 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 808) ([5, 6]) (some (5, loopBody755_79, loopBody755_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody755_81 : HolLoopProg 64 :=
.mark loopBody755_80

def loopBody755_82 : HolLoopProg 64 :=
.seq loopBody755_81 loopBody755_1

def loopBody755_83 : HolLoopProg 64 :=
.mark loopBody755_82

def loopBody755_84 : HolLoopProg 64 :=
.seq loopBody755_77 loopBody755_83

def loopBody755_85 : HolLoopProg 64 :=
.mark loopBody755_84

def loopBody755_86 : HolLoopProg 64 :=
.seq loopBody755_75 loopBody755_85

def loopBody755_87 : HolLoopProg 64 :=
.mark loopBody755_86

def loopBody755_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody755_89 : HolLoopProg 64 :=
.mark loopBody755_88

def loopBody755_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody755_91 : HolLoopProg 64 :=
.mark loopBody755_90

def loopBody755_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody755_93 : HolLoopProg 64 :=
.mark loopBody755_92

def loopBody755_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody755_91 loopBody755_93 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody755_95 : HolLoopProg 64 :=
.mark loopBody755_94

def loopBody755_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody755_97 : HolLoopProg 64 :=
.mark loopBody755_96

def loopBody755_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 10#64)

def loopBody755_99 : HolLoopProg 64 :=
.mark loopBody755_98

def loopBody755_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 5)

def loopBody755_101 : HolLoopProg 64 :=
.mark loopBody755_100

def loopBody755_102 : HolLoopProg 64 :=
.seq loopBody755_101 loopBody755_1

def loopBody755_103 : HolLoopProg 64 :=
.mark loopBody755_102

def loopBody755_104 : HolLoopProg 64 :=
.seq loopBody755_103 loopBody755_1

def loopBody755_105 : HolLoopProg 64 :=
.mark loopBody755_104

def loopBody755_106 : HolLoopProg 64 :=
.seq loopBody755_99 loopBody755_105

def loopBody755_107 : HolLoopProg 64 :=
.mark loopBody755_106

def loopBody755_108 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_107

def loopBody755_109 : HolLoopProg 64 :=
.mark loopBody755_108

def loopBody755_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 8#64)

def loopBody755_111 : HolLoopProg 64 :=
.mark loopBody755_110

def loopBody755_112 : HolLoopProg 64 :=
.seq loopBody755_111 loopBody755_79

def loopBody755_113 : HolLoopProg 64 :=
.mark loopBody755_112

def loopBody755_114 : HolLoopProg 64 :=
.seq loopBody755_109 loopBody755_113

def loopBody755_115 : HolLoopProg 64 :=
.mark loopBody755_114

def loopBody755_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody755_115 loopBody755_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody755_117 : HolLoopProg 64 :=
.mark loopBody755_116

def loopBody755_118 : HolLoopProg 64 :=
.seq loopBody755_117 loopBody755_1

def loopBody755_119 : HolLoopProg 64 :=
.mark loopBody755_118

def loopBody755_120 : HolLoopProg 64 :=
.seq loopBody755_97 loopBody755_119

def loopBody755_121 : HolLoopProg 64 :=
.mark loopBody755_120

def loopBody755_122 : HolLoopProg 64 :=
.seq loopBody755_95 loopBody755_121

def loopBody755_123 : HolLoopProg 64 :=
.mark loopBody755_122

def loopBody755_124 : HolLoopProg 64 :=
.seq loopBody755_89 loopBody755_123

def loopBody755_125 : HolLoopProg 64 :=
.mark loopBody755_124

def loopBody755_126 : HolLoopProg 64 :=
.seq loopBody755_17 loopBody755_125

def loopBody755_127 : HolLoopProg 64 :=
.mark loopBody755_126

def loopBody755_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody755_129 : HolLoopProg 64 :=
.mark loopBody755_128

def loopBody755_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody755_131 : HolLoopProg 64 :=
.mark loopBody755_130

def loopBody755_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody755_133 : HolLoopProg 64 :=
.mark loopBody755_132

def loopBody755_134 : HolLoopProg 64 :=
.seq loopBody755_133 loopBody755_1

def loopBody755_135 : HolLoopProg 64 :=
.mark loopBody755_134

def loopBody755_136 : HolLoopProg 64 :=
.seq loopBody755_131 loopBody755_135

def loopBody755_137 : HolLoopProg 64 :=
.mark loopBody755_136

def loopBody755_138 : HolLoopProg 64 :=
.seq loopBody755_137 loopBody755_1

def loopBody755_139 : HolLoopProg 64 :=
.mark loopBody755_138

def loopBody755_140 : HolLoopProg 64 :=
.seq loopBody755_77 loopBody755_139

def loopBody755_141 : HolLoopProg 64 :=
.mark loopBody755_140

def loopBody755_142 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_141

def loopBody755_143 : HolLoopProg 64 :=
.mark loopBody755_142

def loopBody755_144 : HolLoopProg 64 :=
.seq loopBody755_129 loopBody755_143

def loopBody755_145 : HolLoopProg 64 :=
.mark loopBody755_144

def loopBody755_146 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_145

def loopBody755_147 : HolLoopProg 64 :=
.mark loopBody755_146

def loopBody755_148 : HolLoopProg 64 :=
.seq loopBody755_127 loopBody755_147

def loopBody755_149 : HolLoopProg 64 :=
.mark loopBody755_148

def loopBody755_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody755_151 : HolLoopProg 64 :=
.mark loopBody755_150

def loopBody755_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 256#64)

def loopBody755_153 : HolLoopProg 64 :=
.mark loopBody755_152

def loopBody755_154 : HolLoopProg 64 :=
.seq loopBody755_153 loopBody755_139

def loopBody755_155 : HolLoopProg 64 :=
.mark loopBody755_154

def loopBody755_156 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_155

def loopBody755_157 : HolLoopProg 64 :=
.mark loopBody755_156

def loopBody755_158 : HolLoopProg 64 :=
.seq loopBody755_151 loopBody755_157

def loopBody755_159 : HolLoopProg 64 :=
.mark loopBody755_158

def loopBody755_160 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_159

def loopBody755_161 : HolLoopProg 64 :=
.mark loopBody755_160

def loopBody755_162 : HolLoopProg 64 :=
.seq loopBody755_149 loopBody755_161

def loopBody755_163 : HolLoopProg 64 :=
.mark loopBody755_162

def loopBody755_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody755_165 : HolLoopProg 64 :=
.mark loopBody755_164

def loopBody755_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody755_167 : HolLoopProg 64 :=
.mark loopBody755_166

def loopBody755_168 : HolLoopProg 64 :=
.seq loopBody755_167 loopBody755_1

def loopBody755_169 : HolLoopProg 64 :=
.mark loopBody755_168

def loopBody755_170 : HolLoopProg 64 :=
.seq loopBody755_165 loopBody755_169

def loopBody755_171 : HolLoopProg 64 :=
.mark loopBody755_170

def loopBody755_172 : HolLoopProg 64 :=
.seq loopBody755_163 loopBody755_171

def loopBody755_173 : HolLoopProg 64 :=
.mark loopBody755_172

def loopBody755_174 : HolLoopProg 64 :=
.seq loopBody755_87 loopBody755_173

def loopBody755_175 : HolLoopProg 64 :=
.mark loopBody755_174

def loopBody755_176 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_175

def loopBody755_177 : HolLoopProg 64 :=
.mark loopBody755_176

def loopBody755_178 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_177

def loopBody755_179 : HolLoopProg 64 :=
.mark loopBody755_178

def loopBody755_180 : HolLoopProg 64 :=
.seq loopBody755_73 loopBody755_179

def loopBody755_181 : HolLoopProg 64 :=
.mark loopBody755_180

def loopBody755_182 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_181

def loopBody755_183 : HolLoopProg 64 :=
.mark loopBody755_182

def loopBody755_184 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_183

def loopBody755_185 : HolLoopProg 64 :=
.mark loopBody755_184

def loopBody755_186 : HolLoopProg 64 :=
.seq loopBody755_65 loopBody755_185

def loopBody755_187 : HolLoopProg 64 :=
.mark loopBody755_186

def loopBody755_188 : HolLoopProg 64 :=
.seq loopBody755_5 loopBody755_187

def loopBody755_189 : HolLoopProg 64 :=
.mark loopBody755_188

def loopBody755_190 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_189

def loopBody755_191 : HolLoopProg 64 :=
.mark loopBody755_190

def loopBody755_192 : HolLoopProg 64 :=
.seq loopBody755_3 loopBody755_191

def loopBody755_193 : HolLoopProg 64 :=
.mark loopBody755_192

def loopBody755_194 : HolLoopProg 64 :=
.seq loopBody755_1 loopBody755_193

def loopBody755_195 : HolLoopProg 64 :=
.mark loopBody755_194

def output755 : Nat × List Nat × HolLoopProg 64 :=
  (819, [], loopBody755_195)
end InitECandidate.Proofs.FrontendStages.Loop
