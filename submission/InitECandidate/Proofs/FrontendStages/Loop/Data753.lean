import InitECandidate.Proofs.FrontendStages.Loop.Translate737
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody753_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody753_1 : HolLoopProg 64 :=
.mark loopBody753_0

def loopBody753_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody753_3 : HolLoopProg 64 :=
.mark loopBody753_2

def loopBody753_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64]))

def loopBody753_5 : HolLoopProg 64 :=
.mark loopBody753_4

def loopBody753_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody753_7 : HolLoopProg 64 :=
.mark loopBody753_6

def loopBody753_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 256#64)

def loopBody753_9 : HolLoopProg 64 :=
.mark loopBody753_8

def loopBody753_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody753_11 : HolLoopProg 64 :=
.mark loopBody753_10

def loopBody753_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody753_13 : HolLoopProg 64 :=
.mark loopBody753_12

def loopBody753_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody753_11 loopBody753_13 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody753_15 : HolLoopProg 64 :=
.mark loopBody753_14

def loopBody753_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody753_17 : HolLoopProg 64 :=
.mark loopBody753_16

def loopBody753_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 10#64)

def loopBody753_19 : HolLoopProg 64 :=
.mark loopBody753_18

def loopBody753_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody753_21 : HolLoopProg 64 :=
.mark loopBody753_20

def loopBody753_22 : HolLoopProg 64 :=
.seq loopBody753_21 loopBody753_1

def loopBody753_23 : HolLoopProg 64 :=
.mark loopBody753_22

def loopBody753_24 : HolLoopProg 64 :=
.seq loopBody753_23 loopBody753_1

def loopBody753_25 : HolLoopProg 64 :=
.mark loopBody753_24

def loopBody753_26 : HolLoopProg 64 :=
.seq loopBody753_19 loopBody753_25

def loopBody753_27 : HolLoopProg 64 :=
.mark loopBody753_26

def loopBody753_28 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_27

def loopBody753_29 : HolLoopProg 64 :=
.mark loopBody753_28

def loopBody753_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 8#64)

def loopBody753_31 : HolLoopProg 64 :=
.mark loopBody753_30

def loopBody753_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody753_33 : HolLoopProg 64 :=
.mark loopBody753_32

def loopBody753_34 : HolLoopProg 64 :=
.seq loopBody753_31 loopBody753_33

def loopBody753_35 : HolLoopProg 64 :=
.mark loopBody753_34

def loopBody753_36 : HolLoopProg 64 :=
.seq loopBody753_29 loopBody753_35

def loopBody753_37 : HolLoopProg 64 :=
.mark loopBody753_36

def loopBody753_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody753_37 loopBody753_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody753_39 : HolLoopProg 64 :=
.mark loopBody753_38

def loopBody753_40 : HolLoopProg 64 :=
.seq loopBody753_39 loopBody753_1

def loopBody753_41 : HolLoopProg 64 :=
.mark loopBody753_40

def loopBody753_42 : HolLoopProg 64 :=
.seq loopBody753_17 loopBody753_41

def loopBody753_43 : HolLoopProg 64 :=
.mark loopBody753_42

def loopBody753_44 : HolLoopProg 64 :=
.seq loopBody753_15 loopBody753_43

def loopBody753_45 : HolLoopProg 64 :=
.mark loopBody753_44

def loopBody753_46 : HolLoopProg 64 :=
.seq loopBody753_9 loopBody753_45

def loopBody753_47 : HolLoopProg 64 :=
.mark loopBody753_46

def loopBody753_48 : HolLoopProg 64 :=
.seq loopBody753_7 loopBody753_47

def loopBody753_49 : HolLoopProg 64 :=
.mark loopBody753_48

def loopBody753_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 375#64)

def loopBody753_51 : HolLoopProg 64 :=
.mark loopBody753_50

def loopBody753_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody753_53 : HolLoopProg 64 :=
.mark loopBody753_52

def loopBody753_54 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 466) ([4]) (some (4, loopBody753_53, loopBody753_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody753_55 : HolLoopProg 64 :=
.mark loopBody753_54

def loopBody753_56 : HolLoopProg 64 :=
.seq loopBody753_55 loopBody753_1

def loopBody753_57 : HolLoopProg 64 :=
.mark loopBody753_56

def loopBody753_58 : HolLoopProg 64 :=
.seq loopBody753_51 loopBody753_57

def loopBody753_59 : HolLoopProg 64 :=
.mark loopBody753_58

def loopBody753_60 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_59

def loopBody753_61 : HolLoopProg 64 :=
.mark loopBody753_60

def loopBody753_62 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_61

def loopBody753_63 : HolLoopProg 64 :=
.mark loopBody753_62

def loopBody753_64 : HolLoopProg 64 :=
.seq loopBody753_49 loopBody753_63

def loopBody753_65 : HolLoopProg 64 :=
.mark loopBody753_64

def loopBody753_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 128#64)

def loopBody753_67 : HolLoopProg 64 :=
.mark loopBody753_66

def loopBody753_68 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody753_53, loopBody753_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody753_69 : HolLoopProg 64 :=
.mark loopBody753_68

def loopBody753_70 : HolLoopProg 64 :=
.seq loopBody753_69 loopBody753_1

def loopBody753_71 : HolLoopProg 64 :=
.mark loopBody753_70

def loopBody753_72 : HolLoopProg 64 :=
.seq loopBody753_67 loopBody753_71

def loopBody753_73 : HolLoopProg 64 :=
.mark loopBody753_72

def loopBody753_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 88#64]))

def loopBody753_75 : HolLoopProg 64 :=
.mark loopBody753_74

def loopBody753_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody753_77 : HolLoopProg 64 :=
.mark loopBody753_76

def loopBody753_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody753_79 : HolLoopProg 64 :=
.mark loopBody753_78

def loopBody753_80 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 806) ([5, 6]) (some (5, loopBody753_79, loopBody753_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody753_81 : HolLoopProg 64 :=
.mark loopBody753_80

def loopBody753_82 : HolLoopProg 64 :=
.seq loopBody753_81 loopBody753_1

def loopBody753_83 : HolLoopProg 64 :=
.mark loopBody753_82

def loopBody753_84 : HolLoopProg 64 :=
.seq loopBody753_77 loopBody753_83

def loopBody753_85 : HolLoopProg 64 :=
.mark loopBody753_84

def loopBody753_86 : HolLoopProg 64 :=
.seq loopBody753_75 loopBody753_85

def loopBody753_87 : HolLoopProg 64 :=
.mark loopBody753_86

def loopBody753_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody753_89 : HolLoopProg 64 :=
.mark loopBody753_88

def loopBody753_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody753_91 : HolLoopProg 64 :=
.mark loopBody753_90

def loopBody753_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody753_93 : HolLoopProg 64 :=
.mark loopBody753_92

def loopBody753_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody753_91 loopBody753_93 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody753_95 : HolLoopProg 64 :=
.mark loopBody753_94

def loopBody753_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody753_97 : HolLoopProg 64 :=
.mark loopBody753_96

def loopBody753_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 10#64)

def loopBody753_99 : HolLoopProg 64 :=
.mark loopBody753_98

def loopBody753_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 5)

def loopBody753_101 : HolLoopProg 64 :=
.mark loopBody753_100

def loopBody753_102 : HolLoopProg 64 :=
.seq loopBody753_101 loopBody753_1

def loopBody753_103 : HolLoopProg 64 :=
.mark loopBody753_102

def loopBody753_104 : HolLoopProg 64 :=
.seq loopBody753_103 loopBody753_1

def loopBody753_105 : HolLoopProg 64 :=
.mark loopBody753_104

def loopBody753_106 : HolLoopProg 64 :=
.seq loopBody753_99 loopBody753_105

def loopBody753_107 : HolLoopProg 64 :=
.mark loopBody753_106

def loopBody753_108 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_107

def loopBody753_109 : HolLoopProg 64 :=
.mark loopBody753_108

def loopBody753_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 8#64)

def loopBody753_111 : HolLoopProg 64 :=
.mark loopBody753_110

def loopBody753_112 : HolLoopProg 64 :=
.seq loopBody753_111 loopBody753_79

def loopBody753_113 : HolLoopProg 64 :=
.mark loopBody753_112

def loopBody753_114 : HolLoopProg 64 :=
.seq loopBody753_109 loopBody753_113

def loopBody753_115 : HolLoopProg 64 :=
.mark loopBody753_114

def loopBody753_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody753_115 loopBody753_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody753_117 : HolLoopProg 64 :=
.mark loopBody753_116

def loopBody753_118 : HolLoopProg 64 :=
.seq loopBody753_117 loopBody753_1

def loopBody753_119 : HolLoopProg 64 :=
.mark loopBody753_118

def loopBody753_120 : HolLoopProg 64 :=
.seq loopBody753_97 loopBody753_119

def loopBody753_121 : HolLoopProg 64 :=
.mark loopBody753_120

def loopBody753_122 : HolLoopProg 64 :=
.seq loopBody753_95 loopBody753_121

def loopBody753_123 : HolLoopProg 64 :=
.mark loopBody753_122

def loopBody753_124 : HolLoopProg 64 :=
.seq loopBody753_89 loopBody753_123

def loopBody753_125 : HolLoopProg 64 :=
.mark loopBody753_124

def loopBody753_126 : HolLoopProg 64 :=
.seq loopBody753_17 loopBody753_125

def loopBody753_127 : HolLoopProg 64 :=
.mark loopBody753_126

def loopBody753_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody753_129 : HolLoopProg 64 :=
.mark loopBody753_128

def loopBody753_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody753_131 : HolLoopProg 64 :=
.mark loopBody753_130

def loopBody753_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody753_133 : HolLoopProg 64 :=
.mark loopBody753_132

def loopBody753_134 : HolLoopProg 64 :=
.seq loopBody753_133 loopBody753_1

def loopBody753_135 : HolLoopProg 64 :=
.mark loopBody753_134

def loopBody753_136 : HolLoopProg 64 :=
.seq loopBody753_131 loopBody753_135

def loopBody753_137 : HolLoopProg 64 :=
.mark loopBody753_136

def loopBody753_138 : HolLoopProg 64 :=
.seq loopBody753_137 loopBody753_1

def loopBody753_139 : HolLoopProg 64 :=
.mark loopBody753_138

def loopBody753_140 : HolLoopProg 64 :=
.seq loopBody753_77 loopBody753_139

def loopBody753_141 : HolLoopProg 64 :=
.mark loopBody753_140

def loopBody753_142 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_141

def loopBody753_143 : HolLoopProg 64 :=
.mark loopBody753_142

def loopBody753_144 : HolLoopProg 64 :=
.seq loopBody753_129 loopBody753_143

def loopBody753_145 : HolLoopProg 64 :=
.mark loopBody753_144

def loopBody753_146 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_145

def loopBody753_147 : HolLoopProg 64 :=
.mark loopBody753_146

def loopBody753_148 : HolLoopProg 64 :=
.seq loopBody753_127 loopBody753_147

def loopBody753_149 : HolLoopProg 64 :=
.mark loopBody753_148

def loopBody753_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody753_151 : HolLoopProg 64 :=
.mark loopBody753_150

def loopBody753_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 128#64)

def loopBody753_153 : HolLoopProg 64 :=
.mark loopBody753_152

def loopBody753_154 : HolLoopProg 64 :=
.seq loopBody753_153 loopBody753_139

def loopBody753_155 : HolLoopProg 64 :=
.mark loopBody753_154

def loopBody753_156 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_155

def loopBody753_157 : HolLoopProg 64 :=
.mark loopBody753_156

def loopBody753_158 : HolLoopProg 64 :=
.seq loopBody753_151 loopBody753_157

def loopBody753_159 : HolLoopProg 64 :=
.mark loopBody753_158

def loopBody753_160 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_159

def loopBody753_161 : HolLoopProg 64 :=
.mark loopBody753_160

def loopBody753_162 : HolLoopProg 64 :=
.seq loopBody753_149 loopBody753_161

def loopBody753_163 : HolLoopProg 64 :=
.mark loopBody753_162

def loopBody753_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody753_165 : HolLoopProg 64 :=
.mark loopBody753_164

def loopBody753_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody753_167 : HolLoopProg 64 :=
.mark loopBody753_166

def loopBody753_168 : HolLoopProg 64 :=
.seq loopBody753_167 loopBody753_1

def loopBody753_169 : HolLoopProg 64 :=
.mark loopBody753_168

def loopBody753_170 : HolLoopProg 64 :=
.seq loopBody753_165 loopBody753_169

def loopBody753_171 : HolLoopProg 64 :=
.mark loopBody753_170

def loopBody753_172 : HolLoopProg 64 :=
.seq loopBody753_163 loopBody753_171

def loopBody753_173 : HolLoopProg 64 :=
.mark loopBody753_172

def loopBody753_174 : HolLoopProg 64 :=
.seq loopBody753_87 loopBody753_173

def loopBody753_175 : HolLoopProg 64 :=
.mark loopBody753_174

def loopBody753_176 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_175

def loopBody753_177 : HolLoopProg 64 :=
.mark loopBody753_176

def loopBody753_178 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_177

def loopBody753_179 : HolLoopProg 64 :=
.mark loopBody753_178

def loopBody753_180 : HolLoopProg 64 :=
.seq loopBody753_73 loopBody753_179

def loopBody753_181 : HolLoopProg 64 :=
.mark loopBody753_180

def loopBody753_182 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_181

def loopBody753_183 : HolLoopProg 64 :=
.mark loopBody753_182

def loopBody753_184 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_183

def loopBody753_185 : HolLoopProg 64 :=
.mark loopBody753_184

def loopBody753_186 : HolLoopProg 64 :=
.seq loopBody753_65 loopBody753_185

def loopBody753_187 : HolLoopProg 64 :=
.mark loopBody753_186

def loopBody753_188 : HolLoopProg 64 :=
.seq loopBody753_5 loopBody753_187

def loopBody753_189 : HolLoopProg 64 :=
.mark loopBody753_188

def loopBody753_190 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_189

def loopBody753_191 : HolLoopProg 64 :=
.mark loopBody753_190

def loopBody753_192 : HolLoopProg 64 :=
.seq loopBody753_3 loopBody753_191

def loopBody753_193 : HolLoopProg 64 :=
.mark loopBody753_192

def loopBody753_194 : HolLoopProg 64 :=
.seq loopBody753_1 loopBody753_193

def loopBody753_195 : HolLoopProg 64 :=
.mark loopBody753_194

def output753 : Nat × List Nat × HolLoopProg 64 :=
  (817, [], loopBody753_195)
end InitECandidate.Proofs.FrontendStages.Loop
