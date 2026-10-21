import InitECandidate.Proofs.FrontendStages.Loop.Translate742
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody758_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody758_1 : HolLoopProg 64 :=
.mark loopBody758_0

def loopBody758_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody758_3 : HolLoopProg 64 :=
.mark loopBody758_2

def loopBody758_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64]))

def loopBody758_5 : HolLoopProg 64 :=
.mark loopBody758_4

def loopBody758_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody758_7 : HolLoopProg 64 :=
.mark loopBody758_6

def loopBody758_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 64#64)

def loopBody758_9 : HolLoopProg 64 :=
.mark loopBody758_8

def loopBody758_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody758_11 : HolLoopProg 64 :=
.mark loopBody758_10

def loopBody758_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody758_13 : HolLoopProg 64 :=
.mark loopBody758_12

def loopBody758_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody758_11 loopBody758_13 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody758_15 : HolLoopProg 64 :=
.mark loopBody758_14

def loopBody758_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody758_17 : HolLoopProg 64 :=
.mark loopBody758_16

def loopBody758_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 10#64)

def loopBody758_19 : HolLoopProg 64 :=
.mark loopBody758_18

def loopBody758_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody758_21 : HolLoopProg 64 :=
.mark loopBody758_20

def loopBody758_22 : HolLoopProg 64 :=
.seq loopBody758_21 loopBody758_1

def loopBody758_23 : HolLoopProg 64 :=
.mark loopBody758_22

def loopBody758_24 : HolLoopProg 64 :=
.seq loopBody758_23 loopBody758_1

def loopBody758_25 : HolLoopProg 64 :=
.mark loopBody758_24

def loopBody758_26 : HolLoopProg 64 :=
.seq loopBody758_19 loopBody758_25

def loopBody758_27 : HolLoopProg 64 :=
.mark loopBody758_26

def loopBody758_28 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_27

def loopBody758_29 : HolLoopProg 64 :=
.mark loopBody758_28

def loopBody758_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 8#64)

def loopBody758_31 : HolLoopProg 64 :=
.mark loopBody758_30

def loopBody758_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody758_33 : HolLoopProg 64 :=
.mark loopBody758_32

def loopBody758_34 : HolLoopProg 64 :=
.seq loopBody758_31 loopBody758_33

def loopBody758_35 : HolLoopProg 64 :=
.mark loopBody758_34

def loopBody758_36 : HolLoopProg 64 :=
.seq loopBody758_29 loopBody758_35

def loopBody758_37 : HolLoopProg 64 :=
.mark loopBody758_36

def loopBody758_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody758_37 loopBody758_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody758_39 : HolLoopProg 64 :=
.mark loopBody758_38

def loopBody758_40 : HolLoopProg 64 :=
.seq loopBody758_39 loopBody758_1

def loopBody758_41 : HolLoopProg 64 :=
.mark loopBody758_40

def loopBody758_42 : HolLoopProg 64 :=
.seq loopBody758_17 loopBody758_41

def loopBody758_43 : HolLoopProg 64 :=
.mark loopBody758_42

def loopBody758_44 : HolLoopProg 64 :=
.seq loopBody758_15 loopBody758_43

def loopBody758_45 : HolLoopProg 64 :=
.mark loopBody758_44

def loopBody758_46 : HolLoopProg 64 :=
.seq loopBody758_9 loopBody758_45

def loopBody758_47 : HolLoopProg 64 :=
.mark loopBody758_46

def loopBody758_48 : HolLoopProg 64 :=
.seq loopBody758_7 loopBody758_47

def loopBody758_49 : HolLoopProg 64 :=
.mark loopBody758_48

def loopBody758_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 5500#64)

def loopBody758_51 : HolLoopProg 64 :=
.mark loopBody758_50

def loopBody758_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody758_53 : HolLoopProg 64 :=
.mark loopBody758_52

def loopBody758_54 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 466) ([4]) (some (4, loopBody758_53, loopBody758_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody758_55 : HolLoopProg 64 :=
.mark loopBody758_54

def loopBody758_56 : HolLoopProg 64 :=
.seq loopBody758_55 loopBody758_1

def loopBody758_57 : HolLoopProg 64 :=
.mark loopBody758_56

def loopBody758_58 : HolLoopProg 64 :=
.seq loopBody758_51 loopBody758_57

def loopBody758_59 : HolLoopProg 64 :=
.mark loopBody758_58

def loopBody758_60 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_59

def loopBody758_61 : HolLoopProg 64 :=
.mark loopBody758_60

def loopBody758_62 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_61

def loopBody758_63 : HolLoopProg 64 :=
.mark loopBody758_62

def loopBody758_64 : HolLoopProg 64 :=
.seq loopBody758_49 loopBody758_63

def loopBody758_65 : HolLoopProg 64 :=
.mark loopBody758_64

def loopBody758_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 128#64)

def loopBody758_67 : HolLoopProg 64 :=
.mark loopBody758_66

def loopBody758_68 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody758_53, loopBody758_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody758_69 : HolLoopProg 64 :=
.mark loopBody758_68

def loopBody758_70 : HolLoopProg 64 :=
.seq loopBody758_69 loopBody758_1

def loopBody758_71 : HolLoopProg 64 :=
.mark loopBody758_70

def loopBody758_72 : HolLoopProg 64 :=
.seq loopBody758_67 loopBody758_71

def loopBody758_73 : HolLoopProg 64 :=
.mark loopBody758_72

def loopBody758_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 88#64]))

def loopBody758_75 : HolLoopProg 64 :=
.mark loopBody758_74

def loopBody758_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody758_77 : HolLoopProg 64 :=
.mark loopBody758_76

def loopBody758_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody758_79 : HolLoopProg 64 :=
.mark loopBody758_78

def loopBody758_80 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 811) ([5, 6]) (some (5, loopBody758_79, loopBody758_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody758_81 : HolLoopProg 64 :=
.mark loopBody758_80

def loopBody758_82 : HolLoopProg 64 :=
.seq loopBody758_81 loopBody758_1

def loopBody758_83 : HolLoopProg 64 :=
.mark loopBody758_82

def loopBody758_84 : HolLoopProg 64 :=
.seq loopBody758_77 loopBody758_83

def loopBody758_85 : HolLoopProg 64 :=
.mark loopBody758_84

def loopBody758_86 : HolLoopProg 64 :=
.seq loopBody758_75 loopBody758_85

def loopBody758_87 : HolLoopProg 64 :=
.mark loopBody758_86

def loopBody758_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody758_89 : HolLoopProg 64 :=
.mark loopBody758_88

def loopBody758_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody758_91 : HolLoopProg 64 :=
.mark loopBody758_90

def loopBody758_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody758_93 : HolLoopProg 64 :=
.mark loopBody758_92

def loopBody758_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody758_91 loopBody758_93 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody758_95 : HolLoopProg 64 :=
.mark loopBody758_94

def loopBody758_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody758_97 : HolLoopProg 64 :=
.mark loopBody758_96

def loopBody758_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 10#64)

def loopBody758_99 : HolLoopProg 64 :=
.mark loopBody758_98

def loopBody758_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 5)

def loopBody758_101 : HolLoopProg 64 :=
.mark loopBody758_100

def loopBody758_102 : HolLoopProg 64 :=
.seq loopBody758_101 loopBody758_1

def loopBody758_103 : HolLoopProg 64 :=
.mark loopBody758_102

def loopBody758_104 : HolLoopProg 64 :=
.seq loopBody758_103 loopBody758_1

def loopBody758_105 : HolLoopProg 64 :=
.mark loopBody758_104

def loopBody758_106 : HolLoopProg 64 :=
.seq loopBody758_99 loopBody758_105

def loopBody758_107 : HolLoopProg 64 :=
.mark loopBody758_106

def loopBody758_108 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_107

def loopBody758_109 : HolLoopProg 64 :=
.mark loopBody758_108

def loopBody758_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 8#64)

def loopBody758_111 : HolLoopProg 64 :=
.mark loopBody758_110

def loopBody758_112 : HolLoopProg 64 :=
.seq loopBody758_111 loopBody758_79

def loopBody758_113 : HolLoopProg 64 :=
.mark loopBody758_112

def loopBody758_114 : HolLoopProg 64 :=
.seq loopBody758_109 loopBody758_113

def loopBody758_115 : HolLoopProg 64 :=
.mark loopBody758_114

def loopBody758_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody758_115 loopBody758_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody758_117 : HolLoopProg 64 :=
.mark loopBody758_116

def loopBody758_118 : HolLoopProg 64 :=
.seq loopBody758_117 loopBody758_1

def loopBody758_119 : HolLoopProg 64 :=
.mark loopBody758_118

def loopBody758_120 : HolLoopProg 64 :=
.seq loopBody758_97 loopBody758_119

def loopBody758_121 : HolLoopProg 64 :=
.mark loopBody758_120

def loopBody758_122 : HolLoopProg 64 :=
.seq loopBody758_95 loopBody758_121

def loopBody758_123 : HolLoopProg 64 :=
.mark loopBody758_122

def loopBody758_124 : HolLoopProg 64 :=
.seq loopBody758_89 loopBody758_123

def loopBody758_125 : HolLoopProg 64 :=
.mark loopBody758_124

def loopBody758_126 : HolLoopProg 64 :=
.seq loopBody758_17 loopBody758_125

def loopBody758_127 : HolLoopProg 64 :=
.mark loopBody758_126

def loopBody758_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody758_129 : HolLoopProg 64 :=
.mark loopBody758_128

def loopBody758_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody758_131 : HolLoopProg 64 :=
.mark loopBody758_130

def loopBody758_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody758_133 : HolLoopProg 64 :=
.mark loopBody758_132

def loopBody758_134 : HolLoopProg 64 :=
.seq loopBody758_133 loopBody758_1

def loopBody758_135 : HolLoopProg 64 :=
.mark loopBody758_134

def loopBody758_136 : HolLoopProg 64 :=
.seq loopBody758_131 loopBody758_135

def loopBody758_137 : HolLoopProg 64 :=
.mark loopBody758_136

def loopBody758_138 : HolLoopProg 64 :=
.seq loopBody758_137 loopBody758_1

def loopBody758_139 : HolLoopProg 64 :=
.mark loopBody758_138

def loopBody758_140 : HolLoopProg 64 :=
.seq loopBody758_77 loopBody758_139

def loopBody758_141 : HolLoopProg 64 :=
.mark loopBody758_140

def loopBody758_142 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_141

def loopBody758_143 : HolLoopProg 64 :=
.mark loopBody758_142

def loopBody758_144 : HolLoopProg 64 :=
.seq loopBody758_129 loopBody758_143

def loopBody758_145 : HolLoopProg 64 :=
.mark loopBody758_144

def loopBody758_146 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_145

def loopBody758_147 : HolLoopProg 64 :=
.mark loopBody758_146

def loopBody758_148 : HolLoopProg 64 :=
.seq loopBody758_127 loopBody758_147

def loopBody758_149 : HolLoopProg 64 :=
.mark loopBody758_148

def loopBody758_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody758_151 : HolLoopProg 64 :=
.mark loopBody758_150

def loopBody758_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 128#64)

def loopBody758_153 : HolLoopProg 64 :=
.mark loopBody758_152

def loopBody758_154 : HolLoopProg 64 :=
.seq loopBody758_153 loopBody758_139

def loopBody758_155 : HolLoopProg 64 :=
.mark loopBody758_154

def loopBody758_156 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_155

def loopBody758_157 : HolLoopProg 64 :=
.mark loopBody758_156

def loopBody758_158 : HolLoopProg 64 :=
.seq loopBody758_151 loopBody758_157

def loopBody758_159 : HolLoopProg 64 :=
.mark loopBody758_158

def loopBody758_160 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_159

def loopBody758_161 : HolLoopProg 64 :=
.mark loopBody758_160

def loopBody758_162 : HolLoopProg 64 :=
.seq loopBody758_149 loopBody758_161

def loopBody758_163 : HolLoopProg 64 :=
.mark loopBody758_162

def loopBody758_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody758_165 : HolLoopProg 64 :=
.mark loopBody758_164

def loopBody758_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody758_167 : HolLoopProg 64 :=
.mark loopBody758_166

def loopBody758_168 : HolLoopProg 64 :=
.seq loopBody758_167 loopBody758_1

def loopBody758_169 : HolLoopProg 64 :=
.mark loopBody758_168

def loopBody758_170 : HolLoopProg 64 :=
.seq loopBody758_165 loopBody758_169

def loopBody758_171 : HolLoopProg 64 :=
.mark loopBody758_170

def loopBody758_172 : HolLoopProg 64 :=
.seq loopBody758_163 loopBody758_171

def loopBody758_173 : HolLoopProg 64 :=
.mark loopBody758_172

def loopBody758_174 : HolLoopProg 64 :=
.seq loopBody758_87 loopBody758_173

def loopBody758_175 : HolLoopProg 64 :=
.mark loopBody758_174

def loopBody758_176 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_175

def loopBody758_177 : HolLoopProg 64 :=
.mark loopBody758_176

def loopBody758_178 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_177

def loopBody758_179 : HolLoopProg 64 :=
.mark loopBody758_178

def loopBody758_180 : HolLoopProg 64 :=
.seq loopBody758_73 loopBody758_179

def loopBody758_181 : HolLoopProg 64 :=
.mark loopBody758_180

def loopBody758_182 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_181

def loopBody758_183 : HolLoopProg 64 :=
.mark loopBody758_182

def loopBody758_184 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_183

def loopBody758_185 : HolLoopProg 64 :=
.mark loopBody758_184

def loopBody758_186 : HolLoopProg 64 :=
.seq loopBody758_65 loopBody758_185

def loopBody758_187 : HolLoopProg 64 :=
.mark loopBody758_186

def loopBody758_188 : HolLoopProg 64 :=
.seq loopBody758_5 loopBody758_187

def loopBody758_189 : HolLoopProg 64 :=
.mark loopBody758_188

def loopBody758_190 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_189

def loopBody758_191 : HolLoopProg 64 :=
.mark loopBody758_190

def loopBody758_192 : HolLoopProg 64 :=
.seq loopBody758_3 loopBody758_191

def loopBody758_193 : HolLoopProg 64 :=
.mark loopBody758_192

def loopBody758_194 : HolLoopProg 64 :=
.seq loopBody758_1 loopBody758_193

def loopBody758_195 : HolLoopProg 64 :=
.mark loopBody758_194

def output758 : Nat × List Nat × HolLoopProg 64 :=
  (822, [], loopBody758_195)
end InitECandidate.Proofs.FrontendStages.Loop
