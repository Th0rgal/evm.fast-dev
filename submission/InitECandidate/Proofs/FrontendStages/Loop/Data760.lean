import InitECandidate.Proofs.FrontendStages.Loop.Translate744
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody760_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody760_1 : HolLoopProg 64 :=
.mark loopBody760_0

def loopBody760_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody760_3 : HolLoopProg 64 :=
.mark loopBody760_2

def loopBody760_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64]))

def loopBody760_5 : HolLoopProg 64 :=
.mark loopBody760_4

def loopBody760_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody760_7 : HolLoopProg 64 :=
.mark loopBody760_6

def loopBody760_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 192#64)

def loopBody760_9 : HolLoopProg 64 :=
.mark loopBody760_8

def loopBody760_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody760_11 : HolLoopProg 64 :=
.mark loopBody760_10

def loopBody760_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody760_13 : HolLoopProg 64 :=
.mark loopBody760_12

def loopBody760_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody760_11 loopBody760_13 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody760_15 : HolLoopProg 64 :=
.mark loopBody760_14

def loopBody760_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody760_17 : HolLoopProg 64 :=
.mark loopBody760_16

def loopBody760_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 13#64)

def loopBody760_19 : HolLoopProg 64 :=
.mark loopBody760_18

def loopBody760_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody760_21 : HolLoopProg 64 :=
.mark loopBody760_20

def loopBody760_22 : HolLoopProg 64 :=
.seq loopBody760_21 loopBody760_1

def loopBody760_23 : HolLoopProg 64 :=
.mark loopBody760_22

def loopBody760_24 : HolLoopProg 64 :=
.seq loopBody760_23 loopBody760_1

def loopBody760_25 : HolLoopProg 64 :=
.mark loopBody760_24

def loopBody760_26 : HolLoopProg 64 :=
.seq loopBody760_19 loopBody760_25

def loopBody760_27 : HolLoopProg 64 :=
.mark loopBody760_26

def loopBody760_28 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_27

def loopBody760_29 : HolLoopProg 64 :=
.mark loopBody760_28

def loopBody760_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 8#64)

def loopBody760_31 : HolLoopProg 64 :=
.mark loopBody760_30

def loopBody760_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody760_33 : HolLoopProg 64 :=
.mark loopBody760_32

def loopBody760_34 : HolLoopProg 64 :=
.seq loopBody760_31 loopBody760_33

def loopBody760_35 : HolLoopProg 64 :=
.mark loopBody760_34

def loopBody760_36 : HolLoopProg 64 :=
.seq loopBody760_29 loopBody760_35

def loopBody760_37 : HolLoopProg 64 :=
.mark loopBody760_36

def loopBody760_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody760_37 loopBody760_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody760_39 : HolLoopProg 64 :=
.mark loopBody760_38

def loopBody760_40 : HolLoopProg 64 :=
.seq loopBody760_39 loopBody760_1

def loopBody760_41 : HolLoopProg 64 :=
.mark loopBody760_40

def loopBody760_42 : HolLoopProg 64 :=
.seq loopBody760_17 loopBody760_41

def loopBody760_43 : HolLoopProg 64 :=
.mark loopBody760_42

def loopBody760_44 : HolLoopProg 64 :=
.seq loopBody760_15 loopBody760_43

def loopBody760_45 : HolLoopProg 64 :=
.mark loopBody760_44

def loopBody760_46 : HolLoopProg 64 :=
.seq loopBody760_9 loopBody760_45

def loopBody760_47 : HolLoopProg 64 :=
.mark loopBody760_46

def loopBody760_48 : HolLoopProg 64 :=
.seq loopBody760_7 loopBody760_47

def loopBody760_49 : HolLoopProg 64 :=
.mark loopBody760_48

def loopBody760_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 50000#64)

def loopBody760_51 : HolLoopProg 64 :=
.mark loopBody760_50

def loopBody760_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody760_53 : HolLoopProg 64 :=
.mark loopBody760_52

def loopBody760_54 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 466) ([4]) (some (4, loopBody760_53, loopBody760_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody760_55 : HolLoopProg 64 :=
.mark loopBody760_54

def loopBody760_56 : HolLoopProg 64 :=
.seq loopBody760_55 loopBody760_1

def loopBody760_57 : HolLoopProg 64 :=
.mark loopBody760_56

def loopBody760_58 : HolLoopProg 64 :=
.seq loopBody760_51 loopBody760_57

def loopBody760_59 : HolLoopProg 64 :=
.mark loopBody760_58

def loopBody760_60 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_59

def loopBody760_61 : HolLoopProg 64 :=
.mark loopBody760_60

def loopBody760_62 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_61

def loopBody760_63 : HolLoopProg 64 :=
.mark loopBody760_62

def loopBody760_64 : HolLoopProg 64 :=
.seq loopBody760_49 loopBody760_63

def loopBody760_65 : HolLoopProg 64 :=
.mark loopBody760_64

def loopBody760_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 64#64)

def loopBody760_67 : HolLoopProg 64 :=
.mark loopBody760_66

def loopBody760_68 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody760_53, loopBody760_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody760_69 : HolLoopProg 64 :=
.mark loopBody760_68

def loopBody760_70 : HolLoopProg 64 :=
.seq loopBody760_69 loopBody760_1

def loopBody760_71 : HolLoopProg 64 :=
.mark loopBody760_70

def loopBody760_72 : HolLoopProg 64 :=
.seq loopBody760_67 loopBody760_71

def loopBody760_73 : HolLoopProg 64 :=
.mark loopBody760_72

def loopBody760_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 88#64]))

def loopBody760_75 : HolLoopProg 64 :=
.mark loopBody760_74

def loopBody760_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody760_77 : HolLoopProg 64 :=
.mark loopBody760_76

def loopBody760_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody760_79 : HolLoopProg 64 :=
.mark loopBody760_78

def loopBody760_80 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 813) ([5, 6]) (some (5, loopBody760_79, loopBody760_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody760_81 : HolLoopProg 64 :=
.mark loopBody760_80

def loopBody760_82 : HolLoopProg 64 :=
.seq loopBody760_81 loopBody760_1

def loopBody760_83 : HolLoopProg 64 :=
.mark loopBody760_82

def loopBody760_84 : HolLoopProg 64 :=
.seq loopBody760_77 loopBody760_83

def loopBody760_85 : HolLoopProg 64 :=
.mark loopBody760_84

def loopBody760_86 : HolLoopProg 64 :=
.seq loopBody760_75 loopBody760_85

def loopBody760_87 : HolLoopProg 64 :=
.mark loopBody760_86

def loopBody760_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody760_89 : HolLoopProg 64 :=
.mark loopBody760_88

def loopBody760_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody760_91 : HolLoopProg 64 :=
.mark loopBody760_90

def loopBody760_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody760_93 : HolLoopProg 64 :=
.mark loopBody760_92

def loopBody760_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody760_91 loopBody760_93 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody760_95 : HolLoopProg 64 :=
.mark loopBody760_94

def loopBody760_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody760_97 : HolLoopProg 64 :=
.mark loopBody760_96

def loopBody760_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 13#64)

def loopBody760_99 : HolLoopProg 64 :=
.mark loopBody760_98

def loopBody760_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 5)

def loopBody760_101 : HolLoopProg 64 :=
.mark loopBody760_100

def loopBody760_102 : HolLoopProg 64 :=
.seq loopBody760_101 loopBody760_1

def loopBody760_103 : HolLoopProg 64 :=
.mark loopBody760_102

def loopBody760_104 : HolLoopProg 64 :=
.seq loopBody760_103 loopBody760_1

def loopBody760_105 : HolLoopProg 64 :=
.mark loopBody760_104

def loopBody760_106 : HolLoopProg 64 :=
.seq loopBody760_99 loopBody760_105

def loopBody760_107 : HolLoopProg 64 :=
.mark loopBody760_106

def loopBody760_108 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_107

def loopBody760_109 : HolLoopProg 64 :=
.mark loopBody760_108

def loopBody760_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 8#64)

def loopBody760_111 : HolLoopProg 64 :=
.mark loopBody760_110

def loopBody760_112 : HolLoopProg 64 :=
.seq loopBody760_111 loopBody760_79

def loopBody760_113 : HolLoopProg 64 :=
.mark loopBody760_112

def loopBody760_114 : HolLoopProg 64 :=
.seq loopBody760_109 loopBody760_113

def loopBody760_115 : HolLoopProg 64 :=
.mark loopBody760_114

def loopBody760_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody760_115 loopBody760_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody760_117 : HolLoopProg 64 :=
.mark loopBody760_116

def loopBody760_118 : HolLoopProg 64 :=
.seq loopBody760_117 loopBody760_1

def loopBody760_119 : HolLoopProg 64 :=
.mark loopBody760_118

def loopBody760_120 : HolLoopProg 64 :=
.seq loopBody760_97 loopBody760_119

def loopBody760_121 : HolLoopProg 64 :=
.mark loopBody760_120

def loopBody760_122 : HolLoopProg 64 :=
.seq loopBody760_95 loopBody760_121

def loopBody760_123 : HolLoopProg 64 :=
.mark loopBody760_122

def loopBody760_124 : HolLoopProg 64 :=
.seq loopBody760_89 loopBody760_123

def loopBody760_125 : HolLoopProg 64 :=
.mark loopBody760_124

def loopBody760_126 : HolLoopProg 64 :=
.seq loopBody760_17 loopBody760_125

def loopBody760_127 : HolLoopProg 64 :=
.mark loopBody760_126

def loopBody760_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody760_129 : HolLoopProg 64 :=
.mark loopBody760_128

def loopBody760_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody760_131 : HolLoopProg 64 :=
.mark loopBody760_130

def loopBody760_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody760_133 : HolLoopProg 64 :=
.mark loopBody760_132

def loopBody760_134 : HolLoopProg 64 :=
.seq loopBody760_133 loopBody760_1

def loopBody760_135 : HolLoopProg 64 :=
.mark loopBody760_134

def loopBody760_136 : HolLoopProg 64 :=
.seq loopBody760_131 loopBody760_135

def loopBody760_137 : HolLoopProg 64 :=
.mark loopBody760_136

def loopBody760_138 : HolLoopProg 64 :=
.seq loopBody760_137 loopBody760_1

def loopBody760_139 : HolLoopProg 64 :=
.mark loopBody760_138

def loopBody760_140 : HolLoopProg 64 :=
.seq loopBody760_77 loopBody760_139

def loopBody760_141 : HolLoopProg 64 :=
.mark loopBody760_140

def loopBody760_142 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_141

def loopBody760_143 : HolLoopProg 64 :=
.mark loopBody760_142

def loopBody760_144 : HolLoopProg 64 :=
.seq loopBody760_129 loopBody760_143

def loopBody760_145 : HolLoopProg 64 :=
.mark loopBody760_144

def loopBody760_146 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_145

def loopBody760_147 : HolLoopProg 64 :=
.mark loopBody760_146

def loopBody760_148 : HolLoopProg 64 :=
.seq loopBody760_127 loopBody760_147

def loopBody760_149 : HolLoopProg 64 :=
.mark loopBody760_148

def loopBody760_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody760_151 : HolLoopProg 64 :=
.mark loopBody760_150

def loopBody760_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 64#64)

def loopBody760_153 : HolLoopProg 64 :=
.mark loopBody760_152

def loopBody760_154 : HolLoopProg 64 :=
.seq loopBody760_153 loopBody760_139

def loopBody760_155 : HolLoopProg 64 :=
.mark loopBody760_154

def loopBody760_156 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_155

def loopBody760_157 : HolLoopProg 64 :=
.mark loopBody760_156

def loopBody760_158 : HolLoopProg 64 :=
.seq loopBody760_151 loopBody760_157

def loopBody760_159 : HolLoopProg 64 :=
.mark loopBody760_158

def loopBody760_160 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_159

def loopBody760_161 : HolLoopProg 64 :=
.mark loopBody760_160

def loopBody760_162 : HolLoopProg 64 :=
.seq loopBody760_149 loopBody760_161

def loopBody760_163 : HolLoopProg 64 :=
.mark loopBody760_162

def loopBody760_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody760_165 : HolLoopProg 64 :=
.mark loopBody760_164

def loopBody760_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody760_167 : HolLoopProg 64 :=
.mark loopBody760_166

def loopBody760_168 : HolLoopProg 64 :=
.seq loopBody760_167 loopBody760_1

def loopBody760_169 : HolLoopProg 64 :=
.mark loopBody760_168

def loopBody760_170 : HolLoopProg 64 :=
.seq loopBody760_165 loopBody760_169

def loopBody760_171 : HolLoopProg 64 :=
.mark loopBody760_170

def loopBody760_172 : HolLoopProg 64 :=
.seq loopBody760_163 loopBody760_171

def loopBody760_173 : HolLoopProg 64 :=
.mark loopBody760_172

def loopBody760_174 : HolLoopProg 64 :=
.seq loopBody760_87 loopBody760_173

def loopBody760_175 : HolLoopProg 64 :=
.mark loopBody760_174

def loopBody760_176 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_175

def loopBody760_177 : HolLoopProg 64 :=
.mark loopBody760_176

def loopBody760_178 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_177

def loopBody760_179 : HolLoopProg 64 :=
.mark loopBody760_178

def loopBody760_180 : HolLoopProg 64 :=
.seq loopBody760_73 loopBody760_179

def loopBody760_181 : HolLoopProg 64 :=
.mark loopBody760_180

def loopBody760_182 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_181

def loopBody760_183 : HolLoopProg 64 :=
.mark loopBody760_182

def loopBody760_184 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_183

def loopBody760_185 : HolLoopProg 64 :=
.mark loopBody760_184

def loopBody760_186 : HolLoopProg 64 :=
.seq loopBody760_65 loopBody760_185

def loopBody760_187 : HolLoopProg 64 :=
.mark loopBody760_186

def loopBody760_188 : HolLoopProg 64 :=
.seq loopBody760_5 loopBody760_187

def loopBody760_189 : HolLoopProg 64 :=
.mark loopBody760_188

def loopBody760_190 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_189

def loopBody760_191 : HolLoopProg 64 :=
.mark loopBody760_190

def loopBody760_192 : HolLoopProg 64 :=
.seq loopBody760_3 loopBody760_191

def loopBody760_193 : HolLoopProg 64 :=
.mark loopBody760_192

def loopBody760_194 : HolLoopProg 64 :=
.seq loopBody760_1 loopBody760_193

def loopBody760_195 : HolLoopProg 64 :=
.mark loopBody760_194

def output760 : Nat × List Nat × HolLoopProg 64 :=
  (824, [], loopBody760_195)
end InitECandidate.Proofs.FrontendStages.Loop
