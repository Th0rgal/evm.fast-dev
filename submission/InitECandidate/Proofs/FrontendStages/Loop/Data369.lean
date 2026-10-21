import InitECandidate.Proofs.FrontendStages.Loop.Translate353
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody369_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody369_1 : HolLoopProg 64 :=
.mark loopBody369_0

def loopBody369_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody369_3 : HolLoopProg 64 :=
.mark loopBody369_2

def loopBody369_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody369_5 : HolLoopProg 64 :=
.mark loopBody369_4

def loopBody369_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody369_7 : HolLoopProg 64 :=
.mark loopBody369_6

def loopBody369_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody369_9 : HolLoopProg 64 :=
.mark loopBody369_8

def loopBody369_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody369_11 : HolLoopProg 64 :=
.mark loopBody369_10

def loopBody369_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody369_13 : HolLoopProg 64 :=
.mark loopBody369_12

def loopBody369_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 5 (Flapjack.RegImm.reg 6) loopBody369_11 loopBody369_13 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody369_15 : HolLoopProg 64 :=
.mark loopBody369_14

def loopBody369_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody369_17 : HolLoopProg 64 :=
.mark loopBody369_16

def loopBody369_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody369_19 : HolLoopProg 64 :=
.mark loopBody369_18

def loopBody369_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 7 7 5 6)

def loopBody369_21 : HolLoopProg 64 :=
.mark loopBody369_20

def loopBody369_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 1#64))

def loopBody369_23 : HolLoopProg 64 :=
.mark loopBody369_22

def loopBody369_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody369_25 : HolLoopProg 64 :=
.mark loopBody369_24

def loopBody369_26 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([8]) (some (5, loopBody369_25, loopBody369_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody369_27 : HolLoopProg 64 :=
.mark loopBody369_26

def loopBody369_28 : HolLoopProg 64 :=
.seq loopBody369_27 loopBody369_1

def loopBody369_29 : HolLoopProg 64 :=
.mark loopBody369_28

def loopBody369_30 : HolLoopProg 64 :=
.seq loopBody369_23 loopBody369_29

def loopBody369_31 : HolLoopProg 64 :=
.mark loopBody369_30

def loopBody369_32 : HolLoopProg 64 :=
.seq loopBody369_21 loopBody369_31

def loopBody369_33 : HolLoopProg 64 :=
.mark loopBody369_32

def loopBody369_34 : HolLoopProg 64 :=
.seq loopBody369_9 loopBody369_33

def loopBody369_35 : HolLoopProg 64 :=
.mark loopBody369_34

def loopBody369_36 : HolLoopProg 64 :=
.seq loopBody369_19 loopBody369_35

def loopBody369_37 : HolLoopProg 64 :=
.mark loopBody369_36

def loopBody369_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody369_39 : HolLoopProg 64 :=
.mark loopBody369_38

def loopBody369_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody369_41 : HolLoopProg 64 :=
.mark loopBody369_40

def loopBody369_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 8 8 6 7)

def loopBody369_43 : HolLoopProg 64 :=
.mark loopBody369_42

def loopBody369_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody369_45 : HolLoopProg 64 :=
.mark loopBody369_44

def loopBody369_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody369_47 : HolLoopProg 64 :=
.mark loopBody369_46

def loopBody369_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody369_49 : HolLoopProg 64 :=
.mark loopBody369_48

def loopBody369_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody369_51 : HolLoopProg 64 :=
.mark loopBody369_50

def loopBody369_52 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([9, 10, 11]) (some (6, loopBody369_51, loopBody369_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody369_53 : HolLoopProg 64 :=
.mark loopBody369_52

def loopBody369_54 : HolLoopProg 64 :=
.seq loopBody369_53 loopBody369_1

def loopBody369_55 : HolLoopProg 64 :=
.mark loopBody369_54

def loopBody369_56 : HolLoopProg 64 :=
.seq loopBody369_49 loopBody369_55

def loopBody369_57 : HolLoopProg 64 :=
.mark loopBody369_56

def loopBody369_58 : HolLoopProg 64 :=
.seq loopBody369_47 loopBody369_57

def loopBody369_59 : HolLoopProg 64 :=
.mark loopBody369_58

def loopBody369_60 : HolLoopProg 64 :=
.seq loopBody369_45 loopBody369_59

def loopBody369_61 : HolLoopProg 64 :=
.mark loopBody369_60

def loopBody369_62 : HolLoopProg 64 :=
.seq loopBody369_43 loopBody369_61

def loopBody369_63 : HolLoopProg 64 :=
.mark loopBody369_62

def loopBody369_64 : HolLoopProg 64 :=
.seq loopBody369_41 loopBody369_63

def loopBody369_65 : HolLoopProg 64 :=
.mark loopBody369_64

def loopBody369_66 : HolLoopProg 64 :=
.seq loopBody369_39 loopBody369_65

def loopBody369_67 : HolLoopProg 64 :=
.mark loopBody369_66

def loopBody369_68 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_67

def loopBody369_69 : HolLoopProg 64 :=
.mark loopBody369_68

def loopBody369_70 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_69

def loopBody369_71 : HolLoopProg 64 :=
.mark loopBody369_70

def loopBody369_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64])

def loopBody369_73 : HolLoopProg 64 :=
.mark loopBody369_72

def loopBody369_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody369_75 : HolLoopProg 64 :=
.mark loopBody369_74

def loopBody369_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody369_77 : HolLoopProg 64 :=
.mark loopBody369_76

def loopBody369_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody369_79 : HolLoopProg 64 :=
.mark loopBody369_78

def loopBody369_80 : HolLoopProg 64 :=
.seq loopBody369_79 loopBody369_1

def loopBody369_81 : HolLoopProg 64 :=
.mark loopBody369_80

def loopBody369_82 : HolLoopProg 64 :=
.seq loopBody369_77 loopBody369_81

def loopBody369_83 : HolLoopProg 64 :=
.mark loopBody369_82

def loopBody369_84 : HolLoopProg 64 :=
.seq loopBody369_83 loopBody369_1

def loopBody369_85 : HolLoopProg 64 :=
.mark loopBody369_84

def loopBody369_86 : HolLoopProg 64 :=
.seq loopBody369_75 loopBody369_85

def loopBody369_87 : HolLoopProg 64 :=
.mark loopBody369_86

def loopBody369_88 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_87

def loopBody369_89 : HolLoopProg 64 :=
.mark loopBody369_88

def loopBody369_90 : HolLoopProg 64 :=
.seq loopBody369_73 loopBody369_89

def loopBody369_91 : HolLoopProg 64 :=
.mark loopBody369_90

def loopBody369_92 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_91

def loopBody369_93 : HolLoopProg 64 :=
.mark loopBody369_92

def loopBody369_94 : HolLoopProg 64 :=
.seq loopBody369_71 loopBody369_93

def loopBody369_95 : HolLoopProg 64 :=
.mark loopBody369_94

def loopBody369_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64])

def loopBody369_97 : HolLoopProg 64 :=
.mark loopBody369_96

def loopBody369_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64))

def loopBody369_99 : HolLoopProg 64 :=
.mark loopBody369_98

def loopBody369_100 : HolLoopProg 64 :=
.seq loopBody369_99 loopBody369_85

def loopBody369_101 : HolLoopProg 64 :=
.mark loopBody369_100

def loopBody369_102 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_101

def loopBody369_103 : HolLoopProg 64 :=
.mark loopBody369_102

def loopBody369_104 : HolLoopProg 64 :=
.seq loopBody369_97 loopBody369_103

def loopBody369_105 : HolLoopProg 64 :=
.mark loopBody369_104

def loopBody369_106 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_105

def loopBody369_107 : HolLoopProg 64 :=
.mark loopBody369_106

def loopBody369_108 : HolLoopProg 64 :=
.seq loopBody369_95 loopBody369_107

def loopBody369_109 : HolLoopProg 64 :=
.mark loopBody369_108

def loopBody369_110 : HolLoopProg 64 :=
.seq loopBody369_37 loopBody369_109

def loopBody369_111 : HolLoopProg 64 :=
.mark loopBody369_110

def loopBody369_112 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_111

def loopBody369_113 : HolLoopProg 64 :=
.mark loopBody369_112

def loopBody369_114 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_113

def loopBody369_115 : HolLoopProg 64 :=
.mark loopBody369_114

def loopBody369_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody369_115 loopBody369_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody369_117 : HolLoopProg 64 :=
.mark loopBody369_116

def loopBody369_118 : HolLoopProg 64 :=
.seq loopBody369_117 loopBody369_1

def loopBody369_119 : HolLoopProg 64 :=
.mark loopBody369_118

def loopBody369_120 : HolLoopProg 64 :=
.seq loopBody369_17 loopBody369_119

def loopBody369_121 : HolLoopProg 64 :=
.mark loopBody369_120

def loopBody369_122 : HolLoopProg 64 :=
.seq loopBody369_15 loopBody369_121

def loopBody369_123 : HolLoopProg 64 :=
.mark loopBody369_122

def loopBody369_124 : HolLoopProg 64 :=
.seq loopBody369_9 loopBody369_123

def loopBody369_125 : HolLoopProg 64 :=
.mark loopBody369_124

def loopBody369_126 : HolLoopProg 64 :=
.seq loopBody369_7 loopBody369_125

def loopBody369_127 : HolLoopProg 64 :=
.mark loopBody369_126

def loopBody369_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64])

def loopBody369_129 : HolLoopProg 64 :=
.mark loopBody369_128

def loopBody369_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 1#64])

def loopBody369_131 : HolLoopProg 64 :=
.mark loopBody369_130

def loopBody369_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody369_133 : HolLoopProg 64 :=
.mark loopBody369_132

def loopBody369_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 4) 6

def loopBody369_135 : HolLoopProg 64 :=
.mark loopBody369_134

def loopBody369_136 : HolLoopProg 64 :=
.seq loopBody369_135 loopBody369_1

def loopBody369_137 : HolLoopProg 64 :=
.mark loopBody369_136

def loopBody369_138 : HolLoopProg 64 :=
.seq loopBody369_133 loopBody369_137

def loopBody369_139 : HolLoopProg 64 :=
.mark loopBody369_138

def loopBody369_140 : HolLoopProg 64 :=
.seq loopBody369_139 loopBody369_1

def loopBody369_141 : HolLoopProg 64 :=
.mark loopBody369_140

def loopBody369_142 : HolLoopProg 64 :=
.seq loopBody369_131 loopBody369_141

def loopBody369_143 : HolLoopProg 64 :=
.mark loopBody369_142

def loopBody369_144 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_143

def loopBody369_145 : HolLoopProg 64 :=
.mark loopBody369_144

def loopBody369_146 : HolLoopProg 64 :=
.seq loopBody369_129 loopBody369_145

def loopBody369_147 : HolLoopProg 64 :=
.mark loopBody369_146

def loopBody369_148 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_147

def loopBody369_149 : HolLoopProg 64 :=
.mark loopBody369_148

def loopBody369_150 : HolLoopProg 64 :=
.seq loopBody369_127 loopBody369_149

def loopBody369_151 : HolLoopProg 64 :=
.mark loopBody369_150

def loopBody369_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody369_153 : HolLoopProg 64 :=
.mark loopBody369_152

def loopBody369_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 6 6 4 5)

def loopBody369_155 : HolLoopProg 64 :=
.mark loopBody369_154

def loopBody369_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]),
      Flapjack.HolLoopExp.var 6])

def loopBody369_157 : HolLoopProg 64 :=
.mark loopBody369_156

def loopBody369_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody369_159 : HolLoopProg 64 :=
.mark loopBody369_158

def loopBody369_160 : HolLoopProg 64 :=
.seq loopBody369_159 loopBody369_1

def loopBody369_161 : HolLoopProg 64 :=
.mark loopBody369_160

def loopBody369_162 : HolLoopProg 64 :=
.seq loopBody369_157 loopBody369_161

def loopBody369_163 : HolLoopProg 64 :=
.mark loopBody369_162

def loopBody369_164 : HolLoopProg 64 :=
.seq loopBody369_155 loopBody369_163

def loopBody369_165 : HolLoopProg 64 :=
.mark loopBody369_164

def loopBody369_166 : HolLoopProg 64 :=
.seq loopBody369_19 loopBody369_165

def loopBody369_167 : HolLoopProg 64 :=
.mark loopBody369_166

def loopBody369_168 : HolLoopProg 64 :=
.seq loopBody369_153 loopBody369_167

def loopBody369_169 : HolLoopProg 64 :=
.mark loopBody369_168

def loopBody369_170 : HolLoopProg 64 :=
.seq loopBody369_151 loopBody369_169

def loopBody369_171 : HolLoopProg 64 :=
.mark loopBody369_170

def loopBody369_172 : HolLoopProg 64 :=
.seq loopBody369_5 loopBody369_171

def loopBody369_173 : HolLoopProg 64 :=
.mark loopBody369_172

def loopBody369_174 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_173

def loopBody369_175 : HolLoopProg 64 :=
.mark loopBody369_174

def loopBody369_176 : HolLoopProg 64 :=
.seq loopBody369_3 loopBody369_175

def loopBody369_177 : HolLoopProg 64 :=
.mark loopBody369_176

def loopBody369_178 : HolLoopProg 64 :=
.seq loopBody369_1 loopBody369_177

def loopBody369_179 : HolLoopProg 64 :=
.mark loopBody369_178

def output369 : Nat × List Nat × HolLoopProg 64 :=
  (433, [0, 1], loopBody369_179)
end InitECandidate.Proofs.FrontendStages.Loop
