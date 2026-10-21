import InitECandidate.Proofs.FrontendStages.Loop.Translate367
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody383_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody383_1 : HolLoopProg 64 :=
.mark loopBody383_0

def loopBody383_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody383_3 : HolLoopProg 64 :=
.mark loopBody383_2

def loopBody383_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody383_5 : HolLoopProg 64 :=
.mark loopBody383_4

def loopBody383_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody383_7 : HolLoopProg 64 :=
.mark loopBody383_6

def loopBody383_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody383_9 : HolLoopProg 64 :=
.mark loopBody383_8

def loopBody383_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody383_11 : HolLoopProg 64 :=
.mark loopBody383_10

def loopBody383_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody383_13 : HolLoopProg 64 :=
.mark loopBody383_12

def loopBody383_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody383_15 : HolLoopProg 64 :=
.mark loopBody383_14

def loopBody383_16 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 7 (Flapjack.RegImm.reg 8) loopBody383_13 loopBody383_15 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody383_17 : HolLoopProg 64 :=
.mark loopBody383_16

def loopBody383_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody383_19 : HolLoopProg 64 :=
.mark loopBody383_18

def loopBody383_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody383_21 : HolLoopProg 64 :=
.mark loopBody383_20

def loopBody383_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody383_23 : HolLoopProg 64 :=
.mark loopBody383_22

def loopBody383_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 8 8 6 7)

def loopBody383_25 : HolLoopProg 64 :=
.mark loopBody383_24

def loopBody383_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 8]))

def loopBody383_27 : HolLoopProg 64 :=
.mark loopBody383_26

def loopBody383_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody383_29 : HolLoopProg 64 :=
.mark loopBody383_28

def loopBody383_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody383_31 : HolLoopProg 64 :=
.mark loopBody383_30

def loopBody383_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody383_33 : HolLoopProg 64 :=
.mark loopBody383_32

def loopBody383_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.RegImm.reg 11) loopBody383_31 loopBody383_33 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody383_35 : HolLoopProg 64 :=
.mark loopBody383_34

def loopBody383_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody383_37 : HolLoopProg 64 :=
.mark loopBody383_36

def loopBody383_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody383_39 : HolLoopProg 64 :=
.mark loopBody383_38

def loopBody383_40 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.reg 8) loopBody383_13 loopBody383_15 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody383_41 : HolLoopProg 64 :=
.mark loopBody383_40

def loopBody383_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody383_43 : HolLoopProg 64 :=
.mark loopBody383_42

def loopBody383_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 9 9 7 8)

def loopBody383_45 : HolLoopProg 64 :=
.mark loopBody383_44

def loopBody383_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody383_47 : HolLoopProg 64 :=
.mark loopBody383_46

def loopBody383_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 1)

def loopBody383_49 : HolLoopProg 64 :=
.mark loopBody383_48

def loopBody383_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 12 12 10 11)

def loopBody383_51 : HolLoopProg 64 :=
.mark loopBody383_50

def loopBody383_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 9])

def loopBody383_53 : HolLoopProg 64 :=
.mark loopBody383_52

def loopBody383_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 12])

def loopBody383_55 : HolLoopProg 64 :=
.mark loopBody383_54

def loopBody383_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 1)

def loopBody383_57 : HolLoopProg 64 :=
.mark loopBody383_56

def loopBody383_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody383_59 : HolLoopProg 64 :=
.mark loopBody383_58

def loopBody383_60 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([13, 14, 15]) (some (7, loopBody383_59, loopBody383_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody383_61 : HolLoopProg 64 :=
.mark loopBody383_60

def loopBody383_62 : HolLoopProg 64 :=
.seq loopBody383_61 loopBody383_1

def loopBody383_63 : HolLoopProg 64 :=
.mark loopBody383_62

def loopBody383_64 : HolLoopProg 64 :=
.seq loopBody383_57 loopBody383_63

def loopBody383_65 : HolLoopProg 64 :=
.mark loopBody383_64

def loopBody383_66 : HolLoopProg 64 :=
.seq loopBody383_55 loopBody383_65

def loopBody383_67 : HolLoopProg 64 :=
.mark loopBody383_66

def loopBody383_68 : HolLoopProg 64 :=
.seq loopBody383_53 loopBody383_67

def loopBody383_69 : HolLoopProg 64 :=
.mark loopBody383_68

def loopBody383_70 : HolLoopProg 64 :=
.seq loopBody383_51 loopBody383_69

def loopBody383_71 : HolLoopProg 64 :=
.mark loopBody383_70

def loopBody383_72 : HolLoopProg 64 :=
.seq loopBody383_49 loopBody383_71

def loopBody383_73 : HolLoopProg 64 :=
.mark loopBody383_72

def loopBody383_74 : HolLoopProg 64 :=
.seq loopBody383_47 loopBody383_73

def loopBody383_75 : HolLoopProg 64 :=
.mark loopBody383_74

def loopBody383_76 : HolLoopProg 64 :=
.seq loopBody383_45 loopBody383_75

def loopBody383_77 : HolLoopProg 64 :=
.mark loopBody383_76

def loopBody383_78 : HolLoopProg 64 :=
.seq loopBody383_43 loopBody383_77

def loopBody383_79 : HolLoopProg 64 :=
.mark loopBody383_78

def loopBody383_80 : HolLoopProg 64 :=
.seq loopBody383_9 loopBody383_79

def loopBody383_81 : HolLoopProg 64 :=
.mark loopBody383_80

def loopBody383_82 : HolLoopProg 64 :=
.seq loopBody383_1 loopBody383_81

def loopBody383_83 : HolLoopProg 64 :=
.mark loopBody383_82

def loopBody383_84 : HolLoopProg 64 :=
.seq loopBody383_1 loopBody383_83

def loopBody383_85 : HolLoopProg 64 :=
.mark loopBody383_84

def loopBody383_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody383_85 loopBody383_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody383_87 : HolLoopProg 64 :=
.mark loopBody383_86

def loopBody383_88 : HolLoopProg 64 :=
.seq loopBody383_87 loopBody383_1

def loopBody383_89 : HolLoopProg 64 :=
.mark loopBody383_88

def loopBody383_90 : HolLoopProg 64 :=
.seq loopBody383_19 loopBody383_89

def loopBody383_91 : HolLoopProg 64 :=
.mark loopBody383_90

def loopBody383_92 : HolLoopProg 64 :=
.seq loopBody383_41 loopBody383_91

def loopBody383_93 : HolLoopProg 64 :=
.mark loopBody383_92

def loopBody383_94 : HolLoopProg 64 :=
.seq loopBody383_39 loopBody383_93

def loopBody383_95 : HolLoopProg 64 :=
.mark loopBody383_94

def loopBody383_96 : HolLoopProg 64 :=
.seq loopBody383_9 loopBody383_95

def loopBody383_97 : HolLoopProg 64 :=
.mark loopBody383_96

def loopBody383_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64])

def loopBody383_99 : HolLoopProg 64 :=
.mark loopBody383_98

def loopBody383_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody383_101 : HolLoopProg 64 :=
.mark loopBody383_100

def loopBody383_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody383_103 : HolLoopProg 64 :=
.mark loopBody383_102

def loopBody383_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 6) 8

def loopBody383_105 : HolLoopProg 64 :=
.mark loopBody383_104

def loopBody383_106 : HolLoopProg 64 :=
.seq loopBody383_105 loopBody383_1

def loopBody383_107 : HolLoopProg 64 :=
.mark loopBody383_106

def loopBody383_108 : HolLoopProg 64 :=
.seq loopBody383_103 loopBody383_107

def loopBody383_109 : HolLoopProg 64 :=
.mark loopBody383_108

def loopBody383_110 : HolLoopProg 64 :=
.seq loopBody383_109 loopBody383_1

def loopBody383_111 : HolLoopProg 64 :=
.mark loopBody383_110

def loopBody383_112 : HolLoopProg 64 :=
.seq loopBody383_101 loopBody383_111

def loopBody383_113 : HolLoopProg 64 :=
.mark loopBody383_112

def loopBody383_114 : HolLoopProg 64 :=
.seq loopBody383_1 loopBody383_113

def loopBody383_115 : HolLoopProg 64 :=
.mark loopBody383_114

def loopBody383_116 : HolLoopProg 64 :=
.seq loopBody383_99 loopBody383_115

def loopBody383_117 : HolLoopProg 64 :=
.mark loopBody383_116

def loopBody383_118 : HolLoopProg 64 :=
.seq loopBody383_1 loopBody383_117

def loopBody383_119 : HolLoopProg 64 :=
.mark loopBody383_118

def loopBody383_120 : HolLoopProg 64 :=
.seq loopBody383_97 loopBody383_119

def loopBody383_121 : HolLoopProg 64 :=
.mark loopBody383_120

def loopBody383_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody383_123 : HolLoopProg 64 :=
.mark loopBody383_122

def loopBody383_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody383_125 : HolLoopProg 64 :=
.mark loopBody383_124

def loopBody383_126 : HolLoopProg 64 :=
.seq loopBody383_125 loopBody383_1

def loopBody383_127 : HolLoopProg 64 :=
.mark loopBody383_126

def loopBody383_128 : HolLoopProg 64 :=
.seq loopBody383_123 loopBody383_127

def loopBody383_129 : HolLoopProg 64 :=
.mark loopBody383_128

def loopBody383_130 : HolLoopProg 64 :=
.seq loopBody383_121 loopBody383_129

def loopBody383_131 : HolLoopProg 64 :=
.mark loopBody383_130

def loopBody383_132 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody383_131 loopBody383_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody383_133 : HolLoopProg 64 :=
.mark loopBody383_132

def loopBody383_134 : HolLoopProg 64 :=
.seq loopBody383_133 loopBody383_1

def loopBody383_135 : HolLoopProg 64 :=
.mark loopBody383_134

def loopBody383_136 : HolLoopProg 64 :=
.seq loopBody383_37 loopBody383_135

def loopBody383_137 : HolLoopProg 64 :=
.mark loopBody383_136

def loopBody383_138 : HolLoopProg 64 :=
.seq loopBody383_35 loopBody383_137

def loopBody383_139 : HolLoopProg 64 :=
.mark loopBody383_138

def loopBody383_140 : HolLoopProg 64 :=
.seq loopBody383_29 loopBody383_139

def loopBody383_141 : HolLoopProg 64 :=
.mark loopBody383_140

def loopBody383_142 : HolLoopProg 64 :=
.seq loopBody383_27 loopBody383_141

def loopBody383_143 : HolLoopProg 64 :=
.mark loopBody383_142

def loopBody383_144 : HolLoopProg 64 :=
.seq loopBody383_25 loopBody383_143

def loopBody383_145 : HolLoopProg 64 :=
.mark loopBody383_144

def loopBody383_146 : HolLoopProg 64 :=
.seq loopBody383_23 loopBody383_145

def loopBody383_147 : HolLoopProg 64 :=
.mark loopBody383_146

def loopBody383_148 : HolLoopProg 64 :=
.seq loopBody383_21 loopBody383_147

def loopBody383_149 : HolLoopProg 64 :=
.mark loopBody383_148

def loopBody383_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody383_151 : HolLoopProg 64 :=
.mark loopBody383_150

def loopBody383_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 6)

def loopBody383_153 : HolLoopProg 64 :=
.mark loopBody383_152

def loopBody383_154 : HolLoopProg 64 :=
.seq loopBody383_153 loopBody383_1

def loopBody383_155 : HolLoopProg 64 :=
.mark loopBody383_154

def loopBody383_156 : HolLoopProg 64 :=
.seq loopBody383_155 loopBody383_1

def loopBody383_157 : HolLoopProg 64 :=
.mark loopBody383_156

def loopBody383_158 : HolLoopProg 64 :=
.seq loopBody383_151 loopBody383_157

def loopBody383_159 : HolLoopProg 64 :=
.mark loopBody383_158

def loopBody383_160 : HolLoopProg 64 :=
.seq loopBody383_1 loopBody383_159

def loopBody383_161 : HolLoopProg 64 :=
.mark loopBody383_160

def loopBody383_162 : HolLoopProg 64 :=
.seq loopBody383_149 loopBody383_161

def loopBody383_163 : HolLoopProg 64 :=
.mark loopBody383_162

def loopBody383_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody383_165 : HolLoopProg 64 :=
.mark loopBody383_164

def loopBody383_166 : HolLoopProg 64 :=
.seq loopBody383_163 loopBody383_165

def loopBody383_167 : HolLoopProg 64 :=
.mark loopBody383_166

def loopBody383_168 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody383_169 : HolLoopProg 64 :=
.mark loopBody383_168

def loopBody383_170 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody383_167 loopBody383_169 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody383_171 : HolLoopProg 64 :=
.mark loopBody383_170

def loopBody383_172 : HolLoopProg 64 :=
.seq loopBody383_171 loopBody383_1

def loopBody383_173 : HolLoopProg 64 :=
.mark loopBody383_172

def loopBody383_174 : HolLoopProg 64 :=
.seq loopBody383_19 loopBody383_173

def loopBody383_175 : HolLoopProg 64 :=
.mark loopBody383_174

def loopBody383_176 : HolLoopProg 64 :=
.seq loopBody383_17 loopBody383_175

def loopBody383_177 : HolLoopProg 64 :=
.mark loopBody383_176

def loopBody383_178 : HolLoopProg 64 :=
.seq loopBody383_11 loopBody383_177

def loopBody383_179 : HolLoopProg 64 :=
.mark loopBody383_178

def loopBody383_180 : HolLoopProg 64 :=
.seq loopBody383_9 loopBody383_179

def loopBody383_181 : HolLoopProg 64 :=
.mark loopBody383_180

def loopBody383_182 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody383_181 (Flapjack.Spt.ln)

def loopBody383_183 : HolLoopProg 64 :=
.seq loopBody383_182 loopBody383_129

def loopBody383_184 : HolLoopProg 64 :=
.seq loopBody383_7 loopBody383_183

def loopBody383_185 : HolLoopProg 64 :=
.seq loopBody383_1 loopBody383_184

def loopBody383_186 : HolLoopProg 64 :=
.seq loopBody383_5 loopBody383_185

def loopBody383_187 : HolLoopProg 64 :=
.seq loopBody383_1 loopBody383_186

def loopBody383_188 : HolLoopProg 64 :=
.seq loopBody383_3 loopBody383_187

def loopBody383_189 : HolLoopProg 64 :=
.seq loopBody383_1 loopBody383_188

def output383 : Nat × List Nat × HolLoopProg 64 :=
  (447, [0, 1, 2], loopBody383_189)
end InitECandidate.Proofs.FrontendStages.Loop
