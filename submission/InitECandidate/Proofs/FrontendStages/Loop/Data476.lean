import InitECandidate.Proofs.FrontendStages.Loop.Translate460
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody476_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody476_1 : HolLoopProg 64 :=
.mark loopBody476_0

def loopBody476_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 3#64)

def loopBody476_3 : HolLoopProg 64 :=
.mark loopBody476_2

def loopBody476_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody476_5 : HolLoopProg 64 :=
.mark loopBody476_4

def loopBody476_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody476_5, loopBody476_1, (Flapjack.Spt.ln)))

def loopBody476_7 : HolLoopProg 64 :=
.mark loopBody476_6

def loopBody476_8 : HolLoopProg 64 :=
.seq loopBody476_7 loopBody476_1

def loopBody476_9 : HolLoopProg 64 :=
.mark loopBody476_8

def loopBody476_10 : HolLoopProg 64 :=
.seq loopBody476_3 loopBody476_9

def loopBody476_11 : HolLoopProg 64 :=
.mark loopBody476_10

def loopBody476_12 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_11

def loopBody476_13 : HolLoopProg 64 :=
.mark loopBody476_12

def loopBody476_14 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_13

def loopBody476_15 : HolLoopProg 64 :=
.mark loopBody476_14

def loopBody476_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 536) ([]) (some (2, loopBody476_5, loopBody476_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody476_17 : HolLoopProg 64 :=
.mark loopBody476_16

def loopBody476_18 : HolLoopProg 64 :=
.seq loopBody476_17 loopBody476_1

def loopBody476_19 : HolLoopProg 64 :=
.mark loopBody476_18

def loopBody476_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 81#64)

def loopBody476_21 : HolLoopProg 64 :=
.mark loopBody476_20

def loopBody476_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody476_23 : HolLoopProg 64 :=
.mark loopBody476_22

def loopBody476_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody476_25 : HolLoopProg 64 :=
.mark loopBody476_24

def loopBody476_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody476_27 : HolLoopProg 64 :=
.mark loopBody476_26

def loopBody476_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 3 (Flapjack.RegImm.reg 4) loopBody476_25 loopBody476_27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody476_29 : HolLoopProg 64 :=
.mark loopBody476_28

def loopBody476_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody476_31 : HolLoopProg 64 :=
.mark loopBody476_30

def loopBody476_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody476_33 : HolLoopProg 64 :=
.mark loopBody476_32

def loopBody476_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody476_35 : HolLoopProg 64 :=
.mark loopBody476_34

def loopBody476_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody476_35 loopBody476_31 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))

def loopBody476_37 : HolLoopProg 64 :=
.mark loopBody476_36

def loopBody476_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody476_39 : HolLoopProg 64 :=
.mark loopBody476_38

def loopBody476_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 128#64)

def loopBody476_41 : HolLoopProg 64 :=
.mark loopBody476_40

def loopBody476_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody476_43 : HolLoopProg 64 :=
.mark loopBody476_42

def loopBody476_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody476_45 : HolLoopProg 64 :=
.mark loopBody476_44

def loopBody476_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 9 (Flapjack.RegImm.reg 10) loopBody476_43 loopBody476_45 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))

def loopBody476_47 : HolLoopProg 64 :=
.mark loopBody476_46

def loopBody476_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody476_49 : HolLoopProg 64 :=
.mark loopBody476_48

def loopBody476_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 9)

def loopBody476_51 : HolLoopProg 64 :=
.mark loopBody476_50

def loopBody476_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody476_53 : HolLoopProg 64 :=
.mark loopBody476_52

def loopBody476_54 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.reg 13) loopBody476_53 loopBody476_49 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.ls PUnit.unit))

def loopBody476_55 : HolLoopProg 64 :=
.mark loopBody476_54

def loopBody476_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.var 12])

def loopBody476_57 : HolLoopProg 64 :=
.mark loopBody476_56

def loopBody476_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 10#64)

def loopBody476_59 : HolLoopProg 64 :=
.mark loopBody476_58

def loopBody476_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 2)

def loopBody476_61 : HolLoopProg 64 :=
.mark loopBody476_60

def loopBody476_62 : HolLoopProg 64 :=
.seq loopBody476_61 loopBody476_1

def loopBody476_63 : HolLoopProg 64 :=
.mark loopBody476_62

def loopBody476_64 : HolLoopProg 64 :=
.seq loopBody476_63 loopBody476_1

def loopBody476_65 : HolLoopProg 64 :=
.mark loopBody476_64

def loopBody476_66 : HolLoopProg 64 :=
.seq loopBody476_59 loopBody476_65

def loopBody476_67 : HolLoopProg 64 :=
.mark loopBody476_66

def loopBody476_68 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_67

def loopBody476_69 : HolLoopProg 64 :=
.mark loopBody476_68

def loopBody476_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 8#64)

def loopBody476_71 : HolLoopProg 64 :=
.mark loopBody476_70

def loopBody476_72 : HolLoopProg 64 :=
.seq loopBody476_71 loopBody476_5

def loopBody476_73 : HolLoopProg 64 :=
.mark loopBody476_72

def loopBody476_74 : HolLoopProg 64 :=
.seq loopBody476_69 loopBody476_73

def loopBody476_75 : HolLoopProg 64 :=
.mark loopBody476_74

def loopBody476_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody476_75 loopBody476_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody476_77 : HolLoopProg 64 :=
.mark loopBody476_76

def loopBody476_78 : HolLoopProg 64 :=
.seq loopBody476_77 loopBody476_1

def loopBody476_79 : HolLoopProg 64 :=
.mark loopBody476_78

def loopBody476_80 : HolLoopProg 64 :=
.seq loopBody476_57 loopBody476_79

def loopBody476_81 : HolLoopProg 64 :=
.mark loopBody476_80

def loopBody476_82 : HolLoopProg 64 :=
.seq loopBody476_55 loopBody476_81

def loopBody476_83 : HolLoopProg 64 :=
.mark loopBody476_82

def loopBody476_84 : HolLoopProg 64 :=
.seq loopBody476_51 loopBody476_83

def loopBody476_85 : HolLoopProg 64 :=
.mark loopBody476_84

def loopBody476_86 : HolLoopProg 64 :=
.seq loopBody476_49 loopBody476_85

def loopBody476_87 : HolLoopProg 64 :=
.mark loopBody476_86

def loopBody476_88 : HolLoopProg 64 :=
.seq loopBody476_47 loopBody476_87

def loopBody476_89 : HolLoopProg 64 :=
.mark loopBody476_88

def loopBody476_90 : HolLoopProg 64 :=
.seq loopBody476_41 loopBody476_89

def loopBody476_91 : HolLoopProg 64 :=
.mark loopBody476_90

def loopBody476_92 : HolLoopProg 64 :=
.seq loopBody476_39 loopBody476_91

def loopBody476_93 : HolLoopProg 64 :=
.mark loopBody476_92

def loopBody476_94 : HolLoopProg 64 :=
.seq loopBody476_37 loopBody476_93

def loopBody476_95 : HolLoopProg 64 :=
.mark loopBody476_94

def loopBody476_96 : HolLoopProg 64 :=
.seq loopBody476_33 loopBody476_95

def loopBody476_97 : HolLoopProg 64 :=
.mark loopBody476_96

def loopBody476_98 : HolLoopProg 64 :=
.seq loopBody476_31 loopBody476_97

def loopBody476_99 : HolLoopProg 64 :=
.mark loopBody476_98

def loopBody476_100 : HolLoopProg 64 :=
.seq loopBody476_29 loopBody476_99

def loopBody476_101 : HolLoopProg 64 :=
.mark loopBody476_100

def loopBody476_102 : HolLoopProg 64 :=
.seq loopBody476_23 loopBody476_101

def loopBody476_103 : HolLoopProg 64 :=
.mark loopBody476_102

def loopBody476_104 : HolLoopProg 64 :=
.seq loopBody476_21 loopBody476_103

def loopBody476_105 : HolLoopProg 64 :=
.mark loopBody476_104

def loopBody476_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 143#64])

def loopBody476_107 : HolLoopProg 64 :=
.mark loopBody476_106

def loopBody476_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 4#64))

def loopBody476_109 : HolLoopProg 64 :=
.mark loopBody476_108

def loopBody476_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 15#64])

def loopBody476_111 : HolLoopProg 64 :=
.mark loopBody476_110

def loopBody476_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody476_113 : HolLoopProg 64 :=
.mark loopBody476_112

def loopBody476_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody476_115 : HolLoopProg 64 :=
.mark loopBody476_114

def loopBody476_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody476_117 : HolLoopProg 64 :=
.mark loopBody476_116

def loopBody476_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody476_119 : HolLoopProg 64 :=
.mark loopBody476_118

def loopBody476_120 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.RegImm.reg 9) loopBody476_117 loopBody476_119 (Flapjack.Spt.bn
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody476_121 : HolLoopProg 64 :=
.mark loopBody476_120

def loopBody476_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody476_123 : HolLoopProg 64 :=
.mark loopBody476_122

def loopBody476_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody476_125 : HolLoopProg 64 :=
.mark loopBody476_124

def loopBody476_126 : HolLoopProg 64 :=
.seq loopBody476_125 loopBody476_1

def loopBody476_127 : HolLoopProg 64 :=
.mark loopBody476_126

def loopBody476_128 : HolLoopProg 64 :=
.seq loopBody476_127 loopBody476_1

def loopBody476_129 : HolLoopProg 64 :=
.mark loopBody476_128

def loopBody476_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody476_131 : HolLoopProg 64 :=
.mark loopBody476_130

def loopBody476_132 : HolLoopProg 64 :=
.seq loopBody476_131 loopBody476_1

def loopBody476_133 : HolLoopProg 64 :=
.mark loopBody476_132

def loopBody476_134 : HolLoopProg 64 :=
.seq loopBody476_133 loopBody476_1

def loopBody476_135 : HolLoopProg 64 :=
.mark loopBody476_134

def loopBody476_136 : HolLoopProg 64 :=
.seq loopBody476_129 loopBody476_135

def loopBody476_137 : HolLoopProg 64 :=
.mark loopBody476_136

def loopBody476_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody476_139 : HolLoopProg 64 :=
.mark loopBody476_138

def loopBody476_140 : HolLoopProg 64 :=
.seq loopBody476_139 loopBody476_1

def loopBody476_141 : HolLoopProg 64 :=
.mark loopBody476_140

def loopBody476_142 : HolLoopProg 64 :=
.seq loopBody476_141 loopBody476_1

def loopBody476_143 : HolLoopProg 64 :=
.mark loopBody476_142

def loopBody476_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 29#64, Flapjack.HolLoopExp.var 3])

def loopBody476_145 : HolLoopProg 64 :=
.mark loopBody476_144

def loopBody476_146 : HolLoopProg 64 :=
.seq loopBody476_145 loopBody476_1

def loopBody476_147 : HolLoopProg 64 :=
.mark loopBody476_146

def loopBody476_148 : HolLoopProg 64 :=
.seq loopBody476_147 loopBody476_1

def loopBody476_149 : HolLoopProg 64 :=
.mark loopBody476_148

def loopBody476_150 : HolLoopProg 64 :=
.seq loopBody476_143 loopBody476_149

def loopBody476_151 : HolLoopProg 64 :=
.mark loopBody476_150

def loopBody476_152 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody476_137 loopBody476_151 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody476_153 : HolLoopProg 64 :=
.mark loopBody476_152

def loopBody476_154 : HolLoopProg 64 :=
.seq loopBody476_153 loopBody476_1

def loopBody476_155 : HolLoopProg 64 :=
.mark loopBody476_154

def loopBody476_156 : HolLoopProg 64 :=
.seq loopBody476_123 loopBody476_155

def loopBody476_157 : HolLoopProg 64 :=
.mark loopBody476_156

def loopBody476_158 : HolLoopProg 64 :=
.seq loopBody476_121 loopBody476_157

def loopBody476_159 : HolLoopProg 64 :=
.mark loopBody476_158

def loopBody476_160 : HolLoopProg 64 :=
.seq loopBody476_115 loopBody476_159

def loopBody476_161 : HolLoopProg 64 :=
.mark loopBody476_160

def loopBody476_162 : HolLoopProg 64 :=
.seq loopBody476_113 loopBody476_161

def loopBody476_163 : HolLoopProg 64 :=
.mark loopBody476_162

def loopBody476_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody476_165 : HolLoopProg 64 :=
.mark loopBody476_164

def loopBody476_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody476_167 : HolLoopProg 64 :=
.mark loopBody476_166

def loopBody476_168 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody476_169 : HolLoopProg 64 :=
.mark loopBody476_168

def loopBody476_170 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 93) ([8, 9]) (some (8, loopBody476_169, loopBody476_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody476_171 : HolLoopProg 64 :=
.mark loopBody476_170

def loopBody476_172 : HolLoopProg 64 :=
.seq loopBody476_171 loopBody476_1

def loopBody476_173 : HolLoopProg 64 :=
.mark loopBody476_172

def loopBody476_174 : HolLoopProg 64 :=
.seq loopBody476_167 loopBody476_173

def loopBody476_175 : HolLoopProg 64 :=
.mark loopBody476_174

def loopBody476_176 : HolLoopProg 64 :=
.seq loopBody476_165 loopBody476_175

def loopBody476_177 : HolLoopProg 64 :=
.mark loopBody476_176

def loopBody476_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody476_179 : HolLoopProg 64 :=
.mark loopBody476_178

def loopBody476_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 1#64])

def loopBody476_181 : HolLoopProg 64 :=
.mark loopBody476_180

def loopBody476_182 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 9 (Flapjack.RegImm.reg 10) loopBody476_43 loopBody476_45 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody476_183 : HolLoopProg 64 :=
.mark loopBody476_182

def loopBody476_184 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody476_185 : HolLoopProg 64 :=
.mark loopBody476_184

def loopBody476_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 2#64)

def loopBody476_187 : HolLoopProg 64 :=
.mark loopBody476_186

def loopBody476_188 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 8)

def loopBody476_189 : HolLoopProg 64 :=
.mark loopBody476_188

def loopBody476_190 : HolLoopProg 64 :=
.seq loopBody476_189 loopBody476_1

def loopBody476_191 : HolLoopProg 64 :=
.mark loopBody476_190

def loopBody476_192 : HolLoopProg 64 :=
.seq loopBody476_191 loopBody476_1

def loopBody476_193 : HolLoopProg 64 :=
.mark loopBody476_192

def loopBody476_194 : HolLoopProg 64 :=
.seq loopBody476_187 loopBody476_193

def loopBody476_195 : HolLoopProg 64 :=
.mark loopBody476_194

def loopBody476_196 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_195

def loopBody476_197 : HolLoopProg 64 :=
.mark loopBody476_196

def loopBody476_198 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 8#64)

def loopBody476_199 : HolLoopProg 64 :=
.mark loopBody476_198

def loopBody476_200 : HolLoopProg 64 :=
.seq loopBody476_199 loopBody476_169

def loopBody476_201 : HolLoopProg 64 :=
.mark loopBody476_200

def loopBody476_202 : HolLoopProg 64 :=
.seq loopBody476_197 loopBody476_201

def loopBody476_203 : HolLoopProg 64 :=
.mark loopBody476_202

def loopBody476_204 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody476_203 loopBody476_1 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody476_205 : HolLoopProg 64 :=
.mark loopBody476_204

def loopBody476_206 : HolLoopProg 64 :=
.seq loopBody476_205 loopBody476_1

def loopBody476_207 : HolLoopProg 64 :=
.mark loopBody476_206

def loopBody476_208 : HolLoopProg 64 :=
.seq loopBody476_185 loopBody476_207

def loopBody476_209 : HolLoopProg 64 :=
.mark loopBody476_208

def loopBody476_210 : HolLoopProg 64 :=
.seq loopBody476_183 loopBody476_209

def loopBody476_211 : HolLoopProg 64 :=
.mark loopBody476_210

def loopBody476_212 : HolLoopProg 64 :=
.seq loopBody476_181 loopBody476_211

def loopBody476_213 : HolLoopProg 64 :=
.mark loopBody476_212

def loopBody476_214 : HolLoopProg 64 :=
.seq loopBody476_179 loopBody476_213

def loopBody476_215 : HolLoopProg 64 :=
.mark loopBody476_214

def loopBody476_216 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody476_217 : HolLoopProg 64 :=
.mark loopBody476_216

def loopBody476_218 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody476_219 : HolLoopProg 64 :=
.mark loopBody476_218

def loopBody476_220 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody476_221 : HolLoopProg 64 :=
.mark loopBody476_220

def loopBody476_222 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 534) ([9, 10]) (some (9, loopBody476_221, loopBody476_1, (Flapjack.Spt.ln)))

def loopBody476_223 : HolLoopProg 64 :=
.mark loopBody476_222

def loopBody476_224 : HolLoopProg 64 :=
.seq loopBody476_223 loopBody476_1

def loopBody476_225 : HolLoopProg 64 :=
.mark loopBody476_224

def loopBody476_226 : HolLoopProg 64 :=
.seq loopBody476_219 loopBody476_225

def loopBody476_227 : HolLoopProg 64 :=
.mark loopBody476_226

def loopBody476_228 : HolLoopProg 64 :=
.seq loopBody476_217 loopBody476_227

def loopBody476_229 : HolLoopProg 64 :=
.mark loopBody476_228

def loopBody476_230 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_229

def loopBody476_231 : HolLoopProg 64 :=
.mark loopBody476_230

def loopBody476_232 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_231

def loopBody476_233 : HolLoopProg 64 :=
.mark loopBody476_232

def loopBody476_234 : HolLoopProg 64 :=
.seq loopBody476_215 loopBody476_233

def loopBody476_235 : HolLoopProg 64 :=
.mark loopBody476_234

def loopBody476_236 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 2#64)

def loopBody476_237 : HolLoopProg 64 :=
.mark loopBody476_236

def loopBody476_238 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 486) ([9]) (some (9, loopBody476_221, loopBody476_1, (Flapjack.Spt.ln)))

def loopBody476_239 : HolLoopProg 64 :=
.mark loopBody476_238

def loopBody476_240 : HolLoopProg 64 :=
.seq loopBody476_239 loopBody476_1

def loopBody476_241 : HolLoopProg 64 :=
.mark loopBody476_240

def loopBody476_242 : HolLoopProg 64 :=
.seq loopBody476_237 loopBody476_241

def loopBody476_243 : HolLoopProg 64 :=
.mark loopBody476_242

def loopBody476_244 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_243

def loopBody476_245 : HolLoopProg 64 :=
.mark loopBody476_244

def loopBody476_246 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_245

def loopBody476_247 : HolLoopProg 64 :=
.mark loopBody476_246

def loopBody476_248 : HolLoopProg 64 :=
.seq loopBody476_235 loopBody476_247

def loopBody476_249 : HolLoopProg 64 :=
.mark loopBody476_248

def loopBody476_250 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody476_251 : HolLoopProg 64 :=
.mark loopBody476_250

def loopBody476_252 : HolLoopProg 64 :=
.seq loopBody476_251 loopBody476_1

def loopBody476_253 : HolLoopProg 64 :=
.mark loopBody476_252

def loopBody476_254 : HolLoopProg 64 :=
.seq loopBody476_119 loopBody476_253

def loopBody476_255 : HolLoopProg 64 :=
.mark loopBody476_254

def loopBody476_256 : HolLoopProg 64 :=
.seq loopBody476_249 loopBody476_255

def loopBody476_257 : HolLoopProg 64 :=
.mark loopBody476_256

def loopBody476_258 : HolLoopProg 64 :=
.seq loopBody476_177 loopBody476_257

def loopBody476_259 : HolLoopProg 64 :=
.mark loopBody476_258

def loopBody476_260 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_259

def loopBody476_261 : HolLoopProg 64 :=
.mark loopBody476_260

def loopBody476_262 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_261

def loopBody476_263 : HolLoopProg 64 :=
.mark loopBody476_262

def loopBody476_264 : HolLoopProg 64 :=
.seq loopBody476_163 loopBody476_263

def loopBody476_265 : HolLoopProg 64 :=
.mark loopBody476_264

def loopBody476_266 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_265

def loopBody476_267 : HolLoopProg 64 :=
.mark loopBody476_266

def loopBody476_268 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_267

def loopBody476_269 : HolLoopProg 64 :=
.mark loopBody476_268

def loopBody476_270 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_269

def loopBody476_271 : HolLoopProg 64 :=
.mark loopBody476_270

def loopBody476_272 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_271

def loopBody476_273 : HolLoopProg 64 :=
.mark loopBody476_272

def loopBody476_274 : HolLoopProg 64 :=
.seq loopBody476_111 loopBody476_273

def loopBody476_275 : HolLoopProg 64 :=
.mark loopBody476_274

def loopBody476_276 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_275

def loopBody476_277 : HolLoopProg 64 :=
.mark loopBody476_276

def loopBody476_278 : HolLoopProg 64 :=
.seq loopBody476_109 loopBody476_277

def loopBody476_279 : HolLoopProg 64 :=
.mark loopBody476_278

def loopBody476_280 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_279

def loopBody476_281 : HolLoopProg 64 :=
.mark loopBody476_280

def loopBody476_282 : HolLoopProg 64 :=
.seq loopBody476_107 loopBody476_281

def loopBody476_283 : HolLoopProg 64 :=
.mark loopBody476_282

def loopBody476_284 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_283

def loopBody476_285 : HolLoopProg 64 :=
.mark loopBody476_284

def loopBody476_286 : HolLoopProg 64 :=
.seq loopBody476_105 loopBody476_285

def loopBody476_287 : HolLoopProg 64 :=
.mark loopBody476_286

def loopBody476_288 : HolLoopProg 64 :=
.seq loopBody476_19 loopBody476_287

def loopBody476_289 : HolLoopProg 64 :=
.mark loopBody476_288

def loopBody476_290 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_289

def loopBody476_291 : HolLoopProg 64 :=
.mark loopBody476_290

def loopBody476_292 : HolLoopProg 64 :=
.seq loopBody476_1 loopBody476_291

def loopBody476_293 : HolLoopProg 64 :=
.mark loopBody476_292

def loopBody476_294 : HolLoopProg 64 :=
.seq loopBody476_15 loopBody476_293

def loopBody476_295 : HolLoopProg 64 :=
.mark loopBody476_294

def output476 : Nat × List Nat × HolLoopProg 64 :=
  (540, [], loopBody476_295)
end InitECandidate.Proofs.FrontendStages.Loop
