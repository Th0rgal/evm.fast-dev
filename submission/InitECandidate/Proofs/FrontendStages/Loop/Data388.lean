import InitECandidate.Proofs.FrontendStages.Loop.Translate372
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody388_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody388_1 : HolLoopProg 64 :=
.mark loopBody388_0

def loopBody388_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody388_3 : HolLoopProg 64 :=
.mark loopBody388_2

def loopBody388_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody388_5 : HolLoopProg 64 :=
.mark loopBody388_4

def loopBody388_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody388_7 : HolLoopProg 64 :=
.mark loopBody388_6

def loopBody388_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody388_5 loopBody388_7 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))

def loopBody388_9 : HolLoopProg 64 :=
.mark loopBody388_8

def loopBody388_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody388_11 : HolLoopProg 64 :=
.mark loopBody388_10

def loopBody388_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 1))

def loopBody388_13 : HolLoopProg 64 :=
.mark loopBody388_12

def loopBody388_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 0))

def loopBody388_15 : HolLoopProg 64 :=
.mark loopBody388_14

def loopBody388_16 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.RegImm.reg 5) loopBody388_5 loopBody388_7 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody388_17 : HolLoopProg 64 :=
.mark loopBody388_16

def loopBody388_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody388_19 : HolLoopProg 64 :=
.mark loopBody388_18

def loopBody388_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody388_21 : HolLoopProg 64 :=
.mark loopBody388_20

def loopBody388_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody388_23 : HolLoopProg 64 :=
.mark loopBody388_22

def loopBody388_24 : HolLoopProg 64 :=
.seq loopBody388_21 loopBody388_23

def loopBody388_25 : HolLoopProg 64 :=
.mark loopBody388_24

def loopBody388_26 : HolLoopProg 64 :=
.seq loopBody388_19 loopBody388_25

def loopBody388_27 : HolLoopProg 64 :=
.mark loopBody388_26

def loopBody388_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody388_27 loopBody388_23 (Flapjack.Spt.ln)

def loopBody388_29 : HolLoopProg 64 :=
.mark loopBody388_28

def loopBody388_30 : HolLoopProg 64 :=
.seq loopBody388_29 loopBody388_23

def loopBody388_31 : HolLoopProg 64 :=
.mark loopBody388_30

def loopBody388_32 : HolLoopProg 64 :=
.seq loopBody388_11 loopBody388_31

def loopBody388_33 : HolLoopProg 64 :=
.mark loopBody388_32

def loopBody388_34 : HolLoopProg 64 :=
.seq loopBody388_17 loopBody388_33

def loopBody388_35 : HolLoopProg 64 :=
.mark loopBody388_34

def loopBody388_36 : HolLoopProg 64 :=
.seq loopBody388_15 loopBody388_35

def loopBody388_37 : HolLoopProg 64 :=
.mark loopBody388_36

def loopBody388_38 : HolLoopProg 64 :=
.seq loopBody388_13 loopBody388_37

def loopBody388_39 : HolLoopProg 64 :=
.mark loopBody388_38

def loopBody388_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody388_41 : HolLoopProg 64 :=
.mark loopBody388_40

def loopBody388_42 : HolLoopProg 64 :=
.seq loopBody388_41 loopBody388_25

def loopBody388_43 : HolLoopProg 64 :=
.mark loopBody388_42

def loopBody388_44 : HolLoopProg 64 :=
.seq loopBody388_39 loopBody388_43

def loopBody388_45 : HolLoopProg 64 :=
.mark loopBody388_44

def loopBody388_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody388_45 loopBody388_23 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody388_47 : HolLoopProg 64 :=
.mark loopBody388_46

def loopBody388_48 : HolLoopProg 64 :=
.seq loopBody388_47 loopBody388_23

def loopBody388_49 : HolLoopProg 64 :=
.mark loopBody388_48

def loopBody388_50 : HolLoopProg 64 :=
.seq loopBody388_11 loopBody388_49

def loopBody388_51 : HolLoopProg 64 :=
.mark loopBody388_50

def loopBody388_52 : HolLoopProg 64 :=
.seq loopBody388_9 loopBody388_51

def loopBody388_53 : HolLoopProg 64 :=
.mark loopBody388_52

def loopBody388_54 : HolLoopProg 64 :=
.seq loopBody388_3 loopBody388_53

def loopBody388_55 : HolLoopProg 64 :=
.mark loopBody388_54

def loopBody388_56 : HolLoopProg 64 :=
.seq loopBody388_1 loopBody388_55

def loopBody388_57 : HolLoopProg 64 :=
.mark loopBody388_56

def loopBody388_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 20#64)

def loopBody388_59 : HolLoopProg 64 :=
.mark loopBody388_58

def loopBody388_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody388_61 : HolLoopProg 64 :=
.mark loopBody388_60

def loopBody388_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 2#64)

def loopBody388_63 : HolLoopProg 64 :=
.mark loopBody388_62

def loopBody388_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody388_65 : HolLoopProg 64 :=
.mark loopBody388_64

def loopBody388_66 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody388_65 loopBody388_3 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody388_67 : HolLoopProg 64 :=
.mark loopBody388_66

def loopBody388_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody388_69 : HolLoopProg 64 :=
.mark loopBody388_68

def loopBody388_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 32#64)

def loopBody388_71 : HolLoopProg 64 :=
.mark loopBody388_70

def loopBody388_72 : HolLoopProg 64 :=
.seq loopBody388_71 loopBody388_23

def loopBody388_73 : HolLoopProg 64 :=
.mark loopBody388_72

def loopBody388_74 : HolLoopProg 64 :=
.seq loopBody388_73 loopBody388_23

def loopBody388_75 : HolLoopProg 64 :=
.mark loopBody388_74

def loopBody388_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody388_75 loopBody388_23 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody388_77 : HolLoopProg 64 :=
.mark loopBody388_76

def loopBody388_78 : HolLoopProg 64 :=
.seq loopBody388_77 loopBody388_23

def loopBody388_79 : HolLoopProg 64 :=
.mark loopBody388_78

def loopBody388_80 : HolLoopProg 64 :=
.seq loopBody388_69 loopBody388_79

def loopBody388_81 : HolLoopProg 64 :=
.mark loopBody388_80

def loopBody388_82 : HolLoopProg 64 :=
.seq loopBody388_67 loopBody388_81

def loopBody388_83 : HolLoopProg 64 :=
.mark loopBody388_82

def loopBody388_84 : HolLoopProg 64 :=
.seq loopBody388_63 loopBody388_83

def loopBody388_85 : HolLoopProg 64 :=
.mark loopBody388_84

def loopBody388_86 : HolLoopProg 64 :=
.seq loopBody388_61 loopBody388_85

def loopBody388_87 : HolLoopProg 64 :=
.mark loopBody388_86

def loopBody388_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody388_89 : HolLoopProg 64 :=
.mark loopBody388_88

def loopBody388_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody388_91 : HolLoopProg 64 :=
.mark loopBody388_90

def loopBody388_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody388_93 : HolLoopProg 64 :=
.mark loopBody388_92

def loopBody388_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 6 (Flapjack.RegImm.reg 7) loopBody388_91 loopBody388_93 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody388_95 : HolLoopProg 64 :=
.mark loopBody388_94

def loopBody388_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody388_97 : HolLoopProg 64 :=
.mark loopBody388_96

def loopBody388_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 4])

def loopBody388_99 : HolLoopProg 64 :=
.mark loopBody388_98

def loopBody388_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 5 5

def loopBody388_101 : HolLoopProg 64 :=
.mark loopBody388_100

def loopBody388_102 : HolLoopProg 64 :=
.seq loopBody388_101 loopBody388_23

def loopBody388_103 : HolLoopProg 64 :=
.mark loopBody388_102

def loopBody388_104 : HolLoopProg 64 :=
.seq loopBody388_99 loopBody388_103

def loopBody388_105 : HolLoopProg 64 :=
.mark loopBody388_104

def loopBody388_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody388_107 : HolLoopProg 64 :=
.mark loopBody388_106

def loopBody388_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 4])

def loopBody388_109 : HolLoopProg 64 :=
.mark loopBody388_108

def loopBody388_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 7 7

def loopBody388_111 : HolLoopProg 64 :=
.mark loopBody388_110

def loopBody388_112 : HolLoopProg 64 :=
.seq loopBody388_111 loopBody388_23

def loopBody388_113 : HolLoopProg 64 :=
.mark loopBody388_112

def loopBody388_114 : HolLoopProg 64 :=
.seq loopBody388_109 loopBody388_113

def loopBody388_115 : HolLoopProg 64 :=
.mark loopBody388_114

def loopBody388_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody388_117 : HolLoopProg 64 :=
.mark loopBody388_116

def loopBody388_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody388_119 : HolLoopProg 64 :=
.mark loopBody388_118

def loopBody388_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody388_121 : HolLoopProg 64 :=
.mark loopBody388_120

def loopBody388_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody388_123 : HolLoopProg 64 :=
.mark loopBody388_122

def loopBody388_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody388_125 : HolLoopProg 64 :=
.mark loopBody388_124

def loopBody388_126 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.reg 11) loopBody388_123 loopBody388_125 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody388_127 : HolLoopProg 64 :=
.mark loopBody388_126

def loopBody388_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody388_129 : HolLoopProg 64 :=
.mark loopBody388_128

def loopBody388_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody388_131 : HolLoopProg 64 :=
.mark loopBody388_130

def loopBody388_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody388_133 : HolLoopProg 64 :=
.mark loopBody388_132

def loopBody388_134 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.RegImm.reg 11) loopBody388_123 loopBody388_125 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
  Flapjack.Spt.ln)

def loopBody388_135 : HolLoopProg 64 :=
.mark loopBody388_134

def loopBody388_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody388_137 : HolLoopProg 64 :=
.mark loopBody388_136

def loopBody388_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9]

def loopBody388_139 : HolLoopProg 64 :=
.mark loopBody388_138

def loopBody388_140 : HolLoopProg 64 :=
.seq loopBody388_139 loopBody388_23

def loopBody388_141 : HolLoopProg 64 :=
.mark loopBody388_140

def loopBody388_142 : HolLoopProg 64 :=
.seq loopBody388_137 loopBody388_141

def loopBody388_143 : HolLoopProg 64 :=
.mark loopBody388_142

def loopBody388_144 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody388_143 loopBody388_23 (Flapjack.Spt.ln)

def loopBody388_145 : HolLoopProg 64 :=
.mark loopBody388_144

def loopBody388_146 : HolLoopProg 64 :=
.seq loopBody388_145 loopBody388_23

def loopBody388_147 : HolLoopProg 64 :=
.mark loopBody388_146

def loopBody388_148 : HolLoopProg 64 :=
.seq loopBody388_129 loopBody388_147

def loopBody388_149 : HolLoopProg 64 :=
.mark loopBody388_148

def loopBody388_150 : HolLoopProg 64 :=
.seq loopBody388_135 loopBody388_149

def loopBody388_151 : HolLoopProg 64 :=
.mark loopBody388_150

def loopBody388_152 : HolLoopProg 64 :=
.seq loopBody388_133 loopBody388_151

def loopBody388_153 : HolLoopProg 64 :=
.mark loopBody388_152

def loopBody388_154 : HolLoopProg 64 :=
.seq loopBody388_131 loopBody388_153

def loopBody388_155 : HolLoopProg 64 :=
.mark loopBody388_154

def loopBody388_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody388_157 : HolLoopProg 64 :=
.mark loopBody388_156

def loopBody388_158 : HolLoopProg 64 :=
.seq loopBody388_157 loopBody388_141

def loopBody388_159 : HolLoopProg 64 :=
.mark loopBody388_158

def loopBody388_160 : HolLoopProg 64 :=
.seq loopBody388_155 loopBody388_159

def loopBody388_161 : HolLoopProg 64 :=
.mark loopBody388_160

def loopBody388_162 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody388_161 loopBody388_23 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody388_163 : HolLoopProg 64 :=
.mark loopBody388_162

def loopBody388_164 : HolLoopProg 64 :=
.seq loopBody388_163 loopBody388_23

def loopBody388_165 : HolLoopProg 64 :=
.mark loopBody388_164

def loopBody388_166 : HolLoopProg 64 :=
.seq loopBody388_129 loopBody388_165

def loopBody388_167 : HolLoopProg 64 :=
.mark loopBody388_166

def loopBody388_168 : HolLoopProg 64 :=
.seq loopBody388_127 loopBody388_167

def loopBody388_169 : HolLoopProg 64 :=
.mark loopBody388_168

def loopBody388_170 : HolLoopProg 64 :=
.seq loopBody388_121 loopBody388_169

def loopBody388_171 : HolLoopProg 64 :=
.mark loopBody388_170

def loopBody388_172 : HolLoopProg 64 :=
.seq loopBody388_119 loopBody388_171

def loopBody388_173 : HolLoopProg 64 :=
.mark loopBody388_172

def loopBody388_174 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody388_175 : HolLoopProg 64 :=
.mark loopBody388_174

def loopBody388_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 9)

def loopBody388_177 : HolLoopProg 64 :=
.mark loopBody388_176

def loopBody388_178 : HolLoopProg 64 :=
.seq loopBody388_177 loopBody388_23

def loopBody388_179 : HolLoopProg 64 :=
.mark loopBody388_178

def loopBody388_180 : HolLoopProg 64 :=
.seq loopBody388_179 loopBody388_23

def loopBody388_181 : HolLoopProg 64 :=
.mark loopBody388_180

def loopBody388_182 : HolLoopProg 64 :=
.seq loopBody388_175 loopBody388_181

def loopBody388_183 : HolLoopProg 64 :=
.mark loopBody388_182

def loopBody388_184 : HolLoopProg 64 :=
.seq loopBody388_23 loopBody388_183

def loopBody388_185 : HolLoopProg 64 :=
.mark loopBody388_184

def loopBody388_186 : HolLoopProg 64 :=
.seq loopBody388_173 loopBody388_185

def loopBody388_187 : HolLoopProg 64 :=
.mark loopBody388_186

def loopBody388_188 : HolLoopProg 64 :=
.seq loopBody388_117 loopBody388_187

def loopBody388_189 : HolLoopProg 64 :=
.mark loopBody388_188

def loopBody388_190 : HolLoopProg 64 :=
.seq loopBody388_115 loopBody388_189

def loopBody388_191 : HolLoopProg 64 :=
.mark loopBody388_190

def loopBody388_192 : HolLoopProg 64 :=
.seq loopBody388_107 loopBody388_191

def loopBody388_193 : HolLoopProg 64 :=
.mark loopBody388_192

def loopBody388_194 : HolLoopProg 64 :=
.seq loopBody388_105 loopBody388_193

def loopBody388_195 : HolLoopProg 64 :=
.mark loopBody388_194

def loopBody388_196 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody388_197 : HolLoopProg 64 :=
.mark loopBody388_196

def loopBody388_198 : HolLoopProg 64 :=
.seq loopBody388_195 loopBody388_197

def loopBody388_199 : HolLoopProg 64 :=
.mark loopBody388_198

def loopBody388_200 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody388_201 : HolLoopProg 64 :=
.mark loopBody388_200

def loopBody388_202 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody388_199 loopBody388_201 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody388_203 : HolLoopProg 64 :=
.mark loopBody388_202

def loopBody388_204 : HolLoopProg 64 :=
.seq loopBody388_203 loopBody388_23

def loopBody388_205 : HolLoopProg 64 :=
.mark loopBody388_204

def loopBody388_206 : HolLoopProg 64 :=
.seq loopBody388_97 loopBody388_205

def loopBody388_207 : HolLoopProg 64 :=
.mark loopBody388_206

def loopBody388_208 : HolLoopProg 64 :=
.seq loopBody388_95 loopBody388_207

def loopBody388_209 : HolLoopProg 64 :=
.mark loopBody388_208

def loopBody388_210 : HolLoopProg 64 :=
.seq loopBody388_89 loopBody388_209

def loopBody388_211 : HolLoopProg 64 :=
.mark loopBody388_210

def loopBody388_212 : HolLoopProg 64 :=
.seq loopBody388_11 loopBody388_211

def loopBody388_213 : HolLoopProg 64 :=
.mark loopBody388_212

def loopBody388_214 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody388_213 (Flapjack.Spt.ln)

def loopBody388_215 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody388_216 : HolLoopProg 64 :=
.mark loopBody388_215

def loopBody388_217 : HolLoopProg 64 :=
.seq loopBody388_216 loopBody388_23

def loopBody388_218 : HolLoopProg 64 :=
.mark loopBody388_217

def loopBody388_219 : HolLoopProg 64 :=
.seq loopBody388_3 loopBody388_218

def loopBody388_220 : HolLoopProg 64 :=
.mark loopBody388_219

def loopBody388_221 : HolLoopProg 64 :=
.seq loopBody388_214 loopBody388_220

def loopBody388_222 : HolLoopProg 64 :=
.seq loopBody388_7 loopBody388_221

def loopBody388_223 : HolLoopProg 64 :=
.seq loopBody388_23 loopBody388_222

def loopBody388_224 : HolLoopProg 64 :=
.seq loopBody388_87 loopBody388_223

def loopBody388_225 : HolLoopProg 64 :=
.seq loopBody388_59 loopBody388_224

def loopBody388_226 : HolLoopProg 64 :=
.seq loopBody388_23 loopBody388_225

def loopBody388_227 : HolLoopProg 64 :=
.seq loopBody388_57 loopBody388_226

def output388 : Nat × List Nat × HolLoopProg 64 :=
  (452, [0, 1, 2], loopBody388_227)
end InitECandidate.Proofs.FrontendStages.Loop
