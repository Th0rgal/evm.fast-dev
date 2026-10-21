import InitECandidate.Proofs.FrontendStages.Loop.Translate222
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody238_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody238_1 : HolLoopProg 64 :=
.mark loopBody238_0

def loopBody238_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody238_3 : HolLoopProg 64 :=
.mark loopBody238_2

def loopBody238_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody238_5 : HolLoopProg 64 :=
.mark loopBody238_4

def loopBody238_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody238_7 : HolLoopProg 64 :=
.mark loopBody238_6

def loopBody238_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody238_9 : HolLoopProg 64 :=
.mark loopBody238_8

def loopBody238_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody238_11 : HolLoopProg 64 :=
.mark loopBody238_10

def loopBody238_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.reg 6) loopBody238_9 loopBody238_11 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_13 : HolLoopProg 64 :=
.mark loopBody238_12

def loopBody238_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody238_15 : HolLoopProg 64 :=
.mark loopBody238_14

def loopBody238_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody238_17 : HolLoopProg 64 :=
.mark loopBody238_16

def loopBody238_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody238_19 : HolLoopProg 64 :=
.mark loopBody238_18

def loopBody238_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody238_21 : HolLoopProg 64 :=
.mark loopBody238_20

def loopBody238_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody238_23 : HolLoopProg 64 :=
.mark loopBody238_22

def loopBody238_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody238_23 loopBody238_7 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_25 : HolLoopProg 64 :=
.mark loopBody238_24

def loopBody238_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody238_27 : HolLoopProg 64 :=
.mark loopBody238_26

def loopBody238_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 2#64)

def loopBody238_29 : HolLoopProg 64 :=
.mark loopBody238_28

def loopBody238_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody238_31 : HolLoopProg 64 :=
.mark loopBody238_30

def loopBody238_32 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 282) ([6]) (some (6, loopBody238_31, loopBody238_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody238_33 : HolLoopProg 64 :=
.mark loopBody238_32

def loopBody238_34 : HolLoopProg 64 :=
.seq loopBody238_33 loopBody238_1

def loopBody238_35 : HolLoopProg 64 :=
.mark loopBody238_34

def loopBody238_36 : HolLoopProg 64 :=
.seq loopBody238_29 loopBody238_35

def loopBody238_37 : HolLoopProg 64 :=
.mark loopBody238_36

def loopBody238_38 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_37

def loopBody238_39 : HolLoopProg 64 :=
.mark loopBody238_38

def loopBody238_40 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_39

def loopBody238_41 : HolLoopProg 64 :=
.mark loopBody238_40

def loopBody238_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody238_41 loopBody238_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_43 : HolLoopProg 64 :=
.mark loopBody238_42

def loopBody238_44 : HolLoopProg 64 :=
.seq loopBody238_43 loopBody238_1

def loopBody238_45 : HolLoopProg 64 :=
.mark loopBody238_44

def loopBody238_46 : HolLoopProg 64 :=
.seq loopBody238_27 loopBody238_45

def loopBody238_47 : HolLoopProg 64 :=
.mark loopBody238_46

def loopBody238_48 : HolLoopProg 64 :=
.seq loopBody238_25 loopBody238_47

def loopBody238_49 : HolLoopProg 64 :=
.mark loopBody238_48

def loopBody238_50 : HolLoopProg 64 :=
.seq loopBody238_21 loopBody238_49

def loopBody238_51 : HolLoopProg 64 :=
.mark loopBody238_50

def loopBody238_52 : HolLoopProg 64 :=
.seq loopBody238_19 loopBody238_51

def loopBody238_53 : HolLoopProg 64 :=
.mark loopBody238_52

def loopBody238_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody238_55 : HolLoopProg 64 :=
.mark loopBody238_54

def loopBody238_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 40#64]))

def loopBody238_57 : HolLoopProg 64 :=
.mark loopBody238_56

def loopBody238_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3])

def loopBody238_59 : HolLoopProg 64 :=
.mark loopBody238_58

def loopBody238_60 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody238_55 loopBody238_21 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody238_61 : HolLoopProg 64 :=
.mark loopBody238_60

def loopBody238_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody238_63 : HolLoopProg 64 :=
.mark loopBody238_62

def loopBody238_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 32#64]))

def loopBody238_65 : HolLoopProg 64 :=
.mark loopBody238_64

def loopBody238_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 3])

def loopBody238_67 : HolLoopProg 64 :=
.mark loopBody238_66

def loopBody238_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody238_69 : HolLoopProg 64 :=
.mark loopBody238_68

def loopBody238_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody238_71 : HolLoopProg 64 :=
.mark loopBody238_70

def loopBody238_72 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ls PUnit.unit)) (some 79) ([7, 8, 9]) (some (7, loopBody238_71, loopBody238_1, (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)))

def loopBody238_73 : HolLoopProg 64 :=
.mark loopBody238_72

def loopBody238_74 : HolLoopProg 64 :=
.seq loopBody238_73 loopBody238_1

def loopBody238_75 : HolLoopProg 64 :=
.mark loopBody238_74

def loopBody238_76 : HolLoopProg 64 :=
.seq loopBody238_69 loopBody238_75

def loopBody238_77 : HolLoopProg 64 :=
.mark loopBody238_76

def loopBody238_78 : HolLoopProg 64 :=
.seq loopBody238_67 loopBody238_77

def loopBody238_79 : HolLoopProg 64 :=
.mark loopBody238_78

def loopBody238_80 : HolLoopProg 64 :=
.seq loopBody238_65 loopBody238_79

def loopBody238_81 : HolLoopProg 64 :=
.mark loopBody238_80

def loopBody238_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody238_83 : HolLoopProg 64 :=
.mark loopBody238_82

def loopBody238_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody238_85 : HolLoopProg 64 :=
.mark loopBody238_84

def loopBody238_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody238_87 : HolLoopProg 64 :=
.mark loopBody238_86

def loopBody238_88 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.reg 9) loopBody238_85 loopBody238_87 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def loopBody238_89 : HolLoopProg 64 :=
.mark loopBody238_88

def loopBody238_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody238_91 : HolLoopProg 64 :=
.mark loopBody238_90

def loopBody238_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64]))

def loopBody238_93 : HolLoopProg 64 :=
.mark loopBody238_92

def loopBody238_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 56#64]))

def loopBody238_95 : HolLoopProg 64 :=
.mark loopBody238_94

def loopBody238_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7, 8, 9]

def loopBody238_97 : HolLoopProg 64 :=
.mark loopBody238_96

def loopBody238_98 : HolLoopProg 64 :=
.seq loopBody238_97 loopBody238_1

def loopBody238_99 : HolLoopProg 64 :=
.mark loopBody238_98

def loopBody238_100 : HolLoopProg 64 :=
.seq loopBody238_95 loopBody238_99

def loopBody238_101 : HolLoopProg 64 :=
.mark loopBody238_100

def loopBody238_102 : HolLoopProg 64 :=
.seq loopBody238_93 loopBody238_101

def loopBody238_103 : HolLoopProg 64 :=
.mark loopBody238_102

def loopBody238_104 : HolLoopProg 64 :=
.seq loopBody238_55 loopBody238_103

def loopBody238_105 : HolLoopProg 64 :=
.mark loopBody238_104

def loopBody238_106 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody238_105 loopBody238_1 (Flapjack.Spt.ln)

def loopBody238_107 : HolLoopProg 64 :=
.mark loopBody238_106

def loopBody238_108 : HolLoopProg 64 :=
.seq loopBody238_107 loopBody238_1

def loopBody238_109 : HolLoopProg 64 :=
.mark loopBody238_108

def loopBody238_110 : HolLoopProg 64 :=
.seq loopBody238_91 loopBody238_109

def loopBody238_111 : HolLoopProg 64 :=
.mark loopBody238_110

def loopBody238_112 : HolLoopProg 64 :=
.seq loopBody238_89 loopBody238_111

def loopBody238_113 : HolLoopProg 64 :=
.mark loopBody238_112

def loopBody238_114 : HolLoopProg 64 :=
.seq loopBody238_83 loopBody238_113

def loopBody238_115 : HolLoopProg 64 :=
.mark loopBody238_114

def loopBody238_116 : HolLoopProg 64 :=
.seq loopBody238_27 loopBody238_115

def loopBody238_117 : HolLoopProg 64 :=
.mark loopBody238_116

def loopBody238_118 : HolLoopProg 64 :=
.seq loopBody238_81 loopBody238_117

def loopBody238_119 : HolLoopProg 64 :=
.mark loopBody238_118

def loopBody238_120 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_119

def loopBody238_121 : HolLoopProg 64 :=
.mark loopBody238_120

def loopBody238_122 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_121

def loopBody238_123 : HolLoopProg 64 :=
.mark loopBody238_122

def loopBody238_124 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody238_123 loopBody238_1 (Flapjack.Spt.ln)

def loopBody238_125 : HolLoopProg 64 :=
.mark loopBody238_124

def loopBody238_126 : HolLoopProg 64 :=
.seq loopBody238_125 loopBody238_1

def loopBody238_127 : HolLoopProg 64 :=
.mark loopBody238_126

def loopBody238_128 : HolLoopProg 64 :=
.seq loopBody238_63 loopBody238_127

def loopBody238_129 : HolLoopProg 64 :=
.mark loopBody238_128

def loopBody238_130 : HolLoopProg 64 :=
.seq loopBody238_61 loopBody238_129

def loopBody238_131 : HolLoopProg 64 :=
.mark loopBody238_130

def loopBody238_132 : HolLoopProg 64 :=
.seq loopBody238_59 loopBody238_131

def loopBody238_133 : HolLoopProg 64 :=
.mark loopBody238_132

def loopBody238_134 : HolLoopProg 64 :=
.seq loopBody238_15 loopBody238_133

def loopBody238_135 : HolLoopProg 64 :=
.mark loopBody238_134

def loopBody238_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6, 7, 8]

def loopBody238_137 : HolLoopProg 64 :=
.mark loopBody238_136

def loopBody238_138 : HolLoopProg 64 :=
.seq loopBody238_137 loopBody238_1

def loopBody238_139 : HolLoopProg 64 :=
.mark loopBody238_138

def loopBody238_140 : HolLoopProg 64 :=
.seq loopBody238_87 loopBody238_139

def loopBody238_141 : HolLoopProg 64 :=
.mark loopBody238_140

def loopBody238_142 : HolLoopProg 64 :=
.seq loopBody238_21 loopBody238_141

def loopBody238_143 : HolLoopProg 64 :=
.mark loopBody238_142

def loopBody238_144 : HolLoopProg 64 :=
.seq loopBody238_7 loopBody238_143

def loopBody238_145 : HolLoopProg 64 :=
.mark loopBody238_144

def loopBody238_146 : HolLoopProg 64 :=
.seq loopBody238_135 loopBody238_145

def loopBody238_147 : HolLoopProg 64 :=
.mark loopBody238_146

def loopBody238_148 : HolLoopProg 64 :=
.seq loopBody238_57 loopBody238_147

def loopBody238_149 : HolLoopProg 64 :=
.mark loopBody238_148

def loopBody238_150 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_149

def loopBody238_151 : HolLoopProg 64 :=
.mark loopBody238_150

def loopBody238_152 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody238_151 loopBody238_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_153 : HolLoopProg 64 :=
.mark loopBody238_152

def loopBody238_154 : HolLoopProg 64 :=
.seq loopBody238_153 loopBody238_1

def loopBody238_155 : HolLoopProg 64 :=
.mark loopBody238_154

def loopBody238_156 : HolLoopProg 64 :=
.seq loopBody238_27 loopBody238_155

def loopBody238_157 : HolLoopProg 64 :=
.mark loopBody238_156

def loopBody238_158 : HolLoopProg 64 :=
.seq loopBody238_25 loopBody238_157

def loopBody238_159 : HolLoopProg 64 :=
.mark loopBody238_158

def loopBody238_160 : HolLoopProg 64 :=
.seq loopBody238_55 loopBody238_159

def loopBody238_161 : HolLoopProg 64 :=
.mark loopBody238_160

def loopBody238_162 : HolLoopProg 64 :=
.seq loopBody238_19 loopBody238_161

def loopBody238_163 : HolLoopProg 64 :=
.mark loopBody238_162

def loopBody238_164 : HolLoopProg 64 :=
.seq loopBody238_53 loopBody238_163

def loopBody238_165 : HolLoopProg 64 :=
.mark loopBody238_164

def loopBody238_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 2#64)

def loopBody238_167 : HolLoopProg 64 :=
.mark loopBody238_166

def loopBody238_168 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody238_23 loopBody238_7 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_169 : HolLoopProg 64 :=
.mark loopBody238_168

def loopBody238_170 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3])

def loopBody238_171 : HolLoopProg 64 :=
.mark loopBody238_170

def loopBody238_172 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody238_173 : HolLoopProg 64 :=
.mark loopBody238_172

def loopBody238_174 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody238_55 loopBody238_21 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody238_175 : HolLoopProg 64 :=
.mark loopBody238_174

def loopBody238_176 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody238_145 loopBody238_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_177 : HolLoopProg 64 :=
.mark loopBody238_176

def loopBody238_178 : HolLoopProg 64 :=
.seq loopBody238_177 loopBody238_1

def loopBody238_179 : HolLoopProg 64 :=
.mark loopBody238_178

def loopBody238_180 : HolLoopProg 64 :=
.seq loopBody238_63 loopBody238_179

def loopBody238_181 : HolLoopProg 64 :=
.mark loopBody238_180

def loopBody238_182 : HolLoopProg 64 :=
.seq loopBody238_175 loopBody238_181

def loopBody238_183 : HolLoopProg 64 :=
.mark loopBody238_182

def loopBody238_184 : HolLoopProg 64 :=
.seq loopBody238_173 loopBody238_183

def loopBody238_185 : HolLoopProg 64 :=
.mark loopBody238_184

def loopBody238_186 : HolLoopProg 64 :=
.seq loopBody238_171 loopBody238_185

def loopBody238_187 : HolLoopProg 64 :=
.mark loopBody238_186

def loopBody238_188 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 79) ([7, 8, 9]) (some (7, loopBody238_71, loopBody238_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody238_189 : HolLoopProg 64 :=
.mark loopBody238_188

def loopBody238_190 : HolLoopProg 64 :=
.seq loopBody238_189 loopBody238_1

def loopBody238_191 : HolLoopProg 64 :=
.mark loopBody238_190

def loopBody238_192 : HolLoopProg 64 :=
.seq loopBody238_69 loopBody238_191

def loopBody238_193 : HolLoopProg 64 :=
.mark loopBody238_192

def loopBody238_194 : HolLoopProg 64 :=
.seq loopBody238_67 loopBody238_193

def loopBody238_195 : HolLoopProg 64 :=
.mark loopBody238_194

def loopBody238_196 : HolLoopProg 64 :=
.seq loopBody238_65 loopBody238_195

def loopBody238_197 : HolLoopProg 64 :=
.mark loopBody238_196

def loopBody238_198 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.RegImm.reg 9) loopBody238_85 loopBody238_87 (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_199 : HolLoopProg 64 :=
.mark loopBody238_198

def loopBody238_200 : HolLoopProg 64 :=
.seq loopBody238_83 loopBody238_99

def loopBody238_201 : HolLoopProg 64 :=
.mark loopBody238_200

def loopBody238_202 : HolLoopProg 64 :=
.seq loopBody238_87 loopBody238_201

def loopBody238_203 : HolLoopProg 64 :=
.mark loopBody238_202

def loopBody238_204 : HolLoopProg 64 :=
.seq loopBody238_21 loopBody238_203

def loopBody238_205 : HolLoopProg 64 :=
.mark loopBody238_204

def loopBody238_206 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody238_205 loopBody238_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_207 : HolLoopProg 64 :=
.mark loopBody238_206

def loopBody238_208 : HolLoopProg 64 :=
.seq loopBody238_207 loopBody238_1

def loopBody238_209 : HolLoopProg 64 :=
.mark loopBody238_208

def loopBody238_210 : HolLoopProg 64 :=
.seq loopBody238_91 loopBody238_209

def loopBody238_211 : HolLoopProg 64 :=
.mark loopBody238_210

def loopBody238_212 : HolLoopProg 64 :=
.seq loopBody238_199 loopBody238_211

def loopBody238_213 : HolLoopProg 64 :=
.mark loopBody238_212

def loopBody238_214 : HolLoopProg 64 :=
.seq loopBody238_83 loopBody238_213

def loopBody238_215 : HolLoopProg 64 :=
.mark loopBody238_214

def loopBody238_216 : HolLoopProg 64 :=
.seq loopBody238_27 loopBody238_215

def loopBody238_217 : HolLoopProg 64 :=
.mark loopBody238_216

def loopBody238_218 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.var 5])

def loopBody238_219 : HolLoopProg 64 :=
.mark loopBody238_218

def loopBody238_220 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 7)

def loopBody238_221 : HolLoopProg 64 :=
.mark loopBody238_220

def loopBody238_222 : HolLoopProg 64 :=
.seq loopBody238_221 loopBody238_1

def loopBody238_223 : HolLoopProg 64 :=
.mark loopBody238_222

def loopBody238_224 : HolLoopProg 64 :=
.seq loopBody238_223 loopBody238_1

def loopBody238_225 : HolLoopProg 64 :=
.mark loopBody238_224

def loopBody238_226 : HolLoopProg 64 :=
.seq loopBody238_219 loopBody238_225

def loopBody238_227 : HolLoopProg 64 :=
.mark loopBody238_226

def loopBody238_228 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_227

def loopBody238_229 : HolLoopProg 64 :=
.mark loopBody238_228

def loopBody238_230 : HolLoopProg 64 :=
.seq loopBody238_217 loopBody238_229

def loopBody238_231 : HolLoopProg 64 :=
.mark loopBody238_230

def loopBody238_232 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64]))

def loopBody238_233 : HolLoopProg 64 :=
.mark loopBody238_232

def loopBody238_234 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 0 (Flapjack.HolLoopExp.var 7)

def loopBody238_235 : HolLoopProg 64 :=
.mark loopBody238_234

def loopBody238_236 : HolLoopProg 64 :=
.seq loopBody238_235 loopBody238_1

def loopBody238_237 : HolLoopProg 64 :=
.mark loopBody238_236

def loopBody238_238 : HolLoopProg 64 :=
.seq loopBody238_237 loopBody238_1

def loopBody238_239 : HolLoopProg 64 :=
.mark loopBody238_238

def loopBody238_240 : HolLoopProg 64 :=
.seq loopBody238_233 loopBody238_239

def loopBody238_241 : HolLoopProg 64 :=
.mark loopBody238_240

def loopBody238_242 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_241

def loopBody238_243 : HolLoopProg 64 :=
.mark loopBody238_242

def loopBody238_244 : HolLoopProg 64 :=
.seq loopBody238_231 loopBody238_243

def loopBody238_245 : HolLoopProg 64 :=
.mark loopBody238_244

def loopBody238_246 : HolLoopProg 64 :=
.seq loopBody238_197 loopBody238_245

def loopBody238_247 : HolLoopProg 64 :=
.mark loopBody238_246

def loopBody238_248 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_247

def loopBody238_249 : HolLoopProg 64 :=
.mark loopBody238_248

def loopBody238_250 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_249

def loopBody238_251 : HolLoopProg 64 :=
.mark loopBody238_250

def loopBody238_252 : HolLoopProg 64 :=
.seq loopBody238_187 loopBody238_251

def loopBody238_253 : HolLoopProg 64 :=
.mark loopBody238_252

def loopBody238_254 : HolLoopProg 64 :=
.seq loopBody238_57 loopBody238_253

def loopBody238_255 : HolLoopProg 64 :=
.mark loopBody238_254

def loopBody238_256 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_255

def loopBody238_257 : HolLoopProg 64 :=
.mark loopBody238_256

def loopBody238_258 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody238_259 : HolLoopProg 64 :=
.mark loopBody238_258

def loopBody238_260 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody238_261 : HolLoopProg 64 :=
.mark loopBody238_260

def loopBody238_262 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 168#64]))

def loopBody238_263 : HolLoopProg 64 :=
.mark loopBody238_262

def loopBody238_264 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody238_55 loopBody238_21 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody238_265 : HolLoopProg 64 :=
.mark loopBody238_264

def loopBody238_266 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody238_145 loopBody238_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody238_267 : HolLoopProg 64 :=
.mark loopBody238_266

def loopBody238_268 : HolLoopProg 64 :=
.seq loopBody238_267 loopBody238_1

def loopBody238_269 : HolLoopProg 64 :=
.mark loopBody238_268

def loopBody238_270 : HolLoopProg 64 :=
.seq loopBody238_63 loopBody238_269

def loopBody238_271 : HolLoopProg 64 :=
.mark loopBody238_270

def loopBody238_272 : HolLoopProg 64 :=
.seq loopBody238_265 loopBody238_271

def loopBody238_273 : HolLoopProg 64 :=
.mark loopBody238_272

def loopBody238_274 : HolLoopProg 64 :=
.seq loopBody238_87 loopBody238_273

def loopBody238_275 : HolLoopProg 64 :=
.mark loopBody238_274

def loopBody238_276 : HolLoopProg 64 :=
.seq loopBody238_15 loopBody238_275

def loopBody238_277 : HolLoopProg 64 :=
.mark loopBody238_276

def loopBody238_278 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64]))

def loopBody238_279 : HolLoopProg 64 :=
.mark loopBody238_278

def loopBody238_280 : HolLoopProg 64 :=
.seq loopBody238_173 loopBody238_139

def loopBody238_281 : HolLoopProg 64 :=
.mark loopBody238_280

def loopBody238_282 : HolLoopProg 64 :=
.seq loopBody238_279 loopBody238_281

def loopBody238_283 : HolLoopProg 64 :=
.mark loopBody238_282

def loopBody238_284 : HolLoopProg 64 :=
.seq loopBody238_23 loopBody238_283

def loopBody238_285 : HolLoopProg 64 :=
.mark loopBody238_284

def loopBody238_286 : HolLoopProg 64 :=
.seq loopBody238_277 loopBody238_285

def loopBody238_287 : HolLoopProg 64 :=
.mark loopBody238_286

def loopBody238_288 : HolLoopProg 64 :=
.seq loopBody238_263 loopBody238_287

def loopBody238_289 : HolLoopProg 64 :=
.mark loopBody238_288

def loopBody238_290 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_289

def loopBody238_291 : HolLoopProg 64 :=
.mark loopBody238_290

def loopBody238_292 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody238_291 loopBody238_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_293 : HolLoopProg 64 :=
.mark loopBody238_292

def loopBody238_294 : HolLoopProg 64 :=
.seq loopBody238_293 loopBody238_1

def loopBody238_295 : HolLoopProg 64 :=
.mark loopBody238_294

def loopBody238_296 : HolLoopProg 64 :=
.seq loopBody238_27 loopBody238_295

def loopBody238_297 : HolLoopProg 64 :=
.mark loopBody238_296

def loopBody238_298 : HolLoopProg 64 :=
.seq loopBody238_169 loopBody238_297

def loopBody238_299 : HolLoopProg 64 :=
.mark loopBody238_298

def loopBody238_300 : HolLoopProg 64 :=
.seq loopBody238_261 loopBody238_299

def loopBody238_301 : HolLoopProg 64 :=
.mark loopBody238_300

def loopBody238_302 : HolLoopProg 64 :=
.seq loopBody238_259 loopBody238_301

def loopBody238_303 : HolLoopProg 64 :=
.mark loopBody238_302

def loopBody238_304 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 3])

def loopBody238_305 : HolLoopProg 64 :=
.mark loopBody238_304

def loopBody238_306 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 5 5

def loopBody238_307 : HolLoopProg 64 :=
.mark loopBody238_306

def loopBody238_308 : HolLoopProg 64 :=
.seq loopBody238_307 loopBody238_1

def loopBody238_309 : HolLoopProg 64 :=
.mark loopBody238_308

def loopBody238_310 : HolLoopProg 64 :=
.seq loopBody238_305 loopBody238_309

def loopBody238_311 : HolLoopProg 64 :=
.mark loopBody238_310

def loopBody238_312 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 32#64,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 3#64)]))

def loopBody238_313 : HolLoopProg 64 :=
.mark loopBody238_312

def loopBody238_314 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 0 (Flapjack.HolLoopExp.var 6)

def loopBody238_315 : HolLoopProg 64 :=
.mark loopBody238_314

def loopBody238_316 : HolLoopProg 64 :=
.seq loopBody238_315 loopBody238_1

def loopBody238_317 : HolLoopProg 64 :=
.mark loopBody238_316

def loopBody238_318 : HolLoopProg 64 :=
.seq loopBody238_317 loopBody238_1

def loopBody238_319 : HolLoopProg 64 :=
.mark loopBody238_318

def loopBody238_320 : HolLoopProg 64 :=
.seq loopBody238_313 loopBody238_319

def loopBody238_321 : HolLoopProg 64 :=
.mark loopBody238_320

def loopBody238_322 : HolLoopProg 64 :=
.seq loopBody238_311 loopBody238_321

def loopBody238_323 : HolLoopProg 64 :=
.mark loopBody238_322

def loopBody238_324 : HolLoopProg 64 :=
.seq loopBody238_303 loopBody238_323

def loopBody238_325 : HolLoopProg 64 :=
.mark loopBody238_324

def loopBody238_326 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody238_327 : HolLoopProg 64 :=
.mark loopBody238_326

def loopBody238_328 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 5)

def loopBody238_329 : HolLoopProg 64 :=
.mark loopBody238_328

def loopBody238_330 : HolLoopProg 64 :=
.seq loopBody238_329 loopBody238_1

def loopBody238_331 : HolLoopProg 64 :=
.mark loopBody238_330

def loopBody238_332 : HolLoopProg 64 :=
.seq loopBody238_331 loopBody238_1

def loopBody238_333 : HolLoopProg 64 :=
.mark loopBody238_332

def loopBody238_334 : HolLoopProg 64 :=
.seq loopBody238_327 loopBody238_333

def loopBody238_335 : HolLoopProg 64 :=
.mark loopBody238_334

def loopBody238_336 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_335

def loopBody238_337 : HolLoopProg 64 :=
.mark loopBody238_336

def loopBody238_338 : HolLoopProg 64 :=
.seq loopBody238_325 loopBody238_337

def loopBody238_339 : HolLoopProg 64 :=
.mark loopBody238_338

def loopBody238_340 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody238_257 loopBody238_339 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_341 : HolLoopProg 64 :=
.mark loopBody238_340

def loopBody238_342 : HolLoopProg 64 :=
.seq loopBody238_341 loopBody238_1

def loopBody238_343 : HolLoopProg 64 :=
.mark loopBody238_342

def loopBody238_344 : HolLoopProg 64 :=
.seq loopBody238_27 loopBody238_343

def loopBody238_345 : HolLoopProg 64 :=
.mark loopBody238_344

def loopBody238_346 : HolLoopProg 64 :=
.seq loopBody238_169 loopBody238_345

def loopBody238_347 : HolLoopProg 64 :=
.mark loopBody238_346

def loopBody238_348 : HolLoopProg 64 :=
.seq loopBody238_167 loopBody238_347

def loopBody238_349 : HolLoopProg 64 :=
.mark loopBody238_348

def loopBody238_350 : HolLoopProg 64 :=
.seq loopBody238_19 loopBody238_349

def loopBody238_351 : HolLoopProg 64 :=
.mark loopBody238_350

def loopBody238_352 : HolLoopProg 64 :=
.seq loopBody238_165 loopBody238_351

def loopBody238_353 : HolLoopProg 64 :=
.mark loopBody238_352

def loopBody238_354 : HolLoopProg 64 :=
.seq loopBody238_17 loopBody238_353

def loopBody238_355 : HolLoopProg 64 :=
.mark loopBody238_354

def loopBody238_356 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_355

def loopBody238_357 : HolLoopProg 64 :=
.mark loopBody238_356

def loopBody238_358 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody238_359 : HolLoopProg 64 :=
.mark loopBody238_358

def loopBody238_360 : HolLoopProg 64 :=
.seq loopBody238_357 loopBody238_359

def loopBody238_361 : HolLoopProg 64 :=
.mark loopBody238_360

def loopBody238_362 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody238_363 : HolLoopProg 64 :=
.mark loopBody238_362

def loopBody238_364 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody238_361 loopBody238_363 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody238_365 : HolLoopProg 64 :=
.mark loopBody238_364

def loopBody238_366 : HolLoopProg 64 :=
.seq loopBody238_365 loopBody238_1

def loopBody238_367 : HolLoopProg 64 :=
.mark loopBody238_366

def loopBody238_368 : HolLoopProg 64 :=
.seq loopBody238_15 loopBody238_367

def loopBody238_369 : HolLoopProg 64 :=
.mark loopBody238_368

def loopBody238_370 : HolLoopProg 64 :=
.seq loopBody238_13 loopBody238_369

def loopBody238_371 : HolLoopProg 64 :=
.mark loopBody238_370

def loopBody238_372 : HolLoopProg 64 :=
.seq loopBody238_7 loopBody238_371

def loopBody238_373 : HolLoopProg 64 :=
.mark loopBody238_372

def loopBody238_374 : HolLoopProg 64 :=
.seq loopBody238_5 loopBody238_373

def loopBody238_375 : HolLoopProg 64 :=
.mark loopBody238_374

def loopBody238_376 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody238_375 (Flapjack.Spt.ln)

def loopBody238_377 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody238_378 : HolLoopProg 64 :=
.mark loopBody238_377

def loopBody238_379 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4, 5, 6]

def loopBody238_380 : HolLoopProg 64 :=
.mark loopBody238_379

def loopBody238_381 : HolLoopProg 64 :=
.seq loopBody238_380 loopBody238_1

def loopBody238_382 : HolLoopProg 64 :=
.mark loopBody238_381

def loopBody238_383 : HolLoopProg 64 :=
.seq loopBody238_7 loopBody238_382

def loopBody238_384 : HolLoopProg 64 :=
.mark loopBody238_383

def loopBody238_385 : HolLoopProg 64 :=
.seq loopBody238_11 loopBody238_384

def loopBody238_386 : HolLoopProg 64 :=
.mark loopBody238_385

def loopBody238_387 : HolLoopProg 64 :=
.seq loopBody238_378 loopBody238_386

def loopBody238_388 : HolLoopProg 64 :=
.mark loopBody238_387

def loopBody238_389 : HolLoopProg 64 :=
.seq loopBody238_376 loopBody238_388

def loopBody238_390 : HolLoopProg 64 :=
.seq loopBody238_3 loopBody238_389

def loopBody238_391 : HolLoopProg 64 :=
.seq loopBody238_1 loopBody238_390

def output238 : Nat × List Nat × HolLoopProg 64 :=
  (302, [0, 1, 2], loopBody238_391)
end InitECandidate.Proofs.FrontendStages.Loop
