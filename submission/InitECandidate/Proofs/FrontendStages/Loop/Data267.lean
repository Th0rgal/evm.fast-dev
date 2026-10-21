import InitECandidate.Proofs.FrontendStages.Loop.Translate251
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody267_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody267_1 : HolLoopProg 64 :=
.mark loopBody267_0

def loopBody267_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody267_3 : HolLoopProg 64 :=
.mark loopBody267_2

def loopBody267_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody267_5 : HolLoopProg 64 :=
.mark loopBody267_4

def loopBody267_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody267_7 : HolLoopProg 64 :=
.mark loopBody267_6

def loopBody267_8 : HolLoopProg 64 :=
.call (some ([3, 4, 5, 6], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 161) ([7, 8]) (some (7, loopBody267_7, loopBody267_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody267_9 : HolLoopProg 64 :=
.mark loopBody267_8

def loopBody267_10 : HolLoopProg 64 :=
.seq loopBody267_9 loopBody267_1

def loopBody267_11 : HolLoopProg 64 :=
.mark loopBody267_10

def loopBody267_12 : HolLoopProg 64 :=
.seq loopBody267_5 loopBody267_11

def loopBody267_13 : HolLoopProg 64 :=
.mark loopBody267_12

def loopBody267_14 : HolLoopProg 64 :=
.seq loopBody267_3 loopBody267_13

def loopBody267_15 : HolLoopProg 64 :=
.mark loopBody267_14

def loopBody267_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody267_17 : HolLoopProg 64 :=
.mark loopBody267_16

def loopBody267_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody267_19 : HolLoopProg 64 :=
.mark loopBody267_18

def loopBody267_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody267_21 : HolLoopProg 64 :=
.mark loopBody267_20

def loopBody267_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody267_23 : HolLoopProg 64 :=
.mark loopBody267_22

def loopBody267_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.reg 9) loopBody267_21 loopBody267_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody267_25 : HolLoopProg 64 :=
.mark loopBody267_24

def loopBody267_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody267_27 : HolLoopProg 64 :=
.mark loopBody267_26

def loopBody267_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 10#64)

def loopBody267_29 : HolLoopProg 64 :=
.mark loopBody267_28

def loopBody267_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 7)

def loopBody267_31 : HolLoopProg 64 :=
.mark loopBody267_30

def loopBody267_32 : HolLoopProg 64 :=
.seq loopBody267_31 loopBody267_1

def loopBody267_33 : HolLoopProg 64 :=
.mark loopBody267_32

def loopBody267_34 : HolLoopProg 64 :=
.seq loopBody267_33 loopBody267_1

def loopBody267_35 : HolLoopProg 64 :=
.mark loopBody267_34

def loopBody267_36 : HolLoopProg 64 :=
.seq loopBody267_29 loopBody267_35

def loopBody267_37 : HolLoopProg 64 :=
.mark loopBody267_36

def loopBody267_38 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_37

def loopBody267_39 : HolLoopProg 64 :=
.mark loopBody267_38

def loopBody267_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 6#64)

def loopBody267_41 : HolLoopProg 64 :=
.mark loopBody267_40

def loopBody267_42 : HolLoopProg 64 :=
.seq loopBody267_41 loopBody267_7

def loopBody267_43 : HolLoopProg 64 :=
.mark loopBody267_42

def loopBody267_44 : HolLoopProg 64 :=
.seq loopBody267_39 loopBody267_43

def loopBody267_45 : HolLoopProg 64 :=
.mark loopBody267_44

def loopBody267_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody267_45 loopBody267_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody267_47 : HolLoopProg 64 :=
.mark loopBody267_46

def loopBody267_48 : HolLoopProg 64 :=
.seq loopBody267_47 loopBody267_1

def loopBody267_49 : HolLoopProg 64 :=
.mark loopBody267_48

def loopBody267_50 : HolLoopProg 64 :=
.seq loopBody267_27 loopBody267_49

def loopBody267_51 : HolLoopProg 64 :=
.mark loopBody267_50

def loopBody267_52 : HolLoopProg 64 :=
.seq loopBody267_25 loopBody267_51

def loopBody267_53 : HolLoopProg 64 :=
.mark loopBody267_52

def loopBody267_54 : HolLoopProg 64 :=
.seq loopBody267_19 loopBody267_53

def loopBody267_55 : HolLoopProg 64 :=
.mark loopBody267_54

def loopBody267_56 : HolLoopProg 64 :=
.seq loopBody267_17 loopBody267_55

def loopBody267_57 : HolLoopProg 64 :=
.mark loopBody267_56

def loopBody267_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody267_59 : HolLoopProg 64 :=
.mark loopBody267_58

def loopBody267_60 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.RegImm.reg 9) loopBody267_21 loopBody267_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody267_61 : HolLoopProg 64 :=
.mark loopBody267_60

def loopBody267_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody267_63 : HolLoopProg 64 :=
.mark loopBody267_62

def loopBody267_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 7 7

def loopBody267_65 : HolLoopProg 64 :=
.mark loopBody267_64

def loopBody267_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody267_67 : HolLoopProg 64 :=
.mark loopBody267_66

def loopBody267_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody267_69 : HolLoopProg 64 :=
.mark loopBody267_68

def loopBody267_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody267_71 : HolLoopProg 64 :=
.mark loopBody267_70

def loopBody267_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody267_71 loopBody267_19 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody267_73 : HolLoopProg 64 :=
.mark loopBody267_72

def loopBody267_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody267_75 : HolLoopProg 64 :=
.mark loopBody267_74

def loopBody267_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 11#64)

def loopBody267_77 : HolLoopProg 64 :=
.mark loopBody267_76

def loopBody267_78 : HolLoopProg 64 :=
.seq loopBody267_77 loopBody267_35

def loopBody267_79 : HolLoopProg 64 :=
.mark loopBody267_78

def loopBody267_80 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_79

def loopBody267_81 : HolLoopProg 64 :=
.mark loopBody267_80

def loopBody267_82 : HolLoopProg 64 :=
.seq loopBody267_81 loopBody267_43

def loopBody267_83 : HolLoopProg 64 :=
.mark loopBody267_82

def loopBody267_84 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody267_83 loopBody267_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody267_85 : HolLoopProg 64 :=
.mark loopBody267_84

def loopBody267_86 : HolLoopProg 64 :=
.seq loopBody267_85 loopBody267_1

def loopBody267_87 : HolLoopProg 64 :=
.mark loopBody267_86

def loopBody267_88 : HolLoopProg 64 :=
.seq loopBody267_75 loopBody267_87

def loopBody267_89 : HolLoopProg 64 :=
.mark loopBody267_88

def loopBody267_90 : HolLoopProg 64 :=
.seq loopBody267_73 loopBody267_89

def loopBody267_91 : HolLoopProg 64 :=
.mark loopBody267_90

def loopBody267_92 : HolLoopProg 64 :=
.seq loopBody267_69 loopBody267_91

def loopBody267_93 : HolLoopProg 64 :=
.mark loopBody267_92

def loopBody267_94 : HolLoopProg 64 :=
.seq loopBody267_67 loopBody267_93

def loopBody267_95 : HolLoopProg 64 :=
.mark loopBody267_94

def loopBody267_96 : HolLoopProg 64 :=
.seq loopBody267_65 loopBody267_95

def loopBody267_97 : HolLoopProg 64 :=
.mark loopBody267_96

def loopBody267_98 : HolLoopProg 64 :=
.seq loopBody267_63 loopBody267_97

def loopBody267_99 : HolLoopProg 64 :=
.mark loopBody267_98

def loopBody267_100 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody267_99 loopBody267_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody267_101 : HolLoopProg 64 :=
.mark loopBody267_100

def loopBody267_102 : HolLoopProg 64 :=
.seq loopBody267_101 loopBody267_1

def loopBody267_103 : HolLoopProg 64 :=
.mark loopBody267_102

def loopBody267_104 : HolLoopProg 64 :=
.seq loopBody267_27 loopBody267_103

def loopBody267_105 : HolLoopProg 64 :=
.mark loopBody267_104

def loopBody267_106 : HolLoopProg 64 :=
.seq loopBody267_61 loopBody267_105

def loopBody267_107 : HolLoopProg 64 :=
.mark loopBody267_106

def loopBody267_108 : HolLoopProg 64 :=
.seq loopBody267_59 loopBody267_107

def loopBody267_109 : HolLoopProg 64 :=
.mark loopBody267_108

def loopBody267_110 : HolLoopProg 64 :=
.seq loopBody267_23 loopBody267_109

def loopBody267_111 : HolLoopProg 64 :=
.mark loopBody267_110

def loopBody267_112 : HolLoopProg 64 :=
.seq loopBody267_57 loopBody267_111

def loopBody267_113 : HolLoopProg 64 :=
.mark loopBody267_112

def loopBody267_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody267_115 : HolLoopProg 64 :=
.mark loopBody267_114

def loopBody267_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.RegImm.reg 9) loopBody267_21 loopBody267_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody267_117 : HolLoopProg 64 :=
.mark loopBody267_116

def loopBody267_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 12#64)

def loopBody267_119 : HolLoopProg 64 :=
.mark loopBody267_118

def loopBody267_120 : HolLoopProg 64 :=
.seq loopBody267_119 loopBody267_35

def loopBody267_121 : HolLoopProg 64 :=
.mark loopBody267_120

def loopBody267_122 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_121

def loopBody267_123 : HolLoopProg 64 :=
.mark loopBody267_122

def loopBody267_124 : HolLoopProg 64 :=
.seq loopBody267_123 loopBody267_43

def loopBody267_125 : HolLoopProg 64 :=
.mark loopBody267_124

def loopBody267_126 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody267_125 loopBody267_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody267_127 : HolLoopProg 64 :=
.mark loopBody267_126

def loopBody267_128 : HolLoopProg 64 :=
.seq loopBody267_127 loopBody267_1

def loopBody267_129 : HolLoopProg 64 :=
.mark loopBody267_128

def loopBody267_130 : HolLoopProg 64 :=
.seq loopBody267_27 loopBody267_129

def loopBody267_131 : HolLoopProg 64 :=
.mark loopBody267_130

def loopBody267_132 : HolLoopProg 64 :=
.seq loopBody267_117 loopBody267_131

def loopBody267_133 : HolLoopProg 64 :=
.mark loopBody267_132

def loopBody267_134 : HolLoopProg 64 :=
.seq loopBody267_59 loopBody267_133

def loopBody267_135 : HolLoopProg 64 :=
.mark loopBody267_134

def loopBody267_136 : HolLoopProg 64 :=
.seq loopBody267_115 loopBody267_135

def loopBody267_137 : HolLoopProg 64 :=
.mark loopBody267_136

def loopBody267_138 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody267_137 loopBody267_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody267_139 : HolLoopProg 64 :=
.mark loopBody267_138

def loopBody267_140 : HolLoopProg 64 :=
.seq loopBody267_139 loopBody267_1

def loopBody267_141 : HolLoopProg 64 :=
.mark loopBody267_140

def loopBody267_142 : HolLoopProg 64 :=
.seq loopBody267_27 loopBody267_141

def loopBody267_143 : HolLoopProg 64 :=
.mark loopBody267_142

def loopBody267_144 : HolLoopProg 64 :=
.seq loopBody267_25 loopBody267_143

def loopBody267_145 : HolLoopProg 64 :=
.mark loopBody267_144

def loopBody267_146 : HolLoopProg 64 :=
.seq loopBody267_19 loopBody267_145

def loopBody267_147 : HolLoopProg 64 :=
.mark loopBody267_146

def loopBody267_148 : HolLoopProg 64 :=
.seq loopBody267_115 loopBody267_147

def loopBody267_149 : HolLoopProg 64 :=
.mark loopBody267_148

def loopBody267_150 : HolLoopProg 64 :=
.seq loopBody267_113 loopBody267_149

def loopBody267_151 : HolLoopProg 64 :=
.mark loopBody267_150

def loopBody267_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody267_153 : HolLoopProg 64 :=
.mark loopBody267_152

def loopBody267_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7, 8]

def loopBody267_155 : HolLoopProg 64 :=
.mark loopBody267_154

def loopBody267_156 : HolLoopProg 64 :=
.seq loopBody267_155 loopBody267_1

def loopBody267_157 : HolLoopProg 64 :=
.mark loopBody267_156

def loopBody267_158 : HolLoopProg 64 :=
.seq loopBody267_153 loopBody267_157

def loopBody267_159 : HolLoopProg 64 :=
.mark loopBody267_158

def loopBody267_160 : HolLoopProg 64 :=
.seq loopBody267_63 loopBody267_159

def loopBody267_161 : HolLoopProg 64 :=
.mark loopBody267_160

def loopBody267_162 : HolLoopProg 64 :=
.seq loopBody267_151 loopBody267_161

def loopBody267_163 : HolLoopProg 64 :=
.mark loopBody267_162

def loopBody267_164 : HolLoopProg 64 :=
.seq loopBody267_15 loopBody267_163

def loopBody267_165 : HolLoopProg 64 :=
.mark loopBody267_164

def loopBody267_166 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_165

def loopBody267_167 : HolLoopProg 64 :=
.mark loopBody267_166

def loopBody267_168 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_167

def loopBody267_169 : HolLoopProg 64 :=
.mark loopBody267_168

def loopBody267_170 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_169

def loopBody267_171 : HolLoopProg 64 :=
.mark loopBody267_170

def loopBody267_172 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_171

def loopBody267_173 : HolLoopProg 64 :=
.mark loopBody267_172

def loopBody267_174 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_173

def loopBody267_175 : HolLoopProg 64 :=
.mark loopBody267_174

def loopBody267_176 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_175

def loopBody267_177 : HolLoopProg 64 :=
.mark loopBody267_176

def loopBody267_178 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_177

def loopBody267_179 : HolLoopProg 64 :=
.mark loopBody267_178

def loopBody267_180 : HolLoopProg 64 :=
.seq loopBody267_1 loopBody267_179

def loopBody267_181 : HolLoopProg 64 :=
.mark loopBody267_180

def output267 : Nat × List Nat × HolLoopProg 64 :=
  (331, [0, 1, 2], loopBody267_181)
end InitECandidate.Proofs.FrontendStages.Loop
