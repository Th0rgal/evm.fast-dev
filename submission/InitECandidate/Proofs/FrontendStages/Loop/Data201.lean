import InitECandidate.Proofs.FrontendStages.Loop.Translate185
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody201_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody201_1 : HolLoopProg 64 :=
.mark loopBody201_0

def loopBody201_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody201_3 : HolLoopProg 64 :=
.mark loopBody201_2

def loopBody201_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody201_5 : HolLoopProg 64 :=
.mark loopBody201_4

def loopBody201_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody201_7 : HolLoopProg 64 :=
.mark loopBody201_6

def loopBody201_8 : HolLoopProg 64 :=
.call (some ([3, 4, 5, 6], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 161) ([7, 8]) (some (7, loopBody201_7, loopBody201_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody201_9 : HolLoopProg 64 :=
.mark loopBody201_8

def loopBody201_10 : HolLoopProg 64 :=
.seq loopBody201_9 loopBody201_1

def loopBody201_11 : HolLoopProg 64 :=
.mark loopBody201_10

def loopBody201_12 : HolLoopProg 64 :=
.seq loopBody201_5 loopBody201_11

def loopBody201_13 : HolLoopProg 64 :=
.mark loopBody201_12

def loopBody201_14 : HolLoopProg 64 :=
.seq loopBody201_3 loopBody201_13

def loopBody201_15 : HolLoopProg 64 :=
.mark loopBody201_14

def loopBody201_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody201_17 : HolLoopProg 64 :=
.mark loopBody201_16

def loopBody201_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody201_19 : HolLoopProg 64 :=
.mark loopBody201_18

def loopBody201_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody201_21 : HolLoopProg 64 :=
.mark loopBody201_20

def loopBody201_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody201_23 : HolLoopProg 64 :=
.mark loopBody201_22

def loopBody201_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.reg 9) loopBody201_21 loopBody201_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody201_25 : HolLoopProg 64 :=
.mark loopBody201_24

def loopBody201_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody201_27 : HolLoopProg 64 :=
.mark loopBody201_26

def loopBody201_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody201_29 : HolLoopProg 64 :=
.mark loopBody201_28

def loopBody201_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 7)

def loopBody201_31 : HolLoopProg 64 :=
.mark loopBody201_30

def loopBody201_32 : HolLoopProg 64 :=
.seq loopBody201_31 loopBody201_1

def loopBody201_33 : HolLoopProg 64 :=
.mark loopBody201_32

def loopBody201_34 : HolLoopProg 64 :=
.seq loopBody201_33 loopBody201_1

def loopBody201_35 : HolLoopProg 64 :=
.mark loopBody201_34

def loopBody201_36 : HolLoopProg 64 :=
.seq loopBody201_29 loopBody201_35

def loopBody201_37 : HolLoopProg 64 :=
.mark loopBody201_36

def loopBody201_38 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_37

def loopBody201_39 : HolLoopProg 64 :=
.mark loopBody201_38

def loopBody201_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 3#64)

def loopBody201_41 : HolLoopProg 64 :=
.mark loopBody201_40

def loopBody201_42 : HolLoopProg 64 :=
.seq loopBody201_41 loopBody201_7

def loopBody201_43 : HolLoopProg 64 :=
.mark loopBody201_42

def loopBody201_44 : HolLoopProg 64 :=
.seq loopBody201_39 loopBody201_43

def loopBody201_45 : HolLoopProg 64 :=
.mark loopBody201_44

def loopBody201_46 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody201_45 loopBody201_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody201_47 : HolLoopProg 64 :=
.mark loopBody201_46

def loopBody201_48 : HolLoopProg 64 :=
.seq loopBody201_47 loopBody201_1

def loopBody201_49 : HolLoopProg 64 :=
.mark loopBody201_48

def loopBody201_50 : HolLoopProg 64 :=
.seq loopBody201_27 loopBody201_49

def loopBody201_51 : HolLoopProg 64 :=
.mark loopBody201_50

def loopBody201_52 : HolLoopProg 64 :=
.seq loopBody201_25 loopBody201_51

def loopBody201_53 : HolLoopProg 64 :=
.mark loopBody201_52

def loopBody201_54 : HolLoopProg 64 :=
.seq loopBody201_19 loopBody201_53

def loopBody201_55 : HolLoopProg 64 :=
.mark loopBody201_54

def loopBody201_56 : HolLoopProg 64 :=
.seq loopBody201_17 loopBody201_55

def loopBody201_57 : HolLoopProg 64 :=
.mark loopBody201_56

def loopBody201_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody201_59 : HolLoopProg 64 :=
.mark loopBody201_58

def loopBody201_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody201_61 : HolLoopProg 64 :=
.mark loopBody201_60

def loopBody201_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 7 7

def loopBody201_63 : HolLoopProg 64 :=
.mark loopBody201_62

def loopBody201_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody201_65 : HolLoopProg 64 :=
.mark loopBody201_64

def loopBody201_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody201_67 : HolLoopProg 64 :=
.mark loopBody201_66

def loopBody201_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody201_69 : HolLoopProg 64 :=
.mark loopBody201_68

def loopBody201_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody201_69 loopBody201_19 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody201_71 : HolLoopProg 64 :=
.mark loopBody201_70

def loopBody201_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody201_73 : HolLoopProg 64 :=
.mark loopBody201_72

def loopBody201_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 2#64)

def loopBody201_75 : HolLoopProg 64 :=
.mark loopBody201_74

def loopBody201_76 : HolLoopProg 64 :=
.seq loopBody201_75 loopBody201_35

def loopBody201_77 : HolLoopProg 64 :=
.mark loopBody201_76

def loopBody201_78 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_77

def loopBody201_79 : HolLoopProg 64 :=
.mark loopBody201_78

def loopBody201_80 : HolLoopProg 64 :=
.seq loopBody201_79 loopBody201_43

def loopBody201_81 : HolLoopProg 64 :=
.mark loopBody201_80

def loopBody201_82 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody201_81 loopBody201_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody201_83 : HolLoopProg 64 :=
.mark loopBody201_82

def loopBody201_84 : HolLoopProg 64 :=
.seq loopBody201_83 loopBody201_1

def loopBody201_85 : HolLoopProg 64 :=
.mark loopBody201_84

def loopBody201_86 : HolLoopProg 64 :=
.seq loopBody201_73 loopBody201_85

def loopBody201_87 : HolLoopProg 64 :=
.mark loopBody201_86

def loopBody201_88 : HolLoopProg 64 :=
.seq loopBody201_71 loopBody201_87

def loopBody201_89 : HolLoopProg 64 :=
.mark loopBody201_88

def loopBody201_90 : HolLoopProg 64 :=
.seq loopBody201_67 loopBody201_89

def loopBody201_91 : HolLoopProg 64 :=
.mark loopBody201_90

def loopBody201_92 : HolLoopProg 64 :=
.seq loopBody201_65 loopBody201_91

def loopBody201_93 : HolLoopProg 64 :=
.mark loopBody201_92

def loopBody201_94 : HolLoopProg 64 :=
.seq loopBody201_63 loopBody201_93

def loopBody201_95 : HolLoopProg 64 :=
.mark loopBody201_94

def loopBody201_96 : HolLoopProg 64 :=
.seq loopBody201_61 loopBody201_95

def loopBody201_97 : HolLoopProg 64 :=
.mark loopBody201_96

def loopBody201_98 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody201_97 loopBody201_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody201_99 : HolLoopProg 64 :=
.mark loopBody201_98

def loopBody201_100 : HolLoopProg 64 :=
.seq loopBody201_99 loopBody201_1

def loopBody201_101 : HolLoopProg 64 :=
.mark loopBody201_100

def loopBody201_102 : HolLoopProg 64 :=
.seq loopBody201_27 loopBody201_101

def loopBody201_103 : HolLoopProg 64 :=
.mark loopBody201_102

def loopBody201_104 : HolLoopProg 64 :=
.seq loopBody201_25 loopBody201_103

def loopBody201_105 : HolLoopProg 64 :=
.mark loopBody201_104

def loopBody201_106 : HolLoopProg 64 :=
.seq loopBody201_19 loopBody201_105

def loopBody201_107 : HolLoopProg 64 :=
.mark loopBody201_106

def loopBody201_108 : HolLoopProg 64 :=
.seq loopBody201_59 loopBody201_107

def loopBody201_109 : HolLoopProg 64 :=
.mark loopBody201_108

def loopBody201_110 : HolLoopProg 64 :=
.seq loopBody201_57 loopBody201_109

def loopBody201_111 : HolLoopProg 64 :=
.mark loopBody201_110

def loopBody201_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody201_113 : HolLoopProg 64 :=
.mark loopBody201_112

def loopBody201_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody201_115 : HolLoopProg 64 :=
.mark loopBody201_114

def loopBody201_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.RegImm.reg 9) loopBody201_21 loopBody201_23 (Flapjack.Spt.bn
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody201_117 : HolLoopProg 64 :=
.mark loopBody201_116

def loopBody201_118 : HolLoopProg 64 :=
.seq loopBody201_41 loopBody201_35

def loopBody201_119 : HolLoopProg 64 :=
.mark loopBody201_118

def loopBody201_120 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_119

def loopBody201_121 : HolLoopProg 64 :=
.mark loopBody201_120

def loopBody201_122 : HolLoopProg 64 :=
.seq loopBody201_121 loopBody201_43

def loopBody201_123 : HolLoopProg 64 :=
.mark loopBody201_122

def loopBody201_124 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody201_123 loopBody201_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody201_125 : HolLoopProg 64 :=
.mark loopBody201_124

def loopBody201_126 : HolLoopProg 64 :=
.seq loopBody201_125 loopBody201_1

def loopBody201_127 : HolLoopProg 64 :=
.mark loopBody201_126

def loopBody201_128 : HolLoopProg 64 :=
.seq loopBody201_27 loopBody201_127

def loopBody201_129 : HolLoopProg 64 :=
.mark loopBody201_128

def loopBody201_130 : HolLoopProg 64 :=
.seq loopBody201_117 loopBody201_129

def loopBody201_131 : HolLoopProg 64 :=
.mark loopBody201_130

def loopBody201_132 : HolLoopProg 64 :=
.seq loopBody201_115 loopBody201_131

def loopBody201_133 : HolLoopProg 64 :=
.mark loopBody201_132

def loopBody201_134 : HolLoopProg 64 :=
.seq loopBody201_113 loopBody201_133

def loopBody201_135 : HolLoopProg 64 :=
.mark loopBody201_134

def loopBody201_136 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody201_135 loopBody201_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody201_137 : HolLoopProg 64 :=
.mark loopBody201_136

def loopBody201_138 : HolLoopProg 64 :=
.seq loopBody201_137 loopBody201_1

def loopBody201_139 : HolLoopProg 64 :=
.mark loopBody201_138

def loopBody201_140 : HolLoopProg 64 :=
.seq loopBody201_27 loopBody201_139

def loopBody201_141 : HolLoopProg 64 :=
.mark loopBody201_140

def loopBody201_142 : HolLoopProg 64 :=
.seq loopBody201_25 loopBody201_141

def loopBody201_143 : HolLoopProg 64 :=
.mark loopBody201_142

def loopBody201_144 : HolLoopProg 64 :=
.seq loopBody201_19 loopBody201_143

def loopBody201_145 : HolLoopProg 64 :=
.mark loopBody201_144

def loopBody201_146 : HolLoopProg 64 :=
.seq loopBody201_113 loopBody201_145

def loopBody201_147 : HolLoopProg 64 :=
.mark loopBody201_146

def loopBody201_148 : HolLoopProg 64 :=
.seq loopBody201_111 loopBody201_147

def loopBody201_149 : HolLoopProg 64 :=
.mark loopBody201_148

def loopBody201_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7, 8]

def loopBody201_151 : HolLoopProg 64 :=
.mark loopBody201_150

def loopBody201_152 : HolLoopProg 64 :=
.seq loopBody201_151 loopBody201_1

def loopBody201_153 : HolLoopProg 64 :=
.mark loopBody201_152

def loopBody201_154 : HolLoopProg 64 :=
.seq loopBody201_59 loopBody201_153

def loopBody201_155 : HolLoopProg 64 :=
.mark loopBody201_154

def loopBody201_156 : HolLoopProg 64 :=
.seq loopBody201_61 loopBody201_155

def loopBody201_157 : HolLoopProg 64 :=
.mark loopBody201_156

def loopBody201_158 : HolLoopProg 64 :=
.seq loopBody201_149 loopBody201_157

def loopBody201_159 : HolLoopProg 64 :=
.mark loopBody201_158

def loopBody201_160 : HolLoopProg 64 :=
.seq loopBody201_15 loopBody201_159

def loopBody201_161 : HolLoopProg 64 :=
.mark loopBody201_160

def loopBody201_162 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_161

def loopBody201_163 : HolLoopProg 64 :=
.mark loopBody201_162

def loopBody201_164 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_163

def loopBody201_165 : HolLoopProg 64 :=
.mark loopBody201_164

def loopBody201_166 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_165

def loopBody201_167 : HolLoopProg 64 :=
.mark loopBody201_166

def loopBody201_168 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_167

def loopBody201_169 : HolLoopProg 64 :=
.mark loopBody201_168

def loopBody201_170 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_169

def loopBody201_171 : HolLoopProg 64 :=
.mark loopBody201_170

def loopBody201_172 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_171

def loopBody201_173 : HolLoopProg 64 :=
.mark loopBody201_172

def loopBody201_174 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_173

def loopBody201_175 : HolLoopProg 64 :=
.mark loopBody201_174

def loopBody201_176 : HolLoopProg 64 :=
.seq loopBody201_1 loopBody201_175

def loopBody201_177 : HolLoopProg 64 :=
.mark loopBody201_176

def output201 : Nat × List Nat × HolLoopProg 64 :=
  (265, [0, 1, 2], loopBody201_177)
end InitECandidate.Proofs.FrontendStages.Loop
