import InitECandidate.Proofs.FrontendStages.Loop.Translate369
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody385_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody385_1 : HolLoopProg 64 :=
.mark loopBody385_0

def loopBody385_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 216#64]))

def loopBody385_3 : HolLoopProg 64 :=
.mark loopBody385_2

def loopBody385_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody385_5 : HolLoopProg 64 :=
.mark loopBody385_4

def loopBody385_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody385_7 : HolLoopProg 64 :=
.mark loopBody385_6

def loopBody385_8 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 186) ([5, 6]) (some (5, loopBody385_7, loopBody385_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody385_9 : HolLoopProg 64 :=
.mark loopBody385_8

def loopBody385_10 : HolLoopProg 64 :=
.seq loopBody385_9 loopBody385_1

def loopBody385_11 : HolLoopProg 64 :=
.mark loopBody385_10

def loopBody385_12 : HolLoopProg 64 :=
.seq loopBody385_5 loopBody385_11

def loopBody385_13 : HolLoopProg 64 :=
.mark loopBody385_12

def loopBody385_14 : HolLoopProg 64 :=
.seq loopBody385_3 loopBody385_13

def loopBody385_15 : HolLoopProg 64 :=
.mark loopBody385_14

def loopBody385_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody385_17 : HolLoopProg 64 :=
.mark loopBody385_16

def loopBody385_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody385_19 : HolLoopProg 64 :=
.mark loopBody385_18

def loopBody385_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody385_21 : HolLoopProg 64 :=
.mark loopBody385_20

def loopBody385_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody385_23 : HolLoopProg 64 :=
.mark loopBody385_22

def loopBody385_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody385_21 loopBody385_23 (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.ls PUnit.unit))

def loopBody385_25 : HolLoopProg 64 :=
.mark loopBody385_24

def loopBody385_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody385_27 : HolLoopProg 64 :=
.mark loopBody385_26

def loopBody385_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody385_29 : HolLoopProg 64 :=
.mark loopBody385_28

def loopBody385_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody385_31 : HolLoopProg 64 :=
.mark loopBody385_30

def loopBody385_32 : HolLoopProg 64 :=
.seq loopBody385_31 loopBody385_1

def loopBody385_33 : HolLoopProg 64 :=
.mark loopBody385_32

def loopBody385_34 : HolLoopProg 64 :=
.seq loopBody385_29 loopBody385_33

def loopBody385_35 : HolLoopProg 64 :=
.mark loopBody385_34

def loopBody385_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody385_35 loopBody385_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody385_37 : HolLoopProg 64 :=
.mark loopBody385_36

def loopBody385_38 : HolLoopProg 64 :=
.seq loopBody385_37 loopBody385_1

def loopBody385_39 : HolLoopProg 64 :=
.mark loopBody385_38

def loopBody385_40 : HolLoopProg 64 :=
.seq loopBody385_27 loopBody385_39

def loopBody385_41 : HolLoopProg 64 :=
.mark loopBody385_40

def loopBody385_42 : HolLoopProg 64 :=
.seq loopBody385_25 loopBody385_41

def loopBody385_43 : HolLoopProg 64 :=
.mark loopBody385_42

def loopBody385_44 : HolLoopProg 64 :=
.seq loopBody385_19 loopBody385_43

def loopBody385_45 : HolLoopProg 64 :=
.mark loopBody385_44

def loopBody385_46 : HolLoopProg 64 :=
.seq loopBody385_17 loopBody385_45

def loopBody385_47 : HolLoopProg 64 :=
.mark loopBody385_46

def loopBody385_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 0#64]))

def loopBody385_49 : HolLoopProg 64 :=
.mark loopBody385_48

def loopBody385_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody385_51 : HolLoopProg 64 :=
.mark loopBody385_50

def loopBody385_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody385_53 : HolLoopProg 64 :=
.mark loopBody385_52

def loopBody385_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody385_55 : HolLoopProg 64 :=
.mark loopBody385_54

def loopBody385_56 : HolLoopProg 64 :=
.call (some
  ([6, 7],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))) (some 186) ([8, 9]) (some (8, loopBody385_55, loopBody385_1, (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody385_57 : HolLoopProg 64 :=
.mark loopBody385_56

def loopBody385_58 : HolLoopProg 64 :=
.seq loopBody385_57 loopBody385_1

def loopBody385_59 : HolLoopProg 64 :=
.mark loopBody385_58

def loopBody385_60 : HolLoopProg 64 :=
.seq loopBody385_53 loopBody385_59

def loopBody385_61 : HolLoopProg 64 :=
.mark loopBody385_60

def loopBody385_62 : HolLoopProg 64 :=
.seq loopBody385_51 loopBody385_61

def loopBody385_63 : HolLoopProg 64 :=
.mark loopBody385_62

def loopBody385_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody385_65 : HolLoopProg 64 :=
.mark loopBody385_64

def loopBody385_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody385_67 : HolLoopProg 64 :=
.mark loopBody385_66

def loopBody385_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody385_69 : HolLoopProg 64 :=
.mark loopBody385_68

def loopBody385_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody385_71 : HolLoopProg 64 :=
.mark loopBody385_70

def loopBody385_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody385_69 loopBody385_71 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody385_73 : HolLoopProg 64 :=
.mark loopBody385_72

def loopBody385_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody385_75 : HolLoopProg 64 :=
.mark loopBody385_74

def loopBody385_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody385_77 : HolLoopProg 64 :=
.mark loopBody385_76

def loopBody385_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody385_79 : HolLoopProg 64 :=
.mark loopBody385_78

def loopBody385_80 : HolLoopProg 64 :=
.seq loopBody385_79 loopBody385_1

def loopBody385_81 : HolLoopProg 64 :=
.mark loopBody385_80

def loopBody385_82 : HolLoopProg 64 :=
.seq loopBody385_77 loopBody385_81

def loopBody385_83 : HolLoopProg 64 :=
.mark loopBody385_82

def loopBody385_84 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody385_83 loopBody385_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody385_85 : HolLoopProg 64 :=
.mark loopBody385_84

def loopBody385_86 : HolLoopProg 64 :=
.seq loopBody385_85 loopBody385_1

def loopBody385_87 : HolLoopProg 64 :=
.mark loopBody385_86

def loopBody385_88 : HolLoopProg 64 :=
.seq loopBody385_75 loopBody385_87

def loopBody385_89 : HolLoopProg 64 :=
.mark loopBody385_88

def loopBody385_90 : HolLoopProg 64 :=
.seq loopBody385_73 loopBody385_89

def loopBody385_91 : HolLoopProg 64 :=
.mark loopBody385_90

def loopBody385_92 : HolLoopProg 64 :=
.seq loopBody385_67 loopBody385_91

def loopBody385_93 : HolLoopProg 64 :=
.mark loopBody385_92

def loopBody385_94 : HolLoopProg 64 :=
.seq loopBody385_65 loopBody385_93

def loopBody385_95 : HolLoopProg 64 :=
.mark loopBody385_94

def loopBody385_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody385_97 : HolLoopProg 64 :=
.mark loopBody385_96

def loopBody385_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 40#64)

def loopBody385_99 : HolLoopProg 64 :=
.mark loopBody385_98

def loopBody385_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody385_101 : HolLoopProg 64 :=
.mark loopBody385_100

def loopBody385_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody385_103 : HolLoopProg 64 :=
.mark loopBody385_102

def loopBody385_104 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 447) ([9, 10, 11]) (some (9, loopBody385_103, loopBody385_1, (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody385_105 : HolLoopProg 64 :=
.mark loopBody385_104

def loopBody385_106 : HolLoopProg 64 :=
.seq loopBody385_105 loopBody385_1

def loopBody385_107 : HolLoopProg 64 :=
.mark loopBody385_106

def loopBody385_108 : HolLoopProg 64 :=
.seq loopBody385_101 loopBody385_107

def loopBody385_109 : HolLoopProg 64 :=
.mark loopBody385_108

def loopBody385_110 : HolLoopProg 64 :=
.seq loopBody385_99 loopBody385_109

def loopBody385_111 : HolLoopProg 64 :=
.mark loopBody385_110

def loopBody385_112 : HolLoopProg 64 :=
.seq loopBody385_97 loopBody385_111

def loopBody385_113 : HolLoopProg 64 :=
.mark loopBody385_112

def loopBody385_114 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_113

def loopBody385_115 : HolLoopProg 64 :=
.mark loopBody385_114

def loopBody385_116 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_115

def loopBody385_117 : HolLoopProg 64 :=
.mark loopBody385_116

def loopBody385_118 : HolLoopProg 64 :=
.seq loopBody385_95 loopBody385_117

def loopBody385_119 : HolLoopProg 64 :=
.mark loopBody385_118

def loopBody385_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 8#64]))

def loopBody385_121 : HolLoopProg 64 :=
.mark loopBody385_120

def loopBody385_122 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 9 (Flapjack.RegImm.reg 10) loopBody385_69 loopBody385_71 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))

def loopBody385_123 : HolLoopProg 64 :=
.mark loopBody385_122

def loopBody385_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody385_125 : HolLoopProg 64 :=
.mark loopBody385_124

def loopBody385_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody385_127 : HolLoopProg 64 :=
.mark loopBody385_126

def loopBody385_128 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.ln)) (some 193) ([9, 10]) (some (9, loopBody385_103, loopBody385_1, (Flapjack.Spt.ln)))

def loopBody385_129 : HolLoopProg 64 :=
.mark loopBody385_128

def loopBody385_130 : HolLoopProg 64 :=
.seq loopBody385_129 loopBody385_1

def loopBody385_131 : HolLoopProg 64 :=
.mark loopBody385_130

def loopBody385_132 : HolLoopProg 64 :=
.seq loopBody385_127 loopBody385_131

def loopBody385_133 : HolLoopProg 64 :=
.mark loopBody385_132

def loopBody385_134 : HolLoopProg 64 :=
.seq loopBody385_125 loopBody385_133

def loopBody385_135 : HolLoopProg 64 :=
.mark loopBody385_134

def loopBody385_136 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_135

def loopBody385_137 : HolLoopProg 64 :=
.mark loopBody385_136

def loopBody385_138 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_137

def loopBody385_139 : HolLoopProg 64 :=
.mark loopBody385_138

def loopBody385_140 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody385_139 loopBody385_1 (Flapjack.Spt.ln)

def loopBody385_141 : HolLoopProg 64 :=
.mark loopBody385_140

def loopBody385_142 : HolLoopProg 64 :=
.seq loopBody385_141 loopBody385_1

def loopBody385_143 : HolLoopProg 64 :=
.mark loopBody385_142

def loopBody385_144 : HolLoopProg 64 :=
.seq loopBody385_75 loopBody385_143

def loopBody385_145 : HolLoopProg 64 :=
.mark loopBody385_144

def loopBody385_146 : HolLoopProg 64 :=
.seq loopBody385_123 loopBody385_145

def loopBody385_147 : HolLoopProg 64 :=
.mark loopBody385_146

def loopBody385_148 : HolLoopProg 64 :=
.seq loopBody385_67 loopBody385_147

def loopBody385_149 : HolLoopProg 64 :=
.mark loopBody385_148

def loopBody385_150 : HolLoopProg 64 :=
.seq loopBody385_121 loopBody385_149

def loopBody385_151 : HolLoopProg 64 :=
.mark loopBody385_150

def loopBody385_152 : HolLoopProg 64 :=
.seq loopBody385_119 loopBody385_151

def loopBody385_153 : HolLoopProg 64 :=
.mark loopBody385_152

def loopBody385_154 : HolLoopProg 64 :=
.seq loopBody385_153 loopBody385_83

def loopBody385_155 : HolLoopProg 64 :=
.mark loopBody385_154

def loopBody385_156 : HolLoopProg 64 :=
.seq loopBody385_63 loopBody385_155

def loopBody385_157 : HolLoopProg 64 :=
.mark loopBody385_156

def loopBody385_158 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_157

def loopBody385_159 : HolLoopProg 64 :=
.mark loopBody385_158

def loopBody385_160 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_159

def loopBody385_161 : HolLoopProg 64 :=
.mark loopBody385_160

def loopBody385_162 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_161

def loopBody385_163 : HolLoopProg 64 :=
.mark loopBody385_162

def loopBody385_164 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_163

def loopBody385_165 : HolLoopProg 64 :=
.mark loopBody385_164

def loopBody385_166 : HolLoopProg 64 :=
.seq loopBody385_49 loopBody385_165

def loopBody385_167 : HolLoopProg 64 :=
.mark loopBody385_166

def loopBody385_168 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_167

def loopBody385_169 : HolLoopProg 64 :=
.mark loopBody385_168

def loopBody385_170 : HolLoopProg 64 :=
.seq loopBody385_47 loopBody385_169

def loopBody385_171 : HolLoopProg 64 :=
.mark loopBody385_170

def loopBody385_172 : HolLoopProg 64 :=
.seq loopBody385_15 loopBody385_171

def loopBody385_173 : HolLoopProg 64 :=
.mark loopBody385_172

def loopBody385_174 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_173

def loopBody385_175 : HolLoopProg 64 :=
.mark loopBody385_174

def loopBody385_176 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_175

def loopBody385_177 : HolLoopProg 64 :=
.mark loopBody385_176

def loopBody385_178 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_177

def loopBody385_179 : HolLoopProg 64 :=
.mark loopBody385_178

def loopBody385_180 : HolLoopProg 64 :=
.seq loopBody385_1 loopBody385_179

def loopBody385_181 : HolLoopProg 64 :=
.mark loopBody385_180

def output385 : Nat × List Nat × HolLoopProg 64 :=
  (449, [0, 1, 2], loopBody385_181)
end InitECandidate.Proofs.FrontendStages.Loop
