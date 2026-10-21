import InitECandidate.Proofs.FrontendStages.Loop.Translate327
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody343_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody343_1 : HolLoopProg 64 :=
.mark loopBody343_0

def loopBody343_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 184#64]),
        Flapjack.HolLoopExp.const 56#64]))

def loopBody343_3 : HolLoopProg 64 :=
.mark loopBody343_2

def loopBody343_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody343_5 : HolLoopProg 64 :=
.mark loopBody343_4

def loopBody343_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody343_7 : HolLoopProg 64 :=
.mark loopBody343_6

def loopBody343_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 187) ([3, 4]) (some (3, loopBody343_7, loopBody343_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody343_9 : HolLoopProg 64 :=
.mark loopBody343_8

def loopBody343_10 : HolLoopProg 64 :=
.seq loopBody343_9 loopBody343_1

def loopBody343_11 : HolLoopProg 64 :=
.mark loopBody343_10

def loopBody343_12 : HolLoopProg 64 :=
.seq loopBody343_5 loopBody343_11

def loopBody343_13 : HolLoopProg 64 :=
.mark loopBody343_12

def loopBody343_14 : HolLoopProg 64 :=
.seq loopBody343_3 loopBody343_13

def loopBody343_15 : HolLoopProg 64 :=
.mark loopBody343_14

def loopBody343_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody343_17 : HolLoopProg 64 :=
.mark loopBody343_16

def loopBody343_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody343_19 : HolLoopProg 64 :=
.mark loopBody343_18

def loopBody343_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody343_21 : HolLoopProg 64 :=
.mark loopBody343_20

def loopBody343_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody343_23 : HolLoopProg 64 :=
.mark loopBody343_22

def loopBody343_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody343_21 loopBody343_23 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody343_25 : HolLoopProg 64 :=
.mark loopBody343_24

def loopBody343_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody343_27 : HolLoopProg 64 :=
.mark loopBody343_26

def loopBody343_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody343_29 : HolLoopProg 64 :=
.mark loopBody343_28

def loopBody343_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody343_31 : HolLoopProg 64 :=
.mark loopBody343_30

def loopBody343_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3, 4, 5, 6]

def loopBody343_33 : HolLoopProg 64 :=
.mark loopBody343_32

def loopBody343_34 : HolLoopProg 64 :=
.seq loopBody343_33 loopBody343_1

def loopBody343_35 : HolLoopProg 64 :=
.mark loopBody343_34

def loopBody343_36 : HolLoopProg 64 :=
.seq loopBody343_31 loopBody343_35

def loopBody343_37 : HolLoopProg 64 :=
.mark loopBody343_36

def loopBody343_38 : HolLoopProg 64 :=
.seq loopBody343_19 loopBody343_37

def loopBody343_39 : HolLoopProg 64 :=
.mark loopBody343_38

def loopBody343_40 : HolLoopProg 64 :=
.seq loopBody343_23 loopBody343_39

def loopBody343_41 : HolLoopProg 64 :=
.mark loopBody343_40

def loopBody343_42 : HolLoopProg 64 :=
.seq loopBody343_29 loopBody343_41

def loopBody343_43 : HolLoopProg 64 :=
.mark loopBody343_42

def loopBody343_44 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody343_43 loopBody343_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody343_45 : HolLoopProg 64 :=
.mark loopBody343_44

def loopBody343_46 : HolLoopProg 64 :=
.seq loopBody343_45 loopBody343_1

def loopBody343_47 : HolLoopProg 64 :=
.mark loopBody343_46

def loopBody343_48 : HolLoopProg 64 :=
.seq loopBody343_27 loopBody343_47

def loopBody343_49 : HolLoopProg 64 :=
.mark loopBody343_48

def loopBody343_50 : HolLoopProg 64 :=
.seq loopBody343_25 loopBody343_49

def loopBody343_51 : HolLoopProg 64 :=
.mark loopBody343_50

def loopBody343_52 : HolLoopProg 64 :=
.seq loopBody343_19 loopBody343_51

def loopBody343_53 : HolLoopProg 64 :=
.mark loopBody343_52

def loopBody343_54 : HolLoopProg 64 :=
.seq loopBody343_17 loopBody343_53

def loopBody343_55 : HolLoopProg 64 :=
.mark loopBody343_54

def loopBody343_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody343_57 : HolLoopProg 64 :=
.mark loopBody343_56

def loopBody343_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody343_59 : HolLoopProg 64 :=
.mark loopBody343_58

def loopBody343_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody343_61 : HolLoopProg 64 :=
.mark loopBody343_60

def loopBody343_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody343_63 : HolLoopProg 64 :=
.mark loopBody343_62

def loopBody343_64 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 405) ([5, 6, 7]) (some (5, loopBody343_63, loopBody343_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody343_65 : HolLoopProg 64 :=
.mark loopBody343_64

def loopBody343_66 : HolLoopProg 64 :=
.seq loopBody343_65 loopBody343_1

def loopBody343_67 : HolLoopProg 64 :=
.mark loopBody343_66

def loopBody343_68 : HolLoopProg 64 :=
.seq loopBody343_61 loopBody343_67

def loopBody343_69 : HolLoopProg 64 :=
.mark loopBody343_68

def loopBody343_70 : HolLoopProg 64 :=
.seq loopBody343_59 loopBody343_69

def loopBody343_71 : HolLoopProg 64 :=
.mark loopBody343_70

def loopBody343_72 : HolLoopProg 64 :=
.seq loopBody343_57 loopBody343_71

def loopBody343_73 : HolLoopProg 64 :=
.mark loopBody343_72

def loopBody343_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody343_75 : HolLoopProg 64 :=
.mark loopBody343_74

def loopBody343_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody343_77 : HolLoopProg 64 :=
.mark loopBody343_76

def loopBody343_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody343_79 : HolLoopProg 64 :=
.mark loopBody343_78

def loopBody343_80 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody343_79 loopBody343_31 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))

def loopBody343_81 : HolLoopProg 64 :=
.mark loopBody343_80

def loopBody343_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody343_83 : HolLoopProg 64 :=
.mark loopBody343_82

def loopBody343_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 4))

def loopBody343_85 : HolLoopProg 64 :=
.mark loopBody343_84

def loopBody343_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 8#64]))

def loopBody343_87 : HolLoopProg 64 :=
.mark loopBody343_86

def loopBody343_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 16#64]))

def loopBody343_89 : HolLoopProg 64 :=
.mark loopBody343_88

def loopBody343_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 24#64]))

def loopBody343_91 : HolLoopProg 64 :=
.mark loopBody343_90

def loopBody343_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6, 7, 8]

def loopBody343_93 : HolLoopProg 64 :=
.mark loopBody343_92

def loopBody343_94 : HolLoopProg 64 :=
.seq loopBody343_93 loopBody343_1

def loopBody343_95 : HolLoopProg 64 :=
.mark loopBody343_94

def loopBody343_96 : HolLoopProg 64 :=
.seq loopBody343_91 loopBody343_95

def loopBody343_97 : HolLoopProg 64 :=
.mark loopBody343_96

def loopBody343_98 : HolLoopProg 64 :=
.seq loopBody343_89 loopBody343_97

def loopBody343_99 : HolLoopProg 64 :=
.mark loopBody343_98

def loopBody343_100 : HolLoopProg 64 :=
.seq loopBody343_87 loopBody343_99

def loopBody343_101 : HolLoopProg 64 :=
.mark loopBody343_100

def loopBody343_102 : HolLoopProg 64 :=
.seq loopBody343_85 loopBody343_101

def loopBody343_103 : HolLoopProg 64 :=
.mark loopBody343_102

def loopBody343_104 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody343_103 loopBody343_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody343_105 : HolLoopProg 64 :=
.mark loopBody343_104

def loopBody343_106 : HolLoopProg 64 :=
.seq loopBody343_105 loopBody343_1

def loopBody343_107 : HolLoopProg 64 :=
.mark loopBody343_106

def loopBody343_108 : HolLoopProg 64 :=
.seq loopBody343_83 loopBody343_107

def loopBody343_109 : HolLoopProg 64 :=
.mark loopBody343_108

def loopBody343_110 : HolLoopProg 64 :=
.seq loopBody343_81 loopBody343_109

def loopBody343_111 : HolLoopProg 64 :=
.mark loopBody343_110

def loopBody343_112 : HolLoopProg 64 :=
.seq loopBody343_77 loopBody343_111

def loopBody343_113 : HolLoopProg 64 :=
.mark loopBody343_112

def loopBody343_114 : HolLoopProg 64 :=
.seq loopBody343_75 loopBody343_113

def loopBody343_115 : HolLoopProg 64 :=
.mark loopBody343_114

def loopBody343_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody343_117 : HolLoopProg 64 :=
.mark loopBody343_116

def loopBody343_118 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 392) ([6]) (some (6, loopBody343_117, loopBody343_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody343_119 : HolLoopProg 64 :=
.mark loopBody343_118

def loopBody343_120 : HolLoopProg 64 :=
.seq loopBody343_119 loopBody343_1

def loopBody343_121 : HolLoopProg 64 :=
.mark loopBody343_120

def loopBody343_122 : HolLoopProg 64 :=
.seq loopBody343_59 loopBody343_121

def loopBody343_123 : HolLoopProg 64 :=
.mark loopBody343_122

def loopBody343_124 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_123

def loopBody343_125 : HolLoopProg 64 :=
.mark loopBody343_124

def loopBody343_126 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_125

def loopBody343_127 : HolLoopProg 64 :=
.mark loopBody343_126

def loopBody343_128 : HolLoopProg 64 :=
.seq loopBody343_115 loopBody343_127

def loopBody343_129 : HolLoopProg 64 :=
.mark loopBody343_128

def loopBody343_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody343_131 : HolLoopProg 64 :=
.mark loopBody343_130

def loopBody343_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody343_133 : HolLoopProg 64 :=
.mark loopBody343_132

def loopBody343_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody343_135 : HolLoopProg 64 :=
.mark loopBody343_134

def loopBody343_136 : HolLoopProg 64 :=
.call (some ([5, 6, 7, 8], Flapjack.Spt.ln)) (some 397) ([9, 10]) (some (9, loopBody343_135, loopBody343_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody343_137 : HolLoopProg 64 :=
.mark loopBody343_136

def loopBody343_138 : HolLoopProg 64 :=
.seq loopBody343_137 loopBody343_1

def loopBody343_139 : HolLoopProg 64 :=
.mark loopBody343_138

def loopBody343_140 : HolLoopProg 64 :=
.seq loopBody343_133 loopBody343_139

def loopBody343_141 : HolLoopProg 64 :=
.mark loopBody343_140

def loopBody343_142 : HolLoopProg 64 :=
.seq loopBody343_131 loopBody343_141

def loopBody343_143 : HolLoopProg 64 :=
.mark loopBody343_142

def loopBody343_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody343_145 : HolLoopProg 64 :=
.mark loopBody343_144

def loopBody343_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody343_147 : HolLoopProg 64 :=
.mark loopBody343_146

def loopBody343_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody343_149 : HolLoopProg 64 :=
.mark loopBody343_148

def loopBody343_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 8)

def loopBody343_151 : HolLoopProg 64 :=
.mark loopBody343_150

def loopBody343_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9, 10, 11, 12]

def loopBody343_153 : HolLoopProg 64 :=
.mark loopBody343_152

def loopBody343_154 : HolLoopProg 64 :=
.seq loopBody343_153 loopBody343_1

def loopBody343_155 : HolLoopProg 64 :=
.mark loopBody343_154

def loopBody343_156 : HolLoopProg 64 :=
.seq loopBody343_151 loopBody343_155

def loopBody343_157 : HolLoopProg 64 :=
.mark loopBody343_156

def loopBody343_158 : HolLoopProg 64 :=
.seq loopBody343_149 loopBody343_157

def loopBody343_159 : HolLoopProg 64 :=
.mark loopBody343_158

def loopBody343_160 : HolLoopProg 64 :=
.seq loopBody343_147 loopBody343_159

def loopBody343_161 : HolLoopProg 64 :=
.mark loopBody343_160

def loopBody343_162 : HolLoopProg 64 :=
.seq loopBody343_145 loopBody343_161

def loopBody343_163 : HolLoopProg 64 :=
.mark loopBody343_162

def loopBody343_164 : HolLoopProg 64 :=
.seq loopBody343_143 loopBody343_163

def loopBody343_165 : HolLoopProg 64 :=
.mark loopBody343_164

def loopBody343_166 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_165

def loopBody343_167 : HolLoopProg 64 :=
.mark loopBody343_166

def loopBody343_168 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_167

def loopBody343_169 : HolLoopProg 64 :=
.mark loopBody343_168

def loopBody343_170 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_169

def loopBody343_171 : HolLoopProg 64 :=
.mark loopBody343_170

def loopBody343_172 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_171

def loopBody343_173 : HolLoopProg 64 :=
.mark loopBody343_172

def loopBody343_174 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_173

def loopBody343_175 : HolLoopProg 64 :=
.mark loopBody343_174

def loopBody343_176 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_175

def loopBody343_177 : HolLoopProg 64 :=
.mark loopBody343_176

def loopBody343_178 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_177

def loopBody343_179 : HolLoopProg 64 :=
.mark loopBody343_178

def loopBody343_180 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_179

def loopBody343_181 : HolLoopProg 64 :=
.mark loopBody343_180

def loopBody343_182 : HolLoopProg 64 :=
.seq loopBody343_129 loopBody343_181

def loopBody343_183 : HolLoopProg 64 :=
.mark loopBody343_182

def loopBody343_184 : HolLoopProg 64 :=
.seq loopBody343_73 loopBody343_183

def loopBody343_185 : HolLoopProg 64 :=
.mark loopBody343_184

def loopBody343_186 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_185

def loopBody343_187 : HolLoopProg 64 :=
.mark loopBody343_186

def loopBody343_188 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_187

def loopBody343_189 : HolLoopProg 64 :=
.mark loopBody343_188

def loopBody343_190 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_189

def loopBody343_191 : HolLoopProg 64 :=
.mark loopBody343_190

def loopBody343_192 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_191

def loopBody343_193 : HolLoopProg 64 :=
.mark loopBody343_192

def loopBody343_194 : HolLoopProg 64 :=
.seq loopBody343_55 loopBody343_193

def loopBody343_195 : HolLoopProg 64 :=
.mark loopBody343_194

def loopBody343_196 : HolLoopProg 64 :=
.seq loopBody343_15 loopBody343_195

def loopBody343_197 : HolLoopProg 64 :=
.mark loopBody343_196

def loopBody343_198 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_197

def loopBody343_199 : HolLoopProg 64 :=
.mark loopBody343_198

def loopBody343_200 : HolLoopProg 64 :=
.seq loopBody343_1 loopBody343_199

def loopBody343_201 : HolLoopProg 64 :=
.mark loopBody343_200

def output343 : Nat × List Nat × HolLoopProg 64 :=
  (407, [0, 1], loopBody343_201)
end InitECandidate.Proofs.FrontendStages.Loop
