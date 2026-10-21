import InitECandidate.Proofs.FrontendStages.Loop.Translate326
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody342_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody342_1 : HolLoopProg 64 :=
.mark loopBody342_0

def loopBody342_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody342_3 : HolLoopProg 64 :=
.mark loopBody342_2

def loopBody342_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody342_5 : HolLoopProg 64 :=
.mark loopBody342_4

def loopBody342_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody342_7 : HolLoopProg 64 :=
.mark loopBody342_6

def loopBody342_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 388) ([3, 4]) (some (3, loopBody342_7, loopBody342_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody342_9 : HolLoopProg 64 :=
.mark loopBody342_8

def loopBody342_10 : HolLoopProg 64 :=
.seq loopBody342_9 loopBody342_1

def loopBody342_11 : HolLoopProg 64 :=
.mark loopBody342_10

def loopBody342_12 : HolLoopProg 64 :=
.seq loopBody342_5 loopBody342_11

def loopBody342_13 : HolLoopProg 64 :=
.mark loopBody342_12

def loopBody342_14 : HolLoopProg 64 :=
.seq loopBody342_3 loopBody342_13

def loopBody342_15 : HolLoopProg 64 :=
.mark loopBody342_14

def loopBody342_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 184#64]),
        Flapjack.HolLoopExp.const 24#64]))

def loopBody342_17 : HolLoopProg 64 :=
.mark loopBody342_16

def loopBody342_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody342_19 : HolLoopProg 64 :=
.mark loopBody342_18

def loopBody342_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody342_21 : HolLoopProg 64 :=
.mark loopBody342_20

def loopBody342_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody342_23 : HolLoopProg 64 :=
.mark loopBody342_22

def loopBody342_24 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 192) ([4, 5, 6]) (some (4, loopBody342_23, loopBody342_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody342_25 : HolLoopProg 64 :=
.mark loopBody342_24

def loopBody342_26 : HolLoopProg 64 :=
.seq loopBody342_25 loopBody342_1

def loopBody342_27 : HolLoopProg 64 :=
.mark loopBody342_26

def loopBody342_28 : HolLoopProg 64 :=
.seq loopBody342_21 loopBody342_27

def loopBody342_29 : HolLoopProg 64 :=
.mark loopBody342_28

def loopBody342_30 : HolLoopProg 64 :=
.seq loopBody342_19 loopBody342_29

def loopBody342_31 : HolLoopProg 64 :=
.mark loopBody342_30

def loopBody342_32 : HolLoopProg 64 :=
.seq loopBody342_17 loopBody342_31

def loopBody342_33 : HolLoopProg 64 :=
.mark loopBody342_32

def loopBody342_34 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_33

def loopBody342_35 : HolLoopProg 64 :=
.mark loopBody342_34

def loopBody342_36 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_35

def loopBody342_37 : HolLoopProg 64 :=
.mark loopBody342_36

def loopBody342_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 184#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody342_39 : HolLoopProg 64 :=
.mark loopBody342_38

def loopBody342_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody342_41 : HolLoopProg 64 :=
.mark loopBody342_40

def loopBody342_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody342_43 : HolLoopProg 64 :=
.mark loopBody342_42

def loopBody342_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody342_45 : HolLoopProg 64 :=
.mark loopBody342_44

def loopBody342_46 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 405) ([5, 6, 7]) (some (5, loopBody342_45, loopBody342_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody342_47 : HolLoopProg 64 :=
.mark loopBody342_46

def loopBody342_48 : HolLoopProg 64 :=
.seq loopBody342_47 loopBody342_1

def loopBody342_49 : HolLoopProg 64 :=
.mark loopBody342_48

def loopBody342_50 : HolLoopProg 64 :=
.seq loopBody342_43 loopBody342_49

def loopBody342_51 : HolLoopProg 64 :=
.mark loopBody342_50

def loopBody342_52 : HolLoopProg 64 :=
.seq loopBody342_41 loopBody342_51

def loopBody342_53 : HolLoopProg 64 :=
.mark loopBody342_52

def loopBody342_54 : HolLoopProg 64 :=
.seq loopBody342_39 loopBody342_53

def loopBody342_55 : HolLoopProg 64 :=
.mark loopBody342_54

def loopBody342_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody342_57 : HolLoopProg 64 :=
.mark loopBody342_56

def loopBody342_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody342_59 : HolLoopProg 64 :=
.mark loopBody342_58

def loopBody342_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody342_61 : HolLoopProg 64 :=
.mark loopBody342_60

def loopBody342_62 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody342_21 loopBody342_61 (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))

def loopBody342_63 : HolLoopProg 64 :=
.mark loopBody342_62

def loopBody342_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody342_65 : HolLoopProg 64 :=
.mark loopBody342_64

def loopBody342_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.load (Flapjack.HolLoopExp.var 4))

def loopBody342_67 : HolLoopProg 64 :=
.mark loopBody342_66

def loopBody342_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 8#64]))

def loopBody342_69 : HolLoopProg 64 :=
.mark loopBody342_68

def loopBody342_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 16#64]))

def loopBody342_71 : HolLoopProg 64 :=
.mark loopBody342_70

def loopBody342_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 24#64]))

def loopBody342_73 : HolLoopProg 64 :=
.mark loopBody342_72

def loopBody342_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6, 7, 8]

def loopBody342_75 : HolLoopProg 64 :=
.mark loopBody342_74

def loopBody342_76 : HolLoopProg 64 :=
.seq loopBody342_75 loopBody342_1

def loopBody342_77 : HolLoopProg 64 :=
.mark loopBody342_76

def loopBody342_78 : HolLoopProg 64 :=
.seq loopBody342_73 loopBody342_77

def loopBody342_79 : HolLoopProg 64 :=
.mark loopBody342_78

def loopBody342_80 : HolLoopProg 64 :=
.seq loopBody342_71 loopBody342_79

def loopBody342_81 : HolLoopProg 64 :=
.mark loopBody342_80

def loopBody342_82 : HolLoopProg 64 :=
.seq loopBody342_69 loopBody342_81

def loopBody342_83 : HolLoopProg 64 :=
.mark loopBody342_82

def loopBody342_84 : HolLoopProg 64 :=
.seq loopBody342_67 loopBody342_83

def loopBody342_85 : HolLoopProg 64 :=
.mark loopBody342_84

def loopBody342_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody342_85 loopBody342_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody342_87 : HolLoopProg 64 :=
.mark loopBody342_86

def loopBody342_88 : HolLoopProg 64 :=
.seq loopBody342_87 loopBody342_1

def loopBody342_89 : HolLoopProg 64 :=
.mark loopBody342_88

def loopBody342_90 : HolLoopProg 64 :=
.seq loopBody342_65 loopBody342_89

def loopBody342_91 : HolLoopProg 64 :=
.mark loopBody342_90

def loopBody342_92 : HolLoopProg 64 :=
.seq loopBody342_63 loopBody342_91

def loopBody342_93 : HolLoopProg 64 :=
.mark loopBody342_92

def loopBody342_94 : HolLoopProg 64 :=
.seq loopBody342_59 loopBody342_93

def loopBody342_95 : HolLoopProg 64 :=
.mark loopBody342_94

def loopBody342_96 : HolLoopProg 64 :=
.seq loopBody342_57 loopBody342_95

def loopBody342_97 : HolLoopProg 64 :=
.mark loopBody342_96

def loopBody342_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody342_99 : HolLoopProg 64 :=
.mark loopBody342_98

def loopBody342_100 : HolLoopProg 64 :=
.seq loopBody342_99 loopBody342_53

def loopBody342_101 : HolLoopProg 64 :=
.mark loopBody342_100

def loopBody342_102 : HolLoopProg 64 :=
.seq loopBody342_97 loopBody342_101

def loopBody342_103 : HolLoopProg 64 :=
.mark loopBody342_102

def loopBody342_104 : HolLoopProg 64 :=
.seq loopBody342_103 loopBody342_97

def loopBody342_105 : HolLoopProg 64 :=
.mark loopBody342_104

def loopBody342_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody342_107 : HolLoopProg 64 :=
.mark loopBody342_106

def loopBody342_108 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 392) ([6]) (some (6, loopBody342_107, loopBody342_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody342_109 : HolLoopProg 64 :=
.mark loopBody342_108

def loopBody342_110 : HolLoopProg 64 :=
.seq loopBody342_109 loopBody342_1

def loopBody342_111 : HolLoopProg 64 :=
.mark loopBody342_110

def loopBody342_112 : HolLoopProg 64 :=
.seq loopBody342_41 loopBody342_111

def loopBody342_113 : HolLoopProg 64 :=
.mark loopBody342_112

def loopBody342_114 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_113

def loopBody342_115 : HolLoopProg 64 :=
.mark loopBody342_114

def loopBody342_116 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_115

def loopBody342_117 : HolLoopProg 64 :=
.mark loopBody342_116

def loopBody342_118 : HolLoopProg 64 :=
.seq loopBody342_105 loopBody342_117

def loopBody342_119 : HolLoopProg 64 :=
.mark loopBody342_118

def loopBody342_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody342_121 : HolLoopProg 64 :=
.mark loopBody342_120

def loopBody342_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody342_123 : HolLoopProg 64 :=
.mark loopBody342_122

def loopBody342_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody342_125 : HolLoopProg 64 :=
.mark loopBody342_124

def loopBody342_126 : HolLoopProg 64 :=
.call (some ([5, 6, 7, 8], Flapjack.Spt.ln)) (some 397) ([9, 10]) (some (9, loopBody342_125, loopBody342_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody342_127 : HolLoopProg 64 :=
.mark loopBody342_126

def loopBody342_128 : HolLoopProg 64 :=
.seq loopBody342_127 loopBody342_1

def loopBody342_129 : HolLoopProg 64 :=
.mark loopBody342_128

def loopBody342_130 : HolLoopProg 64 :=
.seq loopBody342_123 loopBody342_129

def loopBody342_131 : HolLoopProg 64 :=
.mark loopBody342_130

def loopBody342_132 : HolLoopProg 64 :=
.seq loopBody342_121 loopBody342_131

def loopBody342_133 : HolLoopProg 64 :=
.mark loopBody342_132

def loopBody342_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody342_135 : HolLoopProg 64 :=
.mark loopBody342_134

def loopBody342_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody342_137 : HolLoopProg 64 :=
.mark loopBody342_136

def loopBody342_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody342_139 : HolLoopProg 64 :=
.mark loopBody342_138

def loopBody342_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 8)

def loopBody342_141 : HolLoopProg 64 :=
.mark loopBody342_140

def loopBody342_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9, 10, 11, 12]

def loopBody342_143 : HolLoopProg 64 :=
.mark loopBody342_142

def loopBody342_144 : HolLoopProg 64 :=
.seq loopBody342_143 loopBody342_1

def loopBody342_145 : HolLoopProg 64 :=
.mark loopBody342_144

def loopBody342_146 : HolLoopProg 64 :=
.seq loopBody342_141 loopBody342_145

def loopBody342_147 : HolLoopProg 64 :=
.mark loopBody342_146

def loopBody342_148 : HolLoopProg 64 :=
.seq loopBody342_139 loopBody342_147

def loopBody342_149 : HolLoopProg 64 :=
.mark loopBody342_148

def loopBody342_150 : HolLoopProg 64 :=
.seq loopBody342_137 loopBody342_149

def loopBody342_151 : HolLoopProg 64 :=
.mark loopBody342_150

def loopBody342_152 : HolLoopProg 64 :=
.seq loopBody342_135 loopBody342_151

def loopBody342_153 : HolLoopProg 64 :=
.mark loopBody342_152

def loopBody342_154 : HolLoopProg 64 :=
.seq loopBody342_133 loopBody342_153

def loopBody342_155 : HolLoopProg 64 :=
.mark loopBody342_154

def loopBody342_156 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_155

def loopBody342_157 : HolLoopProg 64 :=
.mark loopBody342_156

def loopBody342_158 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_157

def loopBody342_159 : HolLoopProg 64 :=
.mark loopBody342_158

def loopBody342_160 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_159

def loopBody342_161 : HolLoopProg 64 :=
.mark loopBody342_160

def loopBody342_162 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_161

def loopBody342_163 : HolLoopProg 64 :=
.mark loopBody342_162

def loopBody342_164 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_163

def loopBody342_165 : HolLoopProg 64 :=
.mark loopBody342_164

def loopBody342_166 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_165

def loopBody342_167 : HolLoopProg 64 :=
.mark loopBody342_166

def loopBody342_168 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_167

def loopBody342_169 : HolLoopProg 64 :=
.mark loopBody342_168

def loopBody342_170 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_169

def loopBody342_171 : HolLoopProg 64 :=
.mark loopBody342_170

def loopBody342_172 : HolLoopProg 64 :=
.seq loopBody342_119 loopBody342_171

def loopBody342_173 : HolLoopProg 64 :=
.mark loopBody342_172

def loopBody342_174 : HolLoopProg 64 :=
.seq loopBody342_55 loopBody342_173

def loopBody342_175 : HolLoopProg 64 :=
.mark loopBody342_174

def loopBody342_176 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_175

def loopBody342_177 : HolLoopProg 64 :=
.mark loopBody342_176

def loopBody342_178 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_177

def loopBody342_179 : HolLoopProg 64 :=
.mark loopBody342_178

def loopBody342_180 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_179

def loopBody342_181 : HolLoopProg 64 :=
.mark loopBody342_180

def loopBody342_182 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_181

def loopBody342_183 : HolLoopProg 64 :=
.mark loopBody342_182

def loopBody342_184 : HolLoopProg 64 :=
.seq loopBody342_37 loopBody342_183

def loopBody342_185 : HolLoopProg 64 :=
.mark loopBody342_184

def loopBody342_186 : HolLoopProg 64 :=
.seq loopBody342_15 loopBody342_185

def loopBody342_187 : HolLoopProg 64 :=
.mark loopBody342_186

def loopBody342_188 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_187

def loopBody342_189 : HolLoopProg 64 :=
.mark loopBody342_188

def loopBody342_190 : HolLoopProg 64 :=
.seq loopBody342_1 loopBody342_189

def loopBody342_191 : HolLoopProg 64 :=
.mark loopBody342_190

def output342 : Nat × List Nat × HolLoopProg 64 :=
  (406, [0, 1], loopBody342_191)
end InitECandidate.Proofs.FrontendStages.Loop
