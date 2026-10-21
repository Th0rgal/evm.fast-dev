import InitECandidate.Proofs.FrontendStages.Loop.Translate754
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody770_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody770_1 : HolLoopProg 64 :=
.mark loopBody770_0

def loopBody770_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody770_3 : HolLoopProg 64 :=
.mark loopBody770_2

def loopBody770_4 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (4, loopBody770_3, loopBody770_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody770_5 : HolLoopProg 64 :=
.mark loopBody770_4

def loopBody770_6 : HolLoopProg 64 :=
.seq loopBody770_5 loopBody770_1

def loopBody770_7 : HolLoopProg 64 :=
.mark loopBody770_6

def loopBody770_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody770_9 : HolLoopProg 64 :=
.mark loopBody770_8

def loopBody770_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody770_11 : HolLoopProg 64 :=
.mark loopBody770_10

def loopBody770_12 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody770_11, loopBody770_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody770_13 : HolLoopProg 64 :=
.mark loopBody770_12

def loopBody770_14 : HolLoopProg 64 :=
.seq loopBody770_13 loopBody770_1

def loopBody770_15 : HolLoopProg 64 :=
.mark loopBody770_14

def loopBody770_16 : HolLoopProg 64 :=
.seq loopBody770_9 loopBody770_15

def loopBody770_17 : HolLoopProg 64 :=
.mark loopBody770_16

def loopBody770_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody770_19 : HolLoopProg 64 :=
.mark loopBody770_18

def loopBody770_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody770_21 : HolLoopProg 64 :=
.mark loopBody770_20

def loopBody770_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody770_23 : HolLoopProg 64 :=
.mark loopBody770_22

def loopBody770_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody770_25 : HolLoopProg 64 :=
.mark loopBody770_24

def loopBody770_26 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 158) ([6, 7, 8]) (some (6, loopBody770_25, loopBody770_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody770_27 : HolLoopProg 64 :=
.mark loopBody770_26

def loopBody770_28 : HolLoopProg 64 :=
.seq loopBody770_27 loopBody770_1

def loopBody770_29 : HolLoopProg 64 :=
.mark loopBody770_28

def loopBody770_30 : HolLoopProg 64 :=
.seq loopBody770_23 loopBody770_29

def loopBody770_31 : HolLoopProg 64 :=
.mark loopBody770_30

def loopBody770_32 : HolLoopProg 64 :=
.seq loopBody770_21 loopBody770_31

def loopBody770_33 : HolLoopProg 64 :=
.mark loopBody770_32

def loopBody770_34 : HolLoopProg 64 :=
.seq loopBody770_19 loopBody770_33

def loopBody770_35 : HolLoopProg 64 :=
.mark loopBody770_34

def loopBody770_36 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_35

def loopBody770_37 : HolLoopProg 64 :=
.mark loopBody770_36

def loopBody770_38 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_37

def loopBody770_39 : HolLoopProg 64 :=
.mark loopBody770_38

def loopBody770_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody770_41 : HolLoopProg 64 :=
.mark loopBody770_40

def loopBody770_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody770_43 : HolLoopProg 64 :=
.mark loopBody770_42

def loopBody770_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 6#64)

def loopBody770_45 : HolLoopProg 64 :=
.mark loopBody770_44

def loopBody770_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody770_47 : HolLoopProg 64 :=
.mark loopBody770_46

def loopBody770_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody770_49 : HolLoopProg 64 :=
.mark loopBody770_48

def loopBody770_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 7 (Flapjack.RegImm.reg 8) loopBody770_47 loopBody770_49 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody770_51 : HolLoopProg 64 :=
.mark loopBody770_50

def loopBody770_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody770_53 : HolLoopProg 64 :=
.mark loopBody770_52

def loopBody770_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 5])

def loopBody770_55 : HolLoopProg 64 :=
.mark loopBody770_54

def loopBody770_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 6 6

def loopBody770_57 : HolLoopProg 64 :=
.mark loopBody770_56

def loopBody770_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody770_59 : HolLoopProg 64 :=
.mark loopBody770_58

def loopBody770_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 7 7

def loopBody770_61 : HolLoopProg 64 :=
.mark loopBody770_60

def loopBody770_62 : HolLoopProg 64 :=
.seq loopBody770_61 loopBody770_1

def loopBody770_63 : HolLoopProg 64 :=
.mark loopBody770_62

def loopBody770_64 : HolLoopProg 64 :=
.seq loopBody770_59 loopBody770_63

def loopBody770_65 : HolLoopProg 64 :=
.mark loopBody770_64

def loopBody770_66 : HolLoopProg 64 :=
.seq loopBody770_57 loopBody770_65

def loopBody770_67 : HolLoopProg 64 :=
.mark loopBody770_66

def loopBody770_68 : HolLoopProg 64 :=
.seq loopBody770_55 loopBody770_67

def loopBody770_69 : HolLoopProg 64 :=
.mark loopBody770_68

def loopBody770_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.op Flapjack.BinOp.or
        [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 6) (Flapjack.HolLoopExp.const 8#64),
          Flapjack.HolLoopExp.var 7],
      Flapjack.HolLoopExp.const 2047#64])

def loopBody770_71 : HolLoopProg 64 :=
.mark loopBody770_70

def loopBody770_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 2047#64, Flapjack.HolLoopExp.var 8])

def loopBody770_73 : HolLoopProg 64 :=
.mark loopBody770_72

def loopBody770_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 9) (Flapjack.HolLoopExp.const 3#64))

def loopBody770_75 : HolLoopProg 64 :=
.mark loopBody770_74

def loopBody770_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.const 1#64)
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
      [Flapjack.HolLoopExp.const 7#64,
        Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 7#64]]))

def loopBody770_77 : HolLoopProg 64 :=
.mark loopBody770_76

def loopBody770_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 10])

def loopBody770_79 : HolLoopProg 64 :=
.mark loopBody770_78

def loopBody770_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 12 12

def loopBody770_81 : HolLoopProg 64 :=
.mark loopBody770_80

def loopBody770_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 10])

def loopBody770_83 : HolLoopProg 64 :=
.mark loopBody770_82

def loopBody770_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or [Flapjack.HolLoopExp.var 12, Flapjack.HolLoopExp.var 11])

def loopBody770_85 : HolLoopProg 64 :=
.mark loopBody770_84

def loopBody770_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 13 14

def loopBody770_87 : HolLoopProg 64 :=
.mark loopBody770_86

def loopBody770_88 : HolLoopProg 64 :=
.seq loopBody770_87 loopBody770_1

def loopBody770_89 : HolLoopProg 64 :=
.mark loopBody770_88

def loopBody770_90 : HolLoopProg 64 :=
.seq loopBody770_85 loopBody770_89

def loopBody770_91 : HolLoopProg 64 :=
.mark loopBody770_90

def loopBody770_92 : HolLoopProg 64 :=
.seq loopBody770_83 loopBody770_91

def loopBody770_93 : HolLoopProg 64 :=
.mark loopBody770_92

def loopBody770_94 : HolLoopProg 64 :=
.seq loopBody770_81 loopBody770_93

def loopBody770_95 : HolLoopProg 64 :=
.mark loopBody770_94

def loopBody770_96 : HolLoopProg 64 :=
.seq loopBody770_79 loopBody770_95

def loopBody770_97 : HolLoopProg 64 :=
.mark loopBody770_96

def loopBody770_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 2#64])

def loopBody770_99 : HolLoopProg 64 :=
.mark loopBody770_98

def loopBody770_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 12)

def loopBody770_101 : HolLoopProg 64 :=
.mark loopBody770_100

def loopBody770_102 : HolLoopProg 64 :=
.seq loopBody770_101 loopBody770_1

def loopBody770_103 : HolLoopProg 64 :=
.mark loopBody770_102

def loopBody770_104 : HolLoopProg 64 :=
.seq loopBody770_103 loopBody770_1

def loopBody770_105 : HolLoopProg 64 :=
.mark loopBody770_104

def loopBody770_106 : HolLoopProg 64 :=
.seq loopBody770_99 loopBody770_105

def loopBody770_107 : HolLoopProg 64 :=
.mark loopBody770_106

def loopBody770_108 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_107

def loopBody770_109 : HolLoopProg 64 :=
.mark loopBody770_108

def loopBody770_110 : HolLoopProg 64 :=
.seq loopBody770_97 loopBody770_109

def loopBody770_111 : HolLoopProg 64 :=
.mark loopBody770_110

def loopBody770_112 : HolLoopProg 64 :=
.seq loopBody770_77 loopBody770_111

def loopBody770_113 : HolLoopProg 64 :=
.mark loopBody770_112

def loopBody770_114 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_113

def loopBody770_115 : HolLoopProg 64 :=
.mark loopBody770_114

def loopBody770_116 : HolLoopProg 64 :=
.seq loopBody770_75 loopBody770_115

def loopBody770_117 : HolLoopProg 64 :=
.mark loopBody770_116

def loopBody770_118 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_117

def loopBody770_119 : HolLoopProg 64 :=
.mark loopBody770_118

def loopBody770_120 : HolLoopProg 64 :=
.seq loopBody770_73 loopBody770_119

def loopBody770_121 : HolLoopProg 64 :=
.mark loopBody770_120

def loopBody770_122 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_121

def loopBody770_123 : HolLoopProg 64 :=
.mark loopBody770_122

def loopBody770_124 : HolLoopProg 64 :=
.seq loopBody770_71 loopBody770_123

def loopBody770_125 : HolLoopProg 64 :=
.mark loopBody770_124

def loopBody770_126 : HolLoopProg 64 :=
.seq loopBody770_69 loopBody770_125

def loopBody770_127 : HolLoopProg 64 :=
.mark loopBody770_126

def loopBody770_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody770_129 : HolLoopProg 64 :=
.mark loopBody770_128

def loopBody770_130 : HolLoopProg 64 :=
.seq loopBody770_127 loopBody770_129

def loopBody770_131 : HolLoopProg 64 :=
.mark loopBody770_130

def loopBody770_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody770_133 : HolLoopProg 64 :=
.mark loopBody770_132

def loopBody770_134 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody770_131 loopBody770_133 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody770_135 : HolLoopProg 64 :=
.mark loopBody770_134

def loopBody770_136 : HolLoopProg 64 :=
.seq loopBody770_135 loopBody770_1

def loopBody770_137 : HolLoopProg 64 :=
.mark loopBody770_136

def loopBody770_138 : HolLoopProg 64 :=
.seq loopBody770_53 loopBody770_137

def loopBody770_139 : HolLoopProg 64 :=
.mark loopBody770_138

def loopBody770_140 : HolLoopProg 64 :=
.seq loopBody770_51 loopBody770_139

def loopBody770_141 : HolLoopProg 64 :=
.mark loopBody770_140

def loopBody770_142 : HolLoopProg 64 :=
.seq loopBody770_45 loopBody770_141

def loopBody770_143 : HolLoopProg 64 :=
.mark loopBody770_142

def loopBody770_144 : HolLoopProg 64 :=
.seq loopBody770_43 loopBody770_143

def loopBody770_145 : HolLoopProg 64 :=
.mark loopBody770_144

def loopBody770_146 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody770_145 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody770_147 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody770_148 : HolLoopProg 64 :=
.mark loopBody770_147

def loopBody770_149 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody770_150 : HolLoopProg 64 :=
.mark loopBody770_149

def loopBody770_151 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 70) ([7]) (some (7, loopBody770_150, loopBody770_1, (Flapjack.Spt.ln)))

def loopBody770_152 : HolLoopProg 64 :=
.mark loopBody770_151

def loopBody770_153 : HolLoopProg 64 :=
.seq loopBody770_152 loopBody770_1

def loopBody770_154 : HolLoopProg 64 :=
.mark loopBody770_153

def loopBody770_155 : HolLoopProg 64 :=
.seq loopBody770_148 loopBody770_154

def loopBody770_156 : HolLoopProg 64 :=
.mark loopBody770_155

def loopBody770_157 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_156

def loopBody770_158 : HolLoopProg 64 :=
.mark loopBody770_157

def loopBody770_159 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_158

def loopBody770_160 : HolLoopProg 64 :=
.mark loopBody770_159

def loopBody770_161 : HolLoopProg 64 :=
.seq loopBody770_146 loopBody770_160

def loopBody770_162 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody770_163 : HolLoopProg 64 :=
.mark loopBody770_162

def loopBody770_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody770_165 : HolLoopProg 64 :=
.mark loopBody770_164

def loopBody770_166 : HolLoopProg 64 :=
.seq loopBody770_165 loopBody770_1

def loopBody770_167 : HolLoopProg 64 :=
.mark loopBody770_166

def loopBody770_168 : HolLoopProg 64 :=
.seq loopBody770_163 loopBody770_167

def loopBody770_169 : HolLoopProg 64 :=
.mark loopBody770_168

def loopBody770_170 : HolLoopProg 64 :=
.seq loopBody770_161 loopBody770_169

def loopBody770_171 : HolLoopProg 64 :=
.seq loopBody770_41 loopBody770_170

def loopBody770_172 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_171

def loopBody770_173 : HolLoopProg 64 :=
.seq loopBody770_39 loopBody770_172

def loopBody770_174 : HolLoopProg 64 :=
.seq loopBody770_17 loopBody770_173

def loopBody770_175 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_174

def loopBody770_176 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_175

def loopBody770_177 : HolLoopProg 64 :=
.seq loopBody770_7 loopBody770_176

def loopBody770_178 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_177

def loopBody770_179 : HolLoopProg 64 :=
.seq loopBody770_1 loopBody770_178

def output770 : Nat × List Nat × HolLoopProg 64 :=
  (834, [0, 1, 2], loopBody770_179)
end InitECandidate.Proofs.FrontendStages.Loop
