import InitECandidate.Proofs.FrontendStages.Loop.Translate204
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody220_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody220_1 : HolLoopProg 64 :=
.mark loopBody220_0

def loopBody220_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody220_3 : HolLoopProg 64 :=
.mark loopBody220_2

def loopBody220_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody220_5 : HolLoopProg 64 :=
.mark loopBody220_4

def loopBody220_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 4#64])

def loopBody220_7 : HolLoopProg 64 :=
.mark loopBody220_6

def loopBody220_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody220_9 : HolLoopProg 64 :=
.mark loopBody220_8

def loopBody220_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody220_11 : HolLoopProg 64 :=
.mark loopBody220_10

def loopBody220_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 5 (Flapjack.RegImm.reg 6) loopBody220_9 loopBody220_11 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody220_13 : HolLoopProg 64 :=
.mark loopBody220_12

def loopBody220_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody220_15 : HolLoopProg 64 :=
.mark loopBody220_14

def loopBody220_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 3])

def loopBody220_17 : HolLoopProg 64 :=
.mark loopBody220_16

def loopBody220_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 4 4

def loopBody220_19 : HolLoopProg 64 :=
.mark loopBody220_18

def loopBody220_20 : HolLoopProg 64 :=
.seq loopBody220_19 loopBody220_1

def loopBody220_21 : HolLoopProg 64 :=
.mark loopBody220_20

def loopBody220_22 : HolLoopProg 64 :=
.seq loopBody220_17 loopBody220_21

def loopBody220_23 : HolLoopProg 64 :=
.mark loopBody220_22

def loopBody220_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody220_25 : HolLoopProg 64 :=
.mark loopBody220_24

def loopBody220_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64)])

def loopBody220_27 : HolLoopProg 64 :=
.mark loopBody220_26

def loopBody220_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 4#64))

def loopBody220_29 : HolLoopProg 64 :=
.mark loopBody220_28

def loopBody220_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 6 7

def loopBody220_31 : HolLoopProg 64 :=
.mark loopBody220_30

def loopBody220_32 : HolLoopProg 64 :=
.seq loopBody220_31 loopBody220_1

def loopBody220_33 : HolLoopProg 64 :=
.mark loopBody220_32

def loopBody220_34 : HolLoopProg 64 :=
.seq loopBody220_29 loopBody220_33

def loopBody220_35 : HolLoopProg 64 :=
.mark loopBody220_34

def loopBody220_36 : HolLoopProg 64 :=
.seq loopBody220_27 loopBody220_35

def loopBody220_37 : HolLoopProg 64 :=
.mark loopBody220_36

def loopBody220_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 1#64])

def loopBody220_39 : HolLoopProg 64 :=
.mark loopBody220_38

def loopBody220_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 15#64])

def loopBody220_41 : HolLoopProg 64 :=
.mark loopBody220_40

def loopBody220_42 : HolLoopProg 64 :=
.seq loopBody220_41 loopBody220_33

def loopBody220_43 : HolLoopProg 64 :=
.mark loopBody220_42

def loopBody220_44 : HolLoopProg 64 :=
.seq loopBody220_39 loopBody220_43

def loopBody220_45 : HolLoopProg 64 :=
.mark loopBody220_44

def loopBody220_46 : HolLoopProg 64 :=
.seq loopBody220_37 loopBody220_45

def loopBody220_47 : HolLoopProg 64 :=
.mark loopBody220_46

def loopBody220_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody220_49 : HolLoopProg 64 :=
.mark loopBody220_48

def loopBody220_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 6 6

def loopBody220_51 : HolLoopProg 64 :=
.mark loopBody220_50

def loopBody220_52 : HolLoopProg 64 :=
.seq loopBody220_51 loopBody220_1

def loopBody220_53 : HolLoopProg 64 :=
.mark loopBody220_52

def loopBody220_54 : HolLoopProg 64 :=
.seq loopBody220_49 loopBody220_53

def loopBody220_55 : HolLoopProg 64 :=
.mark loopBody220_54

def loopBody220_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody220_57 : HolLoopProg 64 :=
.mark loopBody220_56

def loopBody220_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 2#64])

def loopBody220_59 : HolLoopProg 64 :=
.mark loopBody220_58

def loopBody220_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 4#64))

def loopBody220_61 : HolLoopProg 64 :=
.mark loopBody220_60

def loopBody220_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 8 9

def loopBody220_63 : HolLoopProg 64 :=
.mark loopBody220_62

def loopBody220_64 : HolLoopProg 64 :=
.seq loopBody220_63 loopBody220_1

def loopBody220_65 : HolLoopProg 64 :=
.mark loopBody220_64

def loopBody220_66 : HolLoopProg 64 :=
.seq loopBody220_61 loopBody220_65

def loopBody220_67 : HolLoopProg 64 :=
.mark loopBody220_66

def loopBody220_68 : HolLoopProg 64 :=
.seq loopBody220_59 loopBody220_67

def loopBody220_69 : HolLoopProg 64 :=
.mark loopBody220_68

def loopBody220_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 3#64])

def loopBody220_71 : HolLoopProg 64 :=
.mark loopBody220_70

def loopBody220_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 15#64])

def loopBody220_73 : HolLoopProg 64 :=
.mark loopBody220_72

def loopBody220_74 : HolLoopProg 64 :=
.seq loopBody220_73 loopBody220_65

def loopBody220_75 : HolLoopProg 64 :=
.mark loopBody220_74

def loopBody220_76 : HolLoopProg 64 :=
.seq loopBody220_71 loopBody220_75

def loopBody220_77 : HolLoopProg 64 :=
.mark loopBody220_76

def loopBody220_78 : HolLoopProg 64 :=
.seq loopBody220_69 loopBody220_77

def loopBody220_79 : HolLoopProg 64 :=
.mark loopBody220_78

def loopBody220_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 2#64])

def loopBody220_81 : HolLoopProg 64 :=
.mark loopBody220_80

def loopBody220_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 8 8

def loopBody220_83 : HolLoopProg 64 :=
.mark loopBody220_82

def loopBody220_84 : HolLoopProg 64 :=
.seq loopBody220_83 loopBody220_1

def loopBody220_85 : HolLoopProg 64 :=
.mark loopBody220_84

def loopBody220_86 : HolLoopProg 64 :=
.seq loopBody220_81 loopBody220_85

def loopBody220_87 : HolLoopProg 64 :=
.mark loopBody220_86

def loopBody220_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 8)

def loopBody220_89 : HolLoopProg 64 :=
.mark loopBody220_88

def loopBody220_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 4#64])

def loopBody220_91 : HolLoopProg 64 :=
.mark loopBody220_90

def loopBody220_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 9) (Flapjack.HolLoopExp.const 4#64))

def loopBody220_93 : HolLoopProg 64 :=
.mark loopBody220_92

def loopBody220_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 10 11

def loopBody220_95 : HolLoopProg 64 :=
.mark loopBody220_94

def loopBody220_96 : HolLoopProg 64 :=
.seq loopBody220_95 loopBody220_1

def loopBody220_97 : HolLoopProg 64 :=
.mark loopBody220_96

def loopBody220_98 : HolLoopProg 64 :=
.seq loopBody220_93 loopBody220_97

def loopBody220_99 : HolLoopProg 64 :=
.mark loopBody220_98

def loopBody220_100 : HolLoopProg 64 :=
.seq loopBody220_91 loopBody220_99

def loopBody220_101 : HolLoopProg 64 :=
.mark loopBody220_100

def loopBody220_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 5#64])

def loopBody220_103 : HolLoopProg 64 :=
.mark loopBody220_102

def loopBody220_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.const 15#64])

def loopBody220_105 : HolLoopProg 64 :=
.mark loopBody220_104

def loopBody220_106 : HolLoopProg 64 :=
.seq loopBody220_105 loopBody220_97

def loopBody220_107 : HolLoopProg 64 :=
.mark loopBody220_106

def loopBody220_108 : HolLoopProg 64 :=
.seq loopBody220_103 loopBody220_107

def loopBody220_109 : HolLoopProg 64 :=
.mark loopBody220_108

def loopBody220_110 : HolLoopProg 64 :=
.seq loopBody220_101 loopBody220_109

def loopBody220_111 : HolLoopProg 64 :=
.mark loopBody220_110

def loopBody220_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 3#64])

def loopBody220_113 : HolLoopProg 64 :=
.mark loopBody220_112

def loopBody220_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 10 10

def loopBody220_115 : HolLoopProg 64 :=
.mark loopBody220_114

def loopBody220_116 : HolLoopProg 64 :=
.seq loopBody220_115 loopBody220_1

def loopBody220_117 : HolLoopProg 64 :=
.mark loopBody220_116

def loopBody220_118 : HolLoopProg 64 :=
.seq loopBody220_113 loopBody220_117

def loopBody220_119 : HolLoopProg 64 :=
.mark loopBody220_118

def loopBody220_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 10)

def loopBody220_121 : HolLoopProg 64 :=
.mark loopBody220_120

def loopBody220_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 6#64])

def loopBody220_123 : HolLoopProg 64 :=
.mark loopBody220_122

def loopBody220_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 11) (Flapjack.HolLoopExp.const 4#64))

def loopBody220_125 : HolLoopProg 64 :=
.mark loopBody220_124

def loopBody220_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 12 13

def loopBody220_127 : HolLoopProg 64 :=
.mark loopBody220_126

def loopBody220_128 : HolLoopProg 64 :=
.seq loopBody220_127 loopBody220_1

def loopBody220_129 : HolLoopProg 64 :=
.mark loopBody220_128

def loopBody220_130 : HolLoopProg 64 :=
.seq loopBody220_125 loopBody220_129

def loopBody220_131 : HolLoopProg 64 :=
.mark loopBody220_130

def loopBody220_132 : HolLoopProg 64 :=
.seq loopBody220_123 loopBody220_131

def loopBody220_133 : HolLoopProg 64 :=
.mark loopBody220_132

def loopBody220_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 7#64])

def loopBody220_135 : HolLoopProg 64 :=
.mark loopBody220_134

def loopBody220_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 11, Flapjack.HolLoopExp.const 15#64])

def loopBody220_137 : HolLoopProg 64 :=
.mark loopBody220_136

def loopBody220_138 : HolLoopProg 64 :=
.seq loopBody220_137 loopBody220_129

def loopBody220_139 : HolLoopProg 64 :=
.mark loopBody220_138

def loopBody220_140 : HolLoopProg 64 :=
.seq loopBody220_135 loopBody220_139

def loopBody220_141 : HolLoopProg 64 :=
.mark loopBody220_140

def loopBody220_142 : HolLoopProg 64 :=
.seq loopBody220_133 loopBody220_141

def loopBody220_143 : HolLoopProg 64 :=
.mark loopBody220_142

def loopBody220_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 4#64])

def loopBody220_145 : HolLoopProg 64 :=
.mark loopBody220_144

def loopBody220_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 12)

def loopBody220_147 : HolLoopProg 64 :=
.mark loopBody220_146

def loopBody220_148 : HolLoopProg 64 :=
.seq loopBody220_147 loopBody220_1

def loopBody220_149 : HolLoopProg 64 :=
.mark loopBody220_148

def loopBody220_150 : HolLoopProg 64 :=
.seq loopBody220_149 loopBody220_1

def loopBody220_151 : HolLoopProg 64 :=
.mark loopBody220_150

def loopBody220_152 : HolLoopProg 64 :=
.seq loopBody220_145 loopBody220_151

def loopBody220_153 : HolLoopProg 64 :=
.mark loopBody220_152

def loopBody220_154 : HolLoopProg 64 :=
.seq loopBody220_1 loopBody220_153

def loopBody220_155 : HolLoopProg 64 :=
.mark loopBody220_154

def loopBody220_156 : HolLoopProg 64 :=
.seq loopBody220_143 loopBody220_155

def loopBody220_157 : HolLoopProg 64 :=
.mark loopBody220_156

def loopBody220_158 : HolLoopProg 64 :=
.seq loopBody220_121 loopBody220_157

def loopBody220_159 : HolLoopProg 64 :=
.mark loopBody220_158

def loopBody220_160 : HolLoopProg 64 :=
.seq loopBody220_119 loopBody220_159

def loopBody220_161 : HolLoopProg 64 :=
.mark loopBody220_160

def loopBody220_162 : HolLoopProg 64 :=
.seq loopBody220_111 loopBody220_161

def loopBody220_163 : HolLoopProg 64 :=
.mark loopBody220_162

def loopBody220_164 : HolLoopProg 64 :=
.seq loopBody220_89 loopBody220_163

def loopBody220_165 : HolLoopProg 64 :=
.mark loopBody220_164

def loopBody220_166 : HolLoopProg 64 :=
.seq loopBody220_87 loopBody220_165

def loopBody220_167 : HolLoopProg 64 :=
.mark loopBody220_166

def loopBody220_168 : HolLoopProg 64 :=
.seq loopBody220_79 loopBody220_167

def loopBody220_169 : HolLoopProg 64 :=
.mark loopBody220_168

def loopBody220_170 : HolLoopProg 64 :=
.seq loopBody220_57 loopBody220_169

def loopBody220_171 : HolLoopProg 64 :=
.mark loopBody220_170

def loopBody220_172 : HolLoopProg 64 :=
.seq loopBody220_55 loopBody220_171

def loopBody220_173 : HolLoopProg 64 :=
.mark loopBody220_172

def loopBody220_174 : HolLoopProg 64 :=
.seq loopBody220_47 loopBody220_173

def loopBody220_175 : HolLoopProg 64 :=
.mark loopBody220_174

def loopBody220_176 : HolLoopProg 64 :=
.seq loopBody220_25 loopBody220_175

def loopBody220_177 : HolLoopProg 64 :=
.mark loopBody220_176

def loopBody220_178 : HolLoopProg 64 :=
.seq loopBody220_23 loopBody220_177

def loopBody220_179 : HolLoopProg 64 :=
.mark loopBody220_178

def loopBody220_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody220_181 : HolLoopProg 64 :=
.mark loopBody220_180

def loopBody220_182 : HolLoopProg 64 :=
.seq loopBody220_179 loopBody220_181

def loopBody220_183 : HolLoopProg 64 :=
.mark loopBody220_182

def loopBody220_184 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody220_185 : HolLoopProg 64 :=
.mark loopBody220_184

def loopBody220_186 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody220_183 loopBody220_185 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody220_187 : HolLoopProg 64 :=
.mark loopBody220_186

def loopBody220_188 : HolLoopProg 64 :=
.seq loopBody220_187 loopBody220_1

def loopBody220_189 : HolLoopProg 64 :=
.mark loopBody220_188

def loopBody220_190 : HolLoopProg 64 :=
.seq loopBody220_15 loopBody220_189

def loopBody220_191 : HolLoopProg 64 :=
.mark loopBody220_190

def loopBody220_192 : HolLoopProg 64 :=
.seq loopBody220_13 loopBody220_191

def loopBody220_193 : HolLoopProg 64 :=
.mark loopBody220_192

def loopBody220_194 : HolLoopProg 64 :=
.seq loopBody220_7 loopBody220_193

def loopBody220_195 : HolLoopProg 64 :=
.mark loopBody220_194

def loopBody220_196 : HolLoopProg 64 :=
.seq loopBody220_5 loopBody220_195

def loopBody220_197 : HolLoopProg 64 :=
.mark loopBody220_196

def loopBody220_198 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody220_197 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody220_199 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody220_200 : HolLoopProg 64 :=
.mark loopBody220_199

def loopBody220_201 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody220_202 : HolLoopProg 64 :=
.mark loopBody220_201

def loopBody220_203 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 5 (Flapjack.RegImm.reg 6) loopBody220_9 loopBody220_11 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody220_204 : HolLoopProg 64 :=
.mark loopBody220_203

def loopBody220_205 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody220_206 : HolLoopProg 64 :=
.mark loopBody220_205

def loopBody220_207 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 6)

def loopBody220_208 : HolLoopProg 64 :=
.mark loopBody220_207

def loopBody220_209 : HolLoopProg 64 :=
.seq loopBody220_208 loopBody220_1

def loopBody220_210 : HolLoopProg 64 :=
.mark loopBody220_209

def loopBody220_211 : HolLoopProg 64 :=
.seq loopBody220_210 loopBody220_1

def loopBody220_212 : HolLoopProg 64 :=
.mark loopBody220_211

def loopBody220_213 : HolLoopProg 64 :=
.seq loopBody220_206 loopBody220_212

def loopBody220_214 : HolLoopProg 64 :=
.mark loopBody220_213

def loopBody220_215 : HolLoopProg 64 :=
.seq loopBody220_1 loopBody220_214

def loopBody220_216 : HolLoopProg 64 :=
.mark loopBody220_215

def loopBody220_217 : HolLoopProg 64 :=
.seq loopBody220_47 loopBody220_216

def loopBody220_218 : HolLoopProg 64 :=
.mark loopBody220_217

def loopBody220_219 : HolLoopProg 64 :=
.seq loopBody220_25 loopBody220_218

def loopBody220_220 : HolLoopProg 64 :=
.mark loopBody220_219

def loopBody220_221 : HolLoopProg 64 :=
.seq loopBody220_23 loopBody220_220

def loopBody220_222 : HolLoopProg 64 :=
.mark loopBody220_221

def loopBody220_223 : HolLoopProg 64 :=
.seq loopBody220_222 loopBody220_181

def loopBody220_224 : HolLoopProg 64 :=
.mark loopBody220_223

def loopBody220_225 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody220_224 loopBody220_185 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody220_226 : HolLoopProg 64 :=
.mark loopBody220_225

def loopBody220_227 : HolLoopProg 64 :=
.seq loopBody220_226 loopBody220_1

def loopBody220_228 : HolLoopProg 64 :=
.mark loopBody220_227

def loopBody220_229 : HolLoopProg 64 :=
.seq loopBody220_15 loopBody220_228

def loopBody220_230 : HolLoopProg 64 :=
.mark loopBody220_229

def loopBody220_231 : HolLoopProg 64 :=
.seq loopBody220_204 loopBody220_230

def loopBody220_232 : HolLoopProg 64 :=
.mark loopBody220_231

def loopBody220_233 : HolLoopProg 64 :=
.seq loopBody220_202 loopBody220_232

def loopBody220_234 : HolLoopProg 64 :=
.mark loopBody220_233

def loopBody220_235 : HolLoopProg 64 :=
.seq loopBody220_200 loopBody220_234

def loopBody220_236 : HolLoopProg 64 :=
.mark loopBody220_235

def loopBody220_237 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody220_236 (Flapjack.Spt.ln)

def loopBody220_238 : HolLoopProg 64 :=
.seq loopBody220_198 loopBody220_237

def loopBody220_239 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody220_240 : HolLoopProg 64 :=
.mark loopBody220_239

def loopBody220_241 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody220_242 : HolLoopProg 64 :=
.mark loopBody220_241

def loopBody220_243 : HolLoopProg 64 :=
.seq loopBody220_242 loopBody220_1

def loopBody220_244 : HolLoopProg 64 :=
.mark loopBody220_243

def loopBody220_245 : HolLoopProg 64 :=
.seq loopBody220_240 loopBody220_244

def loopBody220_246 : HolLoopProg 64 :=
.mark loopBody220_245

def loopBody220_247 : HolLoopProg 64 :=
.seq loopBody220_238 loopBody220_246

def loopBody220_248 : HolLoopProg 64 :=
.seq loopBody220_3 loopBody220_247

def loopBody220_249 : HolLoopProg 64 :=
.seq loopBody220_1 loopBody220_248

def output220 : Nat × List Nat × HolLoopProg 64 :=
  (284, [0, 1, 2], loopBody220_249)
end InitECandidate.Proofs.FrontendStages.Loop
