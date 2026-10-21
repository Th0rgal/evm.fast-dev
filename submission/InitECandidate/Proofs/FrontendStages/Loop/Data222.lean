import InitECandidate.Proofs.FrontendStages.Loop.Translate206
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody222_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody222_1 : HolLoopProg 64 :=
.mark loopBody222_0

def loopBody222_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 1#64))

def loopBody222_3 : HolLoopProg 64 :=
.mark loopBody222_2

def loopBody222_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody222_5 : HolLoopProg 64 :=
.mark loopBody222_4

def loopBody222_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64])

def loopBody222_7 : HolLoopProg 64 :=
.mark loopBody222_6

def loopBody222_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody222_9 : HolLoopProg 64 :=
.mark loopBody222_8

def loopBody222_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody222_11 : HolLoopProg 64 :=
.mark loopBody222_10

def loopBody222_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody222_13 : HolLoopProg 64 :=
.mark loopBody222_12

def loopBody222_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody222_11 loopBody222_13 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody222_15 : HolLoopProg 64 :=
.mark loopBody222_14

def loopBody222_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody222_17 : HolLoopProg 64 :=
.mark loopBody222_16

def loopBody222_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody222_19 : HolLoopProg 64 :=
.mark loopBody222_18

def loopBody222_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64))

def loopBody222_21 : HolLoopProg 64 :=
.mark loopBody222_20

def loopBody222_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 6 7

def loopBody222_23 : HolLoopProg 64 :=
.mark loopBody222_22

def loopBody222_24 : HolLoopProg 64 :=
.seq loopBody222_23 loopBody222_1

def loopBody222_25 : HolLoopProg 64 :=
.mark loopBody222_24

def loopBody222_26 : HolLoopProg 64 :=
.seq loopBody222_21 loopBody222_25

def loopBody222_27 : HolLoopProg 64 :=
.mark loopBody222_26

def loopBody222_28 : HolLoopProg 64 :=
.seq loopBody222_19 loopBody222_27

def loopBody222_29 : HolLoopProg 64 :=
.mark loopBody222_28

def loopBody222_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody222_31 : HolLoopProg 64 :=
.mark loopBody222_30

def loopBody222_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 6 6

def loopBody222_33 : HolLoopProg 64 :=
.mark loopBody222_32

def loopBody222_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody222_35 : HolLoopProg 64 :=
.mark loopBody222_34

def loopBody222_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])
        (Flapjack.HolLoopExp.const 4#64),
      Flapjack.HolLoopExp.var 6])

def loopBody222_37 : HolLoopProg 64 :=
.mark loopBody222_36

def loopBody222_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 7 8

def loopBody222_39 : HolLoopProg 64 :=
.mark loopBody222_38

def loopBody222_40 : HolLoopProg 64 :=
.seq loopBody222_39 loopBody222_1

def loopBody222_41 : HolLoopProg 64 :=
.mark loopBody222_40

def loopBody222_42 : HolLoopProg 64 :=
.seq loopBody222_37 loopBody222_41

def loopBody222_43 : HolLoopProg 64 :=
.mark loopBody222_42

def loopBody222_44 : HolLoopProg 64 :=
.seq loopBody222_35 loopBody222_43

def loopBody222_45 : HolLoopProg 64 :=
.mark loopBody222_44

def loopBody222_46 : HolLoopProg 64 :=
.seq loopBody222_33 loopBody222_45

def loopBody222_47 : HolLoopProg 64 :=
.mark loopBody222_46

def loopBody222_48 : HolLoopProg 64 :=
.seq loopBody222_31 loopBody222_47

def loopBody222_49 : HolLoopProg 64 :=
.mark loopBody222_48

def loopBody222_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody222_51 : HolLoopProg 64 :=
.mark loopBody222_50

def loopBody222_52 : HolLoopProg 64 :=
.seq loopBody222_51 loopBody222_1

def loopBody222_53 : HolLoopProg 64 :=
.mark loopBody222_52

def loopBody222_54 : HolLoopProg 64 :=
.seq loopBody222_53 loopBody222_1

def loopBody222_55 : HolLoopProg 64 :=
.mark loopBody222_54

def loopBody222_56 : HolLoopProg 64 :=
.seq loopBody222_49 loopBody222_55

def loopBody222_57 : HolLoopProg 64 :=
.mark loopBody222_56

def loopBody222_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody222_29 loopBody222_57 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody222_59 : HolLoopProg 64 :=
.mark loopBody222_58

def loopBody222_60 : HolLoopProg 64 :=
.seq loopBody222_59 loopBody222_1

def loopBody222_61 : HolLoopProg 64 :=
.mark loopBody222_60

def loopBody222_62 : HolLoopProg 64 :=
.seq loopBody222_17 loopBody222_61

def loopBody222_63 : HolLoopProg 64 :=
.mark loopBody222_62

def loopBody222_64 : HolLoopProg 64 :=
.seq loopBody222_15 loopBody222_63

def loopBody222_65 : HolLoopProg 64 :=
.mark loopBody222_64

def loopBody222_66 : HolLoopProg 64 :=
.seq loopBody222_9 loopBody222_65

def loopBody222_67 : HolLoopProg 64 :=
.mark loopBody222_66

def loopBody222_68 : HolLoopProg 64 :=
.seq loopBody222_7 loopBody222_67

def loopBody222_69 : HolLoopProg 64 :=
.mark loopBody222_68

def loopBody222_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody222_71 : HolLoopProg 64 :=
.mark loopBody222_70

def loopBody222_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody222_73 : HolLoopProg 64 :=
.mark loopBody222_72

def loopBody222_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody222_75 : HolLoopProg 64 :=
.mark loopBody222_74

def loopBody222_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody222_77 : HolLoopProg 64 :=
.mark loopBody222_76

def loopBody222_78 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.RegImm.reg 9) loopBody222_77 loopBody222_9 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody222_79 : HolLoopProg 64 :=
.mark loopBody222_78

def loopBody222_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody222_81 : HolLoopProg 64 :=
.mark loopBody222_80

def loopBody222_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 5])

def loopBody222_83 : HolLoopProg 64 :=
.mark loopBody222_82

def loopBody222_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 7 7

def loopBody222_85 : HolLoopProg 64 :=
.mark loopBody222_84

def loopBody222_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody222_87 : HolLoopProg 64 :=
.mark loopBody222_86

def loopBody222_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 8 8

def loopBody222_89 : HolLoopProg 64 :=
.mark loopBody222_88

def loopBody222_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.var 6])

def loopBody222_91 : HolLoopProg 64 :=
.mark loopBody222_90

def loopBody222_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 4#64),
      Flapjack.HolLoopExp.var 8])

def loopBody222_93 : HolLoopProg 64 :=
.mark loopBody222_92

def loopBody222_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 9 10

def loopBody222_95 : HolLoopProg 64 :=
.mark loopBody222_94

def loopBody222_96 : HolLoopProg 64 :=
.seq loopBody222_95 loopBody222_1

def loopBody222_97 : HolLoopProg 64 :=
.mark loopBody222_96

def loopBody222_98 : HolLoopProg 64 :=
.seq loopBody222_93 loopBody222_97

def loopBody222_99 : HolLoopProg 64 :=
.mark loopBody222_98

def loopBody222_100 : HolLoopProg 64 :=
.seq loopBody222_91 loopBody222_99

def loopBody222_101 : HolLoopProg 64 :=
.mark loopBody222_100

def loopBody222_102 : HolLoopProg 64 :=
.seq loopBody222_89 loopBody222_101

def loopBody222_103 : HolLoopProg 64 :=
.mark loopBody222_102

def loopBody222_104 : HolLoopProg 64 :=
.seq loopBody222_87 loopBody222_103

def loopBody222_105 : HolLoopProg 64 :=
.mark loopBody222_104

def loopBody222_106 : HolLoopProg 64 :=
.seq loopBody222_85 loopBody222_105

def loopBody222_107 : HolLoopProg 64 :=
.mark loopBody222_106

def loopBody222_108 : HolLoopProg 64 :=
.seq loopBody222_83 loopBody222_107

def loopBody222_109 : HolLoopProg 64 :=
.mark loopBody222_108

def loopBody222_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 2#64])

def loopBody222_111 : HolLoopProg 64 :=
.mark loopBody222_110

def loopBody222_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 7)

def loopBody222_113 : HolLoopProg 64 :=
.mark loopBody222_112

def loopBody222_114 : HolLoopProg 64 :=
.seq loopBody222_113 loopBody222_1

def loopBody222_115 : HolLoopProg 64 :=
.mark loopBody222_114

def loopBody222_116 : HolLoopProg 64 :=
.seq loopBody222_115 loopBody222_1

def loopBody222_117 : HolLoopProg 64 :=
.mark loopBody222_116

def loopBody222_118 : HolLoopProg 64 :=
.seq loopBody222_111 loopBody222_117

def loopBody222_119 : HolLoopProg 64 :=
.mark loopBody222_118

def loopBody222_120 : HolLoopProg 64 :=
.seq loopBody222_1 loopBody222_119

def loopBody222_121 : HolLoopProg 64 :=
.mark loopBody222_120

def loopBody222_122 : HolLoopProg 64 :=
.seq loopBody222_109 loopBody222_121

def loopBody222_123 : HolLoopProg 64 :=
.mark loopBody222_122

def loopBody222_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 1#64])

def loopBody222_125 : HolLoopProg 64 :=
.mark loopBody222_124

def loopBody222_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 7)

def loopBody222_127 : HolLoopProg 64 :=
.mark loopBody222_126

def loopBody222_128 : HolLoopProg 64 :=
.seq loopBody222_127 loopBody222_1

def loopBody222_129 : HolLoopProg 64 :=
.mark loopBody222_128

def loopBody222_130 : HolLoopProg 64 :=
.seq loopBody222_129 loopBody222_1

def loopBody222_131 : HolLoopProg 64 :=
.mark loopBody222_130

def loopBody222_132 : HolLoopProg 64 :=
.seq loopBody222_125 loopBody222_131

def loopBody222_133 : HolLoopProg 64 :=
.mark loopBody222_132

def loopBody222_134 : HolLoopProg 64 :=
.seq loopBody222_1 loopBody222_133

def loopBody222_135 : HolLoopProg 64 :=
.mark loopBody222_134

def loopBody222_136 : HolLoopProg 64 :=
.seq loopBody222_123 loopBody222_135

def loopBody222_137 : HolLoopProg 64 :=
.mark loopBody222_136

def loopBody222_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody222_139 : HolLoopProg 64 :=
.mark loopBody222_138

def loopBody222_140 : HolLoopProg 64 :=
.seq loopBody222_137 loopBody222_139

def loopBody222_141 : HolLoopProg 64 :=
.mark loopBody222_140

def loopBody222_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody222_143 : HolLoopProg 64 :=
.mark loopBody222_142

def loopBody222_144 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody222_141 loopBody222_143 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody222_145 : HolLoopProg 64 :=
.mark loopBody222_144

def loopBody222_146 : HolLoopProg 64 :=
.seq loopBody222_145 loopBody222_1

def loopBody222_147 : HolLoopProg 64 :=
.mark loopBody222_146

def loopBody222_148 : HolLoopProg 64 :=
.seq loopBody222_81 loopBody222_147

def loopBody222_149 : HolLoopProg 64 :=
.mark loopBody222_148

def loopBody222_150 : HolLoopProg 64 :=
.seq loopBody222_79 loopBody222_149

def loopBody222_151 : HolLoopProg 64 :=
.mark loopBody222_150

def loopBody222_152 : HolLoopProg 64 :=
.seq loopBody222_75 loopBody222_151

def loopBody222_153 : HolLoopProg 64 :=
.mark loopBody222_152

def loopBody222_154 : HolLoopProg 64 :=
.seq loopBody222_73 loopBody222_153

def loopBody222_155 : HolLoopProg 64 :=
.mark loopBody222_154

def loopBody222_156 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody222_155 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)

def loopBody222_157 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody222_158 : HolLoopProg 64 :=
.mark loopBody222_157

def loopBody222_159 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody222_160 : HolLoopProg 64 :=
.mark loopBody222_159

def loopBody222_161 : HolLoopProg 64 :=
.seq loopBody222_160 loopBody222_1

def loopBody222_162 : HolLoopProg 64 :=
.mark loopBody222_161

def loopBody222_163 : HolLoopProg 64 :=
.seq loopBody222_158 loopBody222_162

def loopBody222_164 : HolLoopProg 64 :=
.mark loopBody222_163

def loopBody222_165 : HolLoopProg 64 :=
.seq loopBody222_156 loopBody222_164

def loopBody222_166 : HolLoopProg 64 :=
.seq loopBody222_71 loopBody222_165

def loopBody222_167 : HolLoopProg 64 :=
.seq loopBody222_1 loopBody222_166

def loopBody222_168 : HolLoopProg 64 :=
.seq loopBody222_69 loopBody222_167

def loopBody222_169 : HolLoopProg 64 :=
.seq loopBody222_5 loopBody222_168

def loopBody222_170 : HolLoopProg 64 :=
.seq loopBody222_1 loopBody222_169

def loopBody222_171 : HolLoopProg 64 :=
.seq loopBody222_3 loopBody222_170

def loopBody222_172 : HolLoopProg 64 :=
.seq loopBody222_1 loopBody222_171

def output222 : Nat × List Nat × HolLoopProg 64 :=
  (286, [0, 1, 2, 3], loopBody222_172)
end InitECandidate.Proofs.FrontendStages.Loop
