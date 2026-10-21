import InitECandidate.Proofs.FrontendStages.Loop.Translate205
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody221_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody221_1 : HolLoopProg 64 :=
.mark loopBody221_0

def loopBody221_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody221_3 : HolLoopProg 64 :=
.mark loopBody221_2

def loopBody221_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody221_5 : HolLoopProg 64 :=
.mark loopBody221_4

def loopBody221_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody221_7 : HolLoopProg 64 :=
.mark loopBody221_6

def loopBody221_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody221_5 loopBody221_7 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody221_9 : HolLoopProg 64 :=
.mark loopBody221_8

def loopBody221_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody221_11 : HolLoopProg 64 :=
.mark loopBody221_10

def loopBody221_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody221_13 : HolLoopProg 64 :=
.mark loopBody221_12

def loopBody221_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 5#64)

def loopBody221_15 : HolLoopProg 64 :=
.mark loopBody221_14

def loopBody221_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody221_17 : HolLoopProg 64 :=
.mark loopBody221_16

def loopBody221_18 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 282) ([3]) (some (3, loopBody221_17, loopBody221_13, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody221_19 : HolLoopProg 64 :=
.mark loopBody221_18

def loopBody221_20 : HolLoopProg 64 :=
.seq loopBody221_19 loopBody221_13

def loopBody221_21 : HolLoopProg 64 :=
.mark loopBody221_20

def loopBody221_22 : HolLoopProg 64 :=
.seq loopBody221_15 loopBody221_21

def loopBody221_23 : HolLoopProg 64 :=
.mark loopBody221_22

def loopBody221_24 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_23

def loopBody221_25 : HolLoopProg 64 :=
.mark loopBody221_24

def loopBody221_26 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_25

def loopBody221_27 : HolLoopProg 64 :=
.mark loopBody221_26

def loopBody221_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody221_27 loopBody221_13 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody221_29 : HolLoopProg 64 :=
.mark loopBody221_28

def loopBody221_30 : HolLoopProg 64 :=
.seq loopBody221_29 loopBody221_13

def loopBody221_31 : HolLoopProg 64 :=
.mark loopBody221_30

def loopBody221_32 : HolLoopProg 64 :=
.seq loopBody221_11 loopBody221_31

def loopBody221_33 : HolLoopProg 64 :=
.mark loopBody221_32

def loopBody221_34 : HolLoopProg 64 :=
.seq loopBody221_9 loopBody221_33

def loopBody221_35 : HolLoopProg 64 :=
.mark loopBody221_34

def loopBody221_36 : HolLoopProg 64 :=
.seq loopBody221_3 loopBody221_35

def loopBody221_37 : HolLoopProg 64 :=
.mark loopBody221_36

def loopBody221_38 : HolLoopProg 64 :=
.seq loopBody221_1 loopBody221_37

def loopBody221_39 : HolLoopProg 64 :=
.mark loopBody221_38

def loopBody221_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody221_41 : HolLoopProg 64 :=
.mark loopBody221_40

def loopBody221_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 2 2

def loopBody221_43 : HolLoopProg 64 :=
.mark loopBody221_42

def loopBody221_44 : HolLoopProg 64 :=
.seq loopBody221_43 loopBody221_13

def loopBody221_45 : HolLoopProg 64 :=
.mark loopBody221_44

def loopBody221_46 : HolLoopProg 64 :=
.seq loopBody221_41 loopBody221_45

def loopBody221_47 : HolLoopProg 64 :=
.mark loopBody221_46

def loopBody221_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody221_49 : HolLoopProg 64 :=
.mark loopBody221_48

def loopBody221_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 4#64))

def loopBody221_51 : HolLoopProg 64 :=
.mark loopBody221_50

def loopBody221_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 1#64])

def loopBody221_53 : HolLoopProg 64 :=
.mark loopBody221_52

def loopBody221_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody221_55 : HolLoopProg 64 :=
.mark loopBody221_54

def loopBody221_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 1#64))

def loopBody221_57 : HolLoopProg 64 :=
.mark loopBody221_56

def loopBody221_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody221_59 : HolLoopProg 64 :=
.mark loopBody221_58

def loopBody221_60 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([8]) (some (8, loopBody221_59, loopBody221_13, (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody221_61 : HolLoopProg 64 :=
.mark loopBody221_60

def loopBody221_62 : HolLoopProg 64 :=
.seq loopBody221_61 loopBody221_13

def loopBody221_63 : HolLoopProg 64 :=
.mark loopBody221_62

def loopBody221_64 : HolLoopProg 64 :=
.seq loopBody221_57 loopBody221_63

def loopBody221_65 : HolLoopProg 64 :=
.mark loopBody221_64

def loopBody221_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody221_67 : HolLoopProg 64 :=
.mark loopBody221_66

def loopBody221_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody221_69 : HolLoopProg 64 :=
.mark loopBody221_68

def loopBody221_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody221_71 : HolLoopProg 64 :=
.mark loopBody221_70

def loopBody221_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody221_73 : HolLoopProg 64 :=
.mark loopBody221_72

def loopBody221_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody221_75 : HolLoopProg 64 :=
.mark loopBody221_74

def loopBody221_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.reg 11) loopBody221_73 loopBody221_75 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody221_77 : HolLoopProg 64 :=
.mark loopBody221_76

def loopBody221_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody221_79 : HolLoopProg 64 :=
.mark loopBody221_78

def loopBody221_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody221_81 : HolLoopProg 64 :=
.mark loopBody221_80

def loopBody221_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 15#64])

def loopBody221_83 : HolLoopProg 64 :=
.mark loopBody221_82

def loopBody221_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 9 10

def loopBody221_85 : HolLoopProg 64 :=
.mark loopBody221_84

def loopBody221_86 : HolLoopProg 64 :=
.seq loopBody221_85 loopBody221_13

def loopBody221_87 : HolLoopProg 64 :=
.mark loopBody221_86

def loopBody221_88 : HolLoopProg 64 :=
.seq loopBody221_83 loopBody221_87

def loopBody221_89 : HolLoopProg 64 :=
.mark loopBody221_88

def loopBody221_90 : HolLoopProg 64 :=
.seq loopBody221_81 loopBody221_89

def loopBody221_91 : HolLoopProg 64 :=
.mark loopBody221_90

def loopBody221_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody221_93 : HolLoopProg 64 :=
.mark loopBody221_92

def loopBody221_94 : HolLoopProg 64 :=
.seq loopBody221_93 loopBody221_13

def loopBody221_95 : HolLoopProg 64 :=
.mark loopBody221_94

def loopBody221_96 : HolLoopProg 64 :=
.seq loopBody221_95 loopBody221_13

def loopBody221_97 : HolLoopProg 64 :=
.mark loopBody221_96

def loopBody221_98 : HolLoopProg 64 :=
.seq loopBody221_91 loopBody221_97

def loopBody221_99 : HolLoopProg 64 :=
.mark loopBody221_98

def loopBody221_100 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody221_99 loopBody221_13 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody221_101 : HolLoopProg 64 :=
.mark loopBody221_100

def loopBody221_102 : HolLoopProg 64 :=
.seq loopBody221_101 loopBody221_13

def loopBody221_103 : HolLoopProg 64 :=
.mark loopBody221_102

def loopBody221_104 : HolLoopProg 64 :=
.seq loopBody221_79 loopBody221_103

def loopBody221_105 : HolLoopProg 64 :=
.mark loopBody221_104

def loopBody221_106 : HolLoopProg 64 :=
.seq loopBody221_77 loopBody221_105

def loopBody221_107 : HolLoopProg 64 :=
.mark loopBody221_106

def loopBody221_108 : HolLoopProg 64 :=
.seq loopBody221_71 loopBody221_107

def loopBody221_109 : HolLoopProg 64 :=
.mark loopBody221_108

def loopBody221_110 : HolLoopProg 64 :=
.seq loopBody221_69 loopBody221_109

def loopBody221_111 : HolLoopProg 64 :=
.mark loopBody221_110

def loopBody221_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 1#64])

def loopBody221_113 : HolLoopProg 64 :=
.mark loopBody221_112

def loopBody221_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64])

def loopBody221_115 : HolLoopProg 64 :=
.mark loopBody221_114

def loopBody221_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.var 8])

def loopBody221_117 : HolLoopProg 64 :=
.mark loopBody221_116

def loopBody221_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody221_119 : HolLoopProg 64 :=
.mark loopBody221_118

def loopBody221_120 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 284) ([10, 11, 12]) (some (10, loopBody221_119, loopBody221_13, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody221_121 : HolLoopProg 64 :=
.mark loopBody221_120

def loopBody221_122 : HolLoopProg 64 :=
.seq loopBody221_121 loopBody221_13

def loopBody221_123 : HolLoopProg 64 :=
.mark loopBody221_122

def loopBody221_124 : HolLoopProg 64 :=
.seq loopBody221_117 loopBody221_123

def loopBody221_125 : HolLoopProg 64 :=
.mark loopBody221_124

def loopBody221_126 : HolLoopProg 64 :=
.seq loopBody221_115 loopBody221_125

def loopBody221_127 : HolLoopProg 64 :=
.mark loopBody221_126

def loopBody221_128 : HolLoopProg 64 :=
.seq loopBody221_113 loopBody221_127

def loopBody221_129 : HolLoopProg 64 :=
.mark loopBody221_128

def loopBody221_130 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_129

def loopBody221_131 : HolLoopProg 64 :=
.mark loopBody221_130

def loopBody221_132 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_131

def loopBody221_133 : HolLoopProg 64 :=
.mark loopBody221_132

def loopBody221_134 : HolLoopProg 64 :=
.seq loopBody221_111 loopBody221_133

def loopBody221_135 : HolLoopProg 64 :=
.mark loopBody221_134

def loopBody221_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 8,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 1#64])
        (Flapjack.HolLoopExp.const 1#64)])

def loopBody221_137 : HolLoopProg 64 :=
.mark loopBody221_136

def loopBody221_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody221_139 : HolLoopProg 64 :=
.mark loopBody221_138

def loopBody221_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9, 10, 11]

def loopBody221_141 : HolLoopProg 64 :=
.mark loopBody221_140

def loopBody221_142 : HolLoopProg 64 :=
.seq loopBody221_141 loopBody221_13

def loopBody221_143 : HolLoopProg 64 :=
.mark loopBody221_142

def loopBody221_144 : HolLoopProg 64 :=
.seq loopBody221_139 loopBody221_143

def loopBody221_145 : HolLoopProg 64 :=
.mark loopBody221_144

def loopBody221_146 : HolLoopProg 64 :=
.seq loopBody221_137 loopBody221_145

def loopBody221_147 : HolLoopProg 64 :=
.mark loopBody221_146

def loopBody221_148 : HolLoopProg 64 :=
.seq loopBody221_81 loopBody221_147

def loopBody221_149 : HolLoopProg 64 :=
.mark loopBody221_148

def loopBody221_150 : HolLoopProg 64 :=
.seq loopBody221_135 loopBody221_149

def loopBody221_151 : HolLoopProg 64 :=
.mark loopBody221_150

def loopBody221_152 : HolLoopProg 64 :=
.seq loopBody221_67 loopBody221_151

def loopBody221_153 : HolLoopProg 64 :=
.mark loopBody221_152

def loopBody221_154 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_153

def loopBody221_155 : HolLoopProg 64 :=
.mark loopBody221_154

def loopBody221_156 : HolLoopProg 64 :=
.seq loopBody221_65 loopBody221_155

def loopBody221_157 : HolLoopProg 64 :=
.mark loopBody221_156

def loopBody221_158 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_157

def loopBody221_159 : HolLoopProg 64 :=
.mark loopBody221_158

def loopBody221_160 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_159

def loopBody221_161 : HolLoopProg 64 :=
.mark loopBody221_160

def loopBody221_162 : HolLoopProg 64 :=
.seq loopBody221_55 loopBody221_161

def loopBody221_163 : HolLoopProg 64 :=
.mark loopBody221_162

def loopBody221_164 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_163

def loopBody221_165 : HolLoopProg 64 :=
.mark loopBody221_164

def loopBody221_166 : HolLoopProg 64 :=
.seq loopBody221_53 loopBody221_165

def loopBody221_167 : HolLoopProg 64 :=
.mark loopBody221_166

def loopBody221_168 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_167

def loopBody221_169 : HolLoopProg 64 :=
.mark loopBody221_168

def loopBody221_170 : HolLoopProg 64 :=
.seq loopBody221_51 loopBody221_169

def loopBody221_171 : HolLoopProg 64 :=
.mark loopBody221_170

def loopBody221_172 : HolLoopProg 64 :=
.seq loopBody221_13 loopBody221_171

def loopBody221_173 : HolLoopProg 64 :=
.mark loopBody221_172

def loopBody221_174 : HolLoopProg 64 :=
.seq loopBody221_49 loopBody221_173

def loopBody221_175 : HolLoopProg 64 :=
.mark loopBody221_174

def loopBody221_176 : HolLoopProg 64 :=
.seq loopBody221_47 loopBody221_175

def loopBody221_177 : HolLoopProg 64 :=
.mark loopBody221_176

def loopBody221_178 : HolLoopProg 64 :=
.seq loopBody221_39 loopBody221_177

def loopBody221_179 : HolLoopProg 64 :=
.mark loopBody221_178

def output221 : Nat × List Nat × HolLoopProg 64 :=
  (285, [0, 1], loopBody221_179)
end InitECandidate.Proofs.FrontendStages.Loop
