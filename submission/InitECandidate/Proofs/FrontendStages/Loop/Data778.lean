import InitECandidate.Proofs.FrontendStages.Loop.Translate762
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody778_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody778_1 : HolLoopProg 64 :=
.mark loopBody778_0

def loopBody778_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 80#64)

def loopBody778_3 : HolLoopProg 64 :=
.mark loopBody778_2

def loopBody778_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody778_5 : HolLoopProg 64 :=
.mark loopBody778_4

def loopBody778_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 68) ([2]) (some (2, loopBody778_5, loopBody778_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody778_7 : HolLoopProg 64 :=
.mark loopBody778_6

def loopBody778_8 : HolLoopProg 64 :=
.seq loopBody778_7 loopBody778_1

def loopBody778_9 : HolLoopProg 64 :=
.mark loopBody778_8

def loopBody778_10 : HolLoopProg 64 :=
.seq loopBody778_3 loopBody778_9

def loopBody778_11 : HolLoopProg 64 :=
.mark loopBody778_10

def loopBody778_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody778_13 : HolLoopProg 64 :=
.mark loopBody778_12

def loopBody778_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody778_15 : HolLoopProg 64 :=
.mark loopBody778_14

def loopBody778_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody778_17 : HolLoopProg 64 :=
.mark loopBody778_16

def loopBody778_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 5#64)

def loopBody778_19 : HolLoopProg 64 :=
.mark loopBody778_18

def loopBody778_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody778_21 : HolLoopProg 64 :=
.mark loopBody778_20

def loopBody778_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody778_23 : HolLoopProg 64 :=
.mark loopBody778_22

def loopBody778_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 5 (Flapjack.RegImm.reg 6) loopBody778_21 loopBody778_23 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_25 : HolLoopProg 64 :=
.mark loopBody778_24

def loopBody778_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody778_27 : HolLoopProg 64 :=
.mark loopBody778_26

def loopBody778_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody778_29 : HolLoopProg 64 :=
.mark loopBody778_28

def loopBody778_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody778_31 : HolLoopProg 64 :=
.mark loopBody778_30

def loopBody778_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 192#64)

def loopBody778_33 : HolLoopProg 64 :=
.mark loopBody778_32

def loopBody778_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody778_35 : HolLoopProg 64 :=
.mark loopBody778_34

def loopBody778_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody778_37 : HolLoopProg 64 :=
.mark loopBody778_36

def loopBody778_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody778_39 : HolLoopProg 64 :=
.mark loopBody778_38

def loopBody778_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody778_41 : HolLoopProg 64 :=
.mark loopBody778_40

def loopBody778_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.RegImm.reg 9) loopBody778_39 loopBody778_41 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_43 : HolLoopProg 64 :=
.mark loopBody778_42

def loopBody778_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody778_45 : HolLoopProg 64 :=
.mark loopBody778_44

def loopBody778_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 76#64)

def loopBody778_47 : HolLoopProg 64 :=
.mark loopBody778_46

def loopBody778_48 : HolLoopProg 64 :=
.seq loopBody778_47 loopBody778_1

def loopBody778_49 : HolLoopProg 64 :=
.mark loopBody778_48

def loopBody778_50 : HolLoopProg 64 :=
.seq loopBody778_49 loopBody778_1

def loopBody778_51 : HolLoopProg 64 :=
.mark loopBody778_50

def loopBody778_52 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody778_51 loopBody778_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_53 : HolLoopProg 64 :=
.mark loopBody778_52

def loopBody778_54 : HolLoopProg 64 :=
.seq loopBody778_53 loopBody778_1

def loopBody778_55 : HolLoopProg 64 :=
.mark loopBody778_54

def loopBody778_56 : HolLoopProg 64 :=
.seq loopBody778_45 loopBody778_55

def loopBody778_57 : HolLoopProg 64 :=
.mark loopBody778_56

def loopBody778_58 : HolLoopProg 64 :=
.seq loopBody778_43 loopBody778_57

def loopBody778_59 : HolLoopProg 64 :=
.mark loopBody778_58

def loopBody778_60 : HolLoopProg 64 :=
.seq loopBody778_37 loopBody778_59

def loopBody778_61 : HolLoopProg 64 :=
.mark loopBody778_60

def loopBody778_62 : HolLoopProg 64 :=
.seq loopBody778_35 loopBody778_61

def loopBody778_63 : HolLoopProg 64 :=
.mark loopBody778_62

def loopBody778_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 2#64)

def loopBody778_65 : HolLoopProg 64 :=
.mark loopBody778_64

def loopBody778_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 116#64)

def loopBody778_67 : HolLoopProg 64 :=
.mark loopBody778_66

def loopBody778_68 : HolLoopProg 64 :=
.seq loopBody778_67 loopBody778_1

def loopBody778_69 : HolLoopProg 64 :=
.mark loopBody778_68

def loopBody778_70 : HolLoopProg 64 :=
.seq loopBody778_69 loopBody778_1

def loopBody778_71 : HolLoopProg 64 :=
.mark loopBody778_70

def loopBody778_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody778_71 loopBody778_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_73 : HolLoopProg 64 :=
.mark loopBody778_72

def loopBody778_74 : HolLoopProg 64 :=
.seq loopBody778_73 loopBody778_1

def loopBody778_75 : HolLoopProg 64 :=
.mark loopBody778_74

def loopBody778_76 : HolLoopProg 64 :=
.seq loopBody778_45 loopBody778_75

def loopBody778_77 : HolLoopProg 64 :=
.mark loopBody778_76

def loopBody778_78 : HolLoopProg 64 :=
.seq loopBody778_43 loopBody778_77

def loopBody778_79 : HolLoopProg 64 :=
.mark loopBody778_78

def loopBody778_80 : HolLoopProg 64 :=
.seq loopBody778_65 loopBody778_79

def loopBody778_81 : HolLoopProg 64 :=
.mark loopBody778_80

def loopBody778_82 : HolLoopProg 64 :=
.seq loopBody778_35 loopBody778_81

def loopBody778_83 : HolLoopProg 64 :=
.mark loopBody778_82

def loopBody778_84 : HolLoopProg 64 :=
.seq loopBody778_63 loopBody778_83

def loopBody778_85 : HolLoopProg 64 :=
.mark loopBody778_84

def loopBody778_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 3#64)

def loopBody778_87 : HolLoopProg 64 :=
.mark loopBody778_86

def loopBody778_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 184#64)

def loopBody778_89 : HolLoopProg 64 :=
.mark loopBody778_88

def loopBody778_90 : HolLoopProg 64 :=
.seq loopBody778_89 loopBody778_1

def loopBody778_91 : HolLoopProg 64 :=
.mark loopBody778_90

def loopBody778_92 : HolLoopProg 64 :=
.seq loopBody778_91 loopBody778_1

def loopBody778_93 : HolLoopProg 64 :=
.mark loopBody778_92

def loopBody778_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody778_93 loopBody778_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_95 : HolLoopProg 64 :=
.mark loopBody778_94

def loopBody778_96 : HolLoopProg 64 :=
.seq loopBody778_95 loopBody778_1

def loopBody778_97 : HolLoopProg 64 :=
.mark loopBody778_96

def loopBody778_98 : HolLoopProg 64 :=
.seq loopBody778_45 loopBody778_97

def loopBody778_99 : HolLoopProg 64 :=
.mark loopBody778_98

def loopBody778_100 : HolLoopProg 64 :=
.seq loopBody778_43 loopBody778_99

def loopBody778_101 : HolLoopProg 64 :=
.mark loopBody778_100

def loopBody778_102 : HolLoopProg 64 :=
.seq loopBody778_87 loopBody778_101

def loopBody778_103 : HolLoopProg 64 :=
.mark loopBody778_102

def loopBody778_104 : HolLoopProg 64 :=
.seq loopBody778_35 loopBody778_103

def loopBody778_105 : HolLoopProg 64 :=
.mark loopBody778_104

def loopBody778_106 : HolLoopProg 64 :=
.seq loopBody778_85 loopBody778_105

def loopBody778_107 : HolLoopProg 64 :=
.mark loopBody778_106

def loopBody778_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 4#64)

def loopBody778_109 : HolLoopProg 64 :=
.mark loopBody778_108

def loopBody778_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 68#64)

def loopBody778_111 : HolLoopProg 64 :=
.mark loopBody778_110

def loopBody778_112 : HolLoopProg 64 :=
.seq loopBody778_111 loopBody778_1

def loopBody778_113 : HolLoopProg 64 :=
.mark loopBody778_112

def loopBody778_114 : HolLoopProg 64 :=
.seq loopBody778_113 loopBody778_1

def loopBody778_115 : HolLoopProg 64 :=
.mark loopBody778_114

def loopBody778_116 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody778_115 loopBody778_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_117 : HolLoopProg 64 :=
.mark loopBody778_116

def loopBody778_118 : HolLoopProg 64 :=
.seq loopBody778_117 loopBody778_1

def loopBody778_119 : HolLoopProg 64 :=
.mark loopBody778_118

def loopBody778_120 : HolLoopProg 64 :=
.seq loopBody778_45 loopBody778_119

def loopBody778_121 : HolLoopProg 64 :=
.mark loopBody778_120

def loopBody778_122 : HolLoopProg 64 :=
.seq loopBody778_43 loopBody778_121

def loopBody778_123 : HolLoopProg 64 :=
.mark loopBody778_122

def loopBody778_124 : HolLoopProg 64 :=
.seq loopBody778_109 loopBody778_123

def loopBody778_125 : HolLoopProg 64 :=
.mark loopBody778_124

def loopBody778_126 : HolLoopProg 64 :=
.seq loopBody778_35 loopBody778_125

def loopBody778_127 : HolLoopProg 64 :=
.mark loopBody778_126

def loopBody778_128 : HolLoopProg 64 :=
.seq loopBody778_107 loopBody778_127

def loopBody778_129 : HolLoopProg 64 :=
.mark loopBody778_128

def loopBody778_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody778_131 : HolLoopProg 64 :=
.mark loopBody778_130

def loopBody778_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody778_133 : HolLoopProg 64 :=
.mark loopBody778_132

def loopBody778_134 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.reg 9) loopBody778_39 loopBody778_41 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_135 : HolLoopProg 64 :=
.mark loopBody778_134

def loopBody778_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody778_137 : HolLoopProg 64 :=
.mark loopBody778_136

def loopBody778_138 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 10 10 8 9)

def loopBody778_139 : HolLoopProg 64 :=
.mark loopBody778_138

def loopBody778_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.const 8#64])

def loopBody778_141 : HolLoopProg 64 :=
.mark loopBody778_140

def loopBody778_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody778_143 : HolLoopProg 64 :=
.mark loopBody778_142

def loopBody778_144 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([11]) (some (8, loopBody778_143, loopBody778_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody778_145 : HolLoopProg 64 :=
.mark loopBody778_144

def loopBody778_146 : HolLoopProg 64 :=
.seq loopBody778_145 loopBody778_1

def loopBody778_147 : HolLoopProg 64 :=
.mark loopBody778_146

def loopBody778_148 : HolLoopProg 64 :=
.seq loopBody778_141 loopBody778_147

def loopBody778_149 : HolLoopProg 64 :=
.mark loopBody778_148

def loopBody778_150 : HolLoopProg 64 :=
.seq loopBody778_139 loopBody778_149

def loopBody778_151 : HolLoopProg 64 :=
.mark loopBody778_150

def loopBody778_152 : HolLoopProg 64 :=
.seq loopBody778_137 loopBody778_151

def loopBody778_153 : HolLoopProg 64 :=
.mark loopBody778_152

def loopBody778_154 : HolLoopProg 64 :=
.seq loopBody778_131 loopBody778_153

def loopBody778_155 : HolLoopProg 64 :=
.mark loopBody778_154

def loopBody778_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody778_157 : HolLoopProg 64 :=
.mark loopBody778_156

def loopBody778_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody778_159 : HolLoopProg 64 :=
.mark loopBody778_158

def loopBody778_160 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 8 9

def loopBody778_161 : HolLoopProg 64 :=
.mark loopBody778_160

def loopBody778_162 : HolLoopProg 64 :=
.seq loopBody778_161 loopBody778_1

def loopBody778_163 : HolLoopProg 64 :=
.mark loopBody778_162

def loopBody778_164 : HolLoopProg 64 :=
.seq loopBody778_159 loopBody778_163

def loopBody778_165 : HolLoopProg 64 :=
.mark loopBody778_164

def loopBody778_166 : HolLoopProg 64 :=
.seq loopBody778_157 loopBody778_165

def loopBody778_167 : HolLoopProg 64 :=
.mark loopBody778_166

def loopBody778_168 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody778_169 : HolLoopProg 64 :=
.mark loopBody778_168

def loopBody778_170 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody778_171 : HolLoopProg 64 :=
.mark loopBody778_170

def loopBody778_172 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 11 11 9 10)

def loopBody778_173 : HolLoopProg 64 :=
.mark loopBody778_172

def loopBody778_174 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 1#64])

def loopBody778_175 : HolLoopProg 64 :=
.mark loopBody778_174

def loopBody778_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody778_177 : HolLoopProg 64 :=
.mark loopBody778_176

def loopBody778_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 11)

def loopBody778_179 : HolLoopProg 64 :=
.mark loopBody778_178

def loopBody778_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody778_181 : HolLoopProg 64 :=
.mark loopBody778_180

def loopBody778_182 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 77) ([12, 13, 14]) (some (9, loopBody778_181, loopBody778_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody778_183 : HolLoopProg 64 :=
.mark loopBody778_182

def loopBody778_184 : HolLoopProg 64 :=
.seq loopBody778_183 loopBody778_1

def loopBody778_185 : HolLoopProg 64 :=
.mark loopBody778_184

def loopBody778_186 : HolLoopProg 64 :=
.seq loopBody778_179 loopBody778_185

def loopBody778_187 : HolLoopProg 64 :=
.mark loopBody778_186

def loopBody778_188 : HolLoopProg 64 :=
.seq loopBody778_177 loopBody778_187

def loopBody778_189 : HolLoopProg 64 :=
.mark loopBody778_188

def loopBody778_190 : HolLoopProg 64 :=
.seq loopBody778_175 loopBody778_189

def loopBody778_191 : HolLoopProg 64 :=
.mark loopBody778_190

def loopBody778_192 : HolLoopProg 64 :=
.seq loopBody778_173 loopBody778_191

def loopBody778_193 : HolLoopProg 64 :=
.mark loopBody778_192

def loopBody778_194 : HolLoopProg 64 :=
.seq loopBody778_171 loopBody778_193

def loopBody778_195 : HolLoopProg 64 :=
.mark loopBody778_194

def loopBody778_196 : HolLoopProg 64 :=
.seq loopBody778_169 loopBody778_195

def loopBody778_197 : HolLoopProg 64 :=
.mark loopBody778_196

def loopBody778_198 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_197

def loopBody778_199 : HolLoopProg 64 :=
.mark loopBody778_198

def loopBody778_200 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_199

def loopBody778_201 : HolLoopProg 64 :=
.mark loopBody778_200

def loopBody778_202 : HolLoopProg 64 :=
.seq loopBody778_167 loopBody778_201

def loopBody778_203 : HolLoopProg 64 :=
.mark loopBody778_202

def loopBody778_204 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 1,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 4#64)])

def loopBody778_205 : HolLoopProg 64 :=
.mark loopBody778_204

def loopBody778_206 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody778_207 : HolLoopProg 64 :=
.mark loopBody778_206

def loopBody778_208 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 9)

def loopBody778_209 : HolLoopProg 64 :=
.mark loopBody778_208

def loopBody778_210 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 8) 10

def loopBody778_211 : HolLoopProg 64 :=
.mark loopBody778_210

def loopBody778_212 : HolLoopProg 64 :=
.seq loopBody778_211 loopBody778_1

def loopBody778_213 : HolLoopProg 64 :=
.mark loopBody778_212

def loopBody778_214 : HolLoopProg 64 :=
.seq loopBody778_209 loopBody778_213

def loopBody778_215 : HolLoopProg 64 :=
.mark loopBody778_214

def loopBody778_216 : HolLoopProg 64 :=
.seq loopBody778_215 loopBody778_1

def loopBody778_217 : HolLoopProg 64 :=
.mark loopBody778_216

def loopBody778_218 : HolLoopProg 64 :=
.seq loopBody778_207 loopBody778_217

def loopBody778_219 : HolLoopProg 64 :=
.mark loopBody778_218

def loopBody778_220 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_219

def loopBody778_221 : HolLoopProg 64 :=
.mark loopBody778_220

def loopBody778_222 : HolLoopProg 64 :=
.seq loopBody778_205 loopBody778_221

def loopBody778_223 : HolLoopProg 64 :=
.mark loopBody778_222

def loopBody778_224 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_223

def loopBody778_225 : HolLoopProg 64 :=
.mark loopBody778_224

def loopBody778_226 : HolLoopProg 64 :=
.seq loopBody778_203 loopBody778_225

def loopBody778_227 : HolLoopProg 64 :=
.mark loopBody778_226

def loopBody778_228 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 1,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 4#64),
      Flapjack.HolLoopExp.const 8#64])

def loopBody778_229 : HolLoopProg 64 :=
.mark loopBody778_228

def loopBody778_230 : HolLoopProg 64 :=
.seq loopBody778_173 loopBody778_1

def loopBody778_231 : HolLoopProg 64 :=
.mark loopBody778_230

def loopBody778_232 : HolLoopProg 64 :=
.seq loopBody778_171 loopBody778_231

def loopBody778_233 : HolLoopProg 64 :=
.mark loopBody778_232

def loopBody778_234 : HolLoopProg 64 :=
.seq loopBody778_169 loopBody778_233

def loopBody778_235 : HolLoopProg 64 :=
.mark loopBody778_234

def loopBody778_236 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 11, Flapjack.HolLoopExp.const 1#64])

def loopBody778_237 : HolLoopProg 64 :=
.mark loopBody778_236

def loopBody778_238 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 12)

def loopBody778_239 : HolLoopProg 64 :=
.mark loopBody778_238

def loopBody778_240 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 8) 13

def loopBody778_241 : HolLoopProg 64 :=
.mark loopBody778_240

def loopBody778_242 : HolLoopProg 64 :=
.seq loopBody778_241 loopBody778_1

def loopBody778_243 : HolLoopProg 64 :=
.mark loopBody778_242

def loopBody778_244 : HolLoopProg 64 :=
.seq loopBody778_239 loopBody778_243

def loopBody778_245 : HolLoopProg 64 :=
.mark loopBody778_244

def loopBody778_246 : HolLoopProg 64 :=
.seq loopBody778_245 loopBody778_1

def loopBody778_247 : HolLoopProg 64 :=
.mark loopBody778_246

def loopBody778_248 : HolLoopProg 64 :=
.seq loopBody778_237 loopBody778_247

def loopBody778_249 : HolLoopProg 64 :=
.mark loopBody778_248

def loopBody778_250 : HolLoopProg 64 :=
.seq loopBody778_235 loopBody778_249

def loopBody778_251 : HolLoopProg 64 :=
.mark loopBody778_250

def loopBody778_252 : HolLoopProg 64 :=
.seq loopBody778_229 loopBody778_251

def loopBody778_253 : HolLoopProg 64 :=
.mark loopBody778_252

def loopBody778_254 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_253

def loopBody778_255 : HolLoopProg 64 :=
.mark loopBody778_254

def loopBody778_256 : HolLoopProg 64 :=
.seq loopBody778_227 loopBody778_255

def loopBody778_257 : HolLoopProg 64 :=
.mark loopBody778_256

def loopBody778_258 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 1#64])

def loopBody778_259 : HolLoopProg 64 :=
.mark loopBody778_258

def loopBody778_260 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 8)

def loopBody778_261 : HolLoopProg 64 :=
.mark loopBody778_260

def loopBody778_262 : HolLoopProg 64 :=
.seq loopBody778_261 loopBody778_1

def loopBody778_263 : HolLoopProg 64 :=
.mark loopBody778_262

def loopBody778_264 : HolLoopProg 64 :=
.seq loopBody778_263 loopBody778_1

def loopBody778_265 : HolLoopProg 64 :=
.mark loopBody778_264

def loopBody778_266 : HolLoopProg 64 :=
.seq loopBody778_259 loopBody778_265

def loopBody778_267 : HolLoopProg 64 :=
.mark loopBody778_266

def loopBody778_268 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_267

def loopBody778_269 : HolLoopProg 64 :=
.mark loopBody778_268

def loopBody778_270 : HolLoopProg 64 :=
.seq loopBody778_257 loopBody778_269

def loopBody778_271 : HolLoopProg 64 :=
.mark loopBody778_270

def loopBody778_272 : HolLoopProg 64 :=
.seq loopBody778_155 loopBody778_271

def loopBody778_273 : HolLoopProg 64 :=
.mark loopBody778_272

def loopBody778_274 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_273

def loopBody778_275 : HolLoopProg 64 :=
.mark loopBody778_274

def loopBody778_276 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_275

def loopBody778_277 : HolLoopProg 64 :=
.mark loopBody778_276

def loopBody778_278 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody778_277 loopBody778_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_279 : HolLoopProg 64 :=
.mark loopBody778_278

def loopBody778_280 : HolLoopProg 64 :=
.seq loopBody778_279 loopBody778_1

def loopBody778_281 : HolLoopProg 64 :=
.mark loopBody778_280

def loopBody778_282 : HolLoopProg 64 :=
.seq loopBody778_45 loopBody778_281

def loopBody778_283 : HolLoopProg 64 :=
.mark loopBody778_282

def loopBody778_284 : HolLoopProg 64 :=
.seq loopBody778_135 loopBody778_283

def loopBody778_285 : HolLoopProg 64 :=
.mark loopBody778_284

def loopBody778_286 : HolLoopProg 64 :=
.seq loopBody778_133 loopBody778_285

def loopBody778_287 : HolLoopProg 64 :=
.mark loopBody778_286

def loopBody778_288 : HolLoopProg 64 :=
.seq loopBody778_131 loopBody778_287

def loopBody778_289 : HolLoopProg 64 :=
.mark loopBody778_288

def loopBody778_290 : HolLoopProg 64 :=
.seq loopBody778_129 loopBody778_289

def loopBody778_291 : HolLoopProg 64 :=
.mark loopBody778_290

def loopBody778_292 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody778_293 : HolLoopProg 64 :=
.mark loopBody778_292

def loopBody778_294 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 7)

def loopBody778_295 : HolLoopProg 64 :=
.mark loopBody778_294

def loopBody778_296 : HolLoopProg 64 :=
.seq loopBody778_295 loopBody778_1

def loopBody778_297 : HolLoopProg 64 :=
.mark loopBody778_296

def loopBody778_298 : HolLoopProg 64 :=
.seq loopBody778_297 loopBody778_1

def loopBody778_299 : HolLoopProg 64 :=
.mark loopBody778_298

def loopBody778_300 : HolLoopProg 64 :=
.seq loopBody778_293 loopBody778_299

def loopBody778_301 : HolLoopProg 64 :=
.mark loopBody778_300

def loopBody778_302 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_301

def loopBody778_303 : HolLoopProg 64 :=
.mark loopBody778_302

def loopBody778_304 : HolLoopProg 64 :=
.seq loopBody778_291 loopBody778_303

def loopBody778_305 : HolLoopProg 64 :=
.mark loopBody778_304

def loopBody778_306 : HolLoopProg 64 :=
.seq loopBody778_33 loopBody778_305

def loopBody778_307 : HolLoopProg 64 :=
.mark loopBody778_306

def loopBody778_308 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_307

def loopBody778_309 : HolLoopProg 64 :=
.mark loopBody778_308

def loopBody778_310 : HolLoopProg 64 :=
.seq loopBody778_31 loopBody778_309

def loopBody778_311 : HolLoopProg 64 :=
.mark loopBody778_310

def loopBody778_312 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_311

def loopBody778_313 : HolLoopProg 64 :=
.mark loopBody778_312

def loopBody778_314 : HolLoopProg 64 :=
.seq loopBody778_29 loopBody778_313

def loopBody778_315 : HolLoopProg 64 :=
.mark loopBody778_314

def loopBody778_316 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_315

def loopBody778_317 : HolLoopProg 64 :=
.mark loopBody778_316

def loopBody778_318 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody778_319 : HolLoopProg 64 :=
.mark loopBody778_318

def loopBody778_320 : HolLoopProg 64 :=
.seq loopBody778_317 loopBody778_319

def loopBody778_321 : HolLoopProg 64 :=
.mark loopBody778_320

def loopBody778_322 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody778_323 : HolLoopProg 64 :=
.mark loopBody778_322

def loopBody778_324 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody778_321 loopBody778_323 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody778_325 : HolLoopProg 64 :=
.mark loopBody778_324

def loopBody778_326 : HolLoopProg 64 :=
.seq loopBody778_325 loopBody778_1

def loopBody778_327 : HolLoopProg 64 :=
.mark loopBody778_326

def loopBody778_328 : HolLoopProg 64 :=
.seq loopBody778_27 loopBody778_327

def loopBody778_329 : HolLoopProg 64 :=
.mark loopBody778_328

def loopBody778_330 : HolLoopProg 64 :=
.seq loopBody778_25 loopBody778_329

def loopBody778_331 : HolLoopProg 64 :=
.mark loopBody778_330

def loopBody778_332 : HolLoopProg 64 :=
.seq loopBody778_19 loopBody778_331

def loopBody778_333 : HolLoopProg 64 :=
.mark loopBody778_332

def loopBody778_334 : HolLoopProg 64 :=
.seq loopBody778_17 loopBody778_333

def loopBody778_335 : HolLoopProg 64 :=
.mark loopBody778_334

def loopBody778_336 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody778_335 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody778_337 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody778_338 : HolLoopProg 64 :=
.mark loopBody778_337

def loopBody778_339 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody778_340 : HolLoopProg 64 :=
.mark loopBody778_339

def loopBody778_341 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4, 5]

def loopBody778_342 : HolLoopProg 64 :=
.mark loopBody778_341

def loopBody778_343 : HolLoopProg 64 :=
.seq loopBody778_342 loopBody778_1

def loopBody778_344 : HolLoopProg 64 :=
.mark loopBody778_343

def loopBody778_345 : HolLoopProg 64 :=
.seq loopBody778_340 loopBody778_344

def loopBody778_346 : HolLoopProg 64 :=
.mark loopBody778_345

def loopBody778_347 : HolLoopProg 64 :=
.seq loopBody778_338 loopBody778_346

def loopBody778_348 : HolLoopProg 64 :=
.mark loopBody778_347

def loopBody778_349 : HolLoopProg 64 :=
.seq loopBody778_336 loopBody778_348

def loopBody778_350 : HolLoopProg 64 :=
.seq loopBody778_15 loopBody778_349

def loopBody778_351 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_350

def loopBody778_352 : HolLoopProg 64 :=
.seq loopBody778_13 loopBody778_351

def loopBody778_353 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_352

def loopBody778_354 : HolLoopProg 64 :=
.seq loopBody778_11 loopBody778_353

def loopBody778_355 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_354

def loopBody778_356 : HolLoopProg 64 :=
.seq loopBody778_1 loopBody778_355

def output778 : Nat × List Nat × HolLoopProg 64 :=
  (842, [0], loopBody778_356)
end InitECandidate.Proofs.FrontendStages.Loop
