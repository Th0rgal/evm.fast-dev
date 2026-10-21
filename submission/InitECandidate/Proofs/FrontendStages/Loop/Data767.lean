import InitECandidate.Proofs.FrontendStages.Loop.Translate751
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody767_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody767_1 : HolLoopProg 64 :=
.mark loopBody767_0

def loopBody767_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 0)

def loopBody767_3 : HolLoopProg 64 :=
.mark loopBody767_2

def loopBody767_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody767_5 : HolLoopProg 64 :=
.mark loopBody767_4

def loopBody767_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody767_7 : HolLoopProg 64 :=
.mark loopBody767_6

def loopBody767_8 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))) (some 93) ([8, 9]) (some (8, loopBody767_7, loopBody767_1, (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody767_9 : HolLoopProg 64 :=
.mark loopBody767_8

def loopBody767_10 : HolLoopProg 64 :=
.seq loopBody767_9 loopBody767_1

def loopBody767_11 : HolLoopProg 64 :=
.mark loopBody767_10

def loopBody767_12 : HolLoopProg 64 :=
.seq loopBody767_5 loopBody767_11

def loopBody767_13 : HolLoopProg 64 :=
.mark loopBody767_12

def loopBody767_14 : HolLoopProg 64 :=
.seq loopBody767_3 loopBody767_13

def loopBody767_15 : HolLoopProg 64 :=
.mark loopBody767_14

def loopBody767_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 7#64])
    (Flapjack.HolLoopExp.const 3#64))

def loopBody767_17 : HolLoopProg 64 :=
.mark loopBody767_16

def loopBody767_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 16#64)

def loopBody767_19 : HolLoopProg 64 :=
.mark loopBody767_18

def loopBody767_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 32#64)

def loopBody767_21 : HolLoopProg 64 :=
.mark loopBody767_20

def loopBody767_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 7)

def loopBody767_23 : HolLoopProg 64 :=
.mark loopBody767_22

def loopBody767_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody767_25 : HolLoopProg 64 :=
.mark loopBody767_24

def loopBody767_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody767_27 : HolLoopProg 64 :=
.mark loopBody767_26

def loopBody767_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 11 (Flapjack.RegImm.reg 12) loopBody767_25 loopBody767_27 (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody767_29 : HolLoopProg 64 :=
.mark loopBody767_28

def loopBody767_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody767_31 : HolLoopProg 64 :=
.mark loopBody767_30

def loopBody767_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 8) (Flapjack.HolLoopExp.const 1#64))

def loopBody767_33 : HolLoopProg 64 :=
.mark loopBody767_32

def loopBody767_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody767_35 : HolLoopProg 64 :=
.mark loopBody767_34

def loopBody767_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 12 12 10 11)

def loopBody767_37 : HolLoopProg 64 :=
.mark loopBody767_36

def loopBody767_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 12)

def loopBody767_39 : HolLoopProg 64 :=
.mark loopBody767_38

def loopBody767_40 : HolLoopProg 64 :=
.seq loopBody767_39 loopBody767_1

def loopBody767_41 : HolLoopProg 64 :=
.mark loopBody767_40

def loopBody767_42 : HolLoopProg 64 :=
.seq loopBody767_37 loopBody767_41

def loopBody767_43 : HolLoopProg 64 :=
.mark loopBody767_42

def loopBody767_44 : HolLoopProg 64 :=
.seq loopBody767_35 loopBody767_43

def loopBody767_45 : HolLoopProg 64 :=
.mark loopBody767_44

def loopBody767_46 : HolLoopProg 64 :=
.seq loopBody767_33 loopBody767_45

def loopBody767_47 : HolLoopProg 64 :=
.mark loopBody767_46

def loopBody767_48 : HolLoopProg 64 :=
.seq loopBody767_47 loopBody767_1

def loopBody767_49 : HolLoopProg 64 :=
.mark loopBody767_48

def loopBody767_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody767_49 loopBody767_1 (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody767_51 : HolLoopProg 64 :=
.mark loopBody767_50

def loopBody767_52 : HolLoopProg 64 :=
.seq loopBody767_51 loopBody767_1

def loopBody767_53 : HolLoopProg 64 :=
.mark loopBody767_52

def loopBody767_54 : HolLoopProg 64 :=
.seq loopBody767_31 loopBody767_53

def loopBody767_55 : HolLoopProg 64 :=
.mark loopBody767_54

def loopBody767_56 : HolLoopProg 64 :=
.seq loopBody767_29 loopBody767_55

def loopBody767_57 : HolLoopProg 64 :=
.mark loopBody767_56

def loopBody767_58 : HolLoopProg 64 :=
.seq loopBody767_23 loopBody767_57

def loopBody767_59 : HolLoopProg 64 :=
.mark loopBody767_58

def loopBody767_60 : HolLoopProg 64 :=
.seq loopBody767_21 loopBody767_59

def loopBody767_61 : HolLoopProg 64 :=
.mark loopBody767_60

def loopBody767_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 3)

def loopBody767_63 : HolLoopProg 64 :=
.mark loopBody767_62

def loopBody767_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 4)

def loopBody767_65 : HolLoopProg 64 :=
.mark loopBody767_64

def loopBody767_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 5)

def loopBody767_67 : HolLoopProg 64 :=
.mark loopBody767_66

def loopBody767_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 6)

def loopBody767_69 : HolLoopProg 64 :=
.mark loopBody767_68

def loopBody767_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody767_71 : HolLoopProg 64 :=
.mark loopBody767_70

def loopBody767_72 : HolLoopProg 64 :=
.call (some
  ([10],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))) (some 138) ([11, 12, 13, 14]) (some (11, loopBody767_71, loopBody767_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))

def loopBody767_73 : HolLoopProg 64 :=
.mark loopBody767_72

def loopBody767_74 : HolLoopProg 64 :=
.seq loopBody767_73 loopBody767_1

def loopBody767_75 : HolLoopProg 64 :=
.mark loopBody767_74

def loopBody767_76 : HolLoopProg 64 :=
.seq loopBody767_69 loopBody767_75

def loopBody767_77 : HolLoopProg 64 :=
.mark loopBody767_76

def loopBody767_78 : HolLoopProg 64 :=
.seq loopBody767_67 loopBody767_77

def loopBody767_79 : HolLoopProg 64 :=
.mark loopBody767_78

def loopBody767_80 : HolLoopProg 64 :=
.seq loopBody767_65 loopBody767_79

def loopBody767_81 : HolLoopProg 64 :=
.mark loopBody767_80

def loopBody767_82 : HolLoopProg 64 :=
.seq loopBody767_63 loopBody767_81

def loopBody767_83 : HolLoopProg 64 :=
.mark loopBody767_82

def loopBody767_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody767_85 : HolLoopProg 64 :=
.mark loopBody767_84

def loopBody767_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 10)

def loopBody767_87 : HolLoopProg 64 :=
.mark loopBody767_86

def loopBody767_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody767_89 : HolLoopProg 64 :=
.mark loopBody767_88

def loopBody767_90 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.RegImm.reg 13) loopBody767_89 loopBody767_85 (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody767_91 : HolLoopProg 64 :=
.mark loopBody767_90

def loopBody767_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody767_93 : HolLoopProg 64 :=
.mark loopBody767_92

def loopBody767_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.const 1#64])

def loopBody767_95 : HolLoopProg 64 :=
.mark loopBody767_94

def loopBody767_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 11)

def loopBody767_97 : HolLoopProg 64 :=
.mark loopBody767_96

def loopBody767_98 : HolLoopProg 64 :=
.seq loopBody767_97 loopBody767_1

def loopBody767_99 : HolLoopProg 64 :=
.mark loopBody767_98

def loopBody767_100 : HolLoopProg 64 :=
.seq loopBody767_99 loopBody767_1

def loopBody767_101 : HolLoopProg 64 :=
.mark loopBody767_100

def loopBody767_102 : HolLoopProg 64 :=
.seq loopBody767_95 loopBody767_101

def loopBody767_103 : HolLoopProg 64 :=
.mark loopBody767_102

def loopBody767_104 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_103

def loopBody767_105 : HolLoopProg 64 :=
.mark loopBody767_104

def loopBody767_106 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody767_105 loopBody767_1 (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody767_107 : HolLoopProg 64 :=
.mark loopBody767_106

def loopBody767_108 : HolLoopProg 64 :=
.seq loopBody767_107 loopBody767_1

def loopBody767_109 : HolLoopProg 64 :=
.mark loopBody767_108

def loopBody767_110 : HolLoopProg 64 :=
.seq loopBody767_93 loopBody767_109

def loopBody767_111 : HolLoopProg 64 :=
.mark loopBody767_110

def loopBody767_112 : HolLoopProg 64 :=
.seq loopBody767_91 loopBody767_111

def loopBody767_113 : HolLoopProg 64 :=
.mark loopBody767_112

def loopBody767_114 : HolLoopProg 64 :=
.seq loopBody767_87 loopBody767_113

def loopBody767_115 : HolLoopProg 64 :=
.mark loopBody767_114

def loopBody767_116 : HolLoopProg 64 :=
.seq loopBody767_85 loopBody767_115

def loopBody767_117 : HolLoopProg 64 :=
.mark loopBody767_116

def loopBody767_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 32#64)

def loopBody767_119 : HolLoopProg 64 :=
.mark loopBody767_118

def loopBody767_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody767_121 : HolLoopProg 64 :=
.mark loopBody767_120

def loopBody767_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody767_123 : HolLoopProg 64 :=
.mark loopBody767_122

def loopBody767_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody767_125 : HolLoopProg 64 :=
.mark loopBody767_124

def loopBody767_126 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 13 (Flapjack.RegImm.reg 14) loopBody767_123 loopBody767_125 (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody767_127 : HolLoopProg 64 :=
.mark loopBody767_126

def loopBody767_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 13)

def loopBody767_129 : HolLoopProg 64 :=
.mark loopBody767_128

def loopBody767_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 10)

def loopBody767_131 : HolLoopProg 64 :=
.mark loopBody767_130

def loopBody767_132 : HolLoopProg 64 :=
.seq loopBody767_131 loopBody767_1

def loopBody767_133 : HolLoopProg 64 :=
.mark loopBody767_132

def loopBody767_134 : HolLoopProg 64 :=
.seq loopBody767_133 loopBody767_1

def loopBody767_135 : HolLoopProg 64 :=
.mark loopBody767_134

def loopBody767_136 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 32#64])
        (Flapjack.HolLoopExp.const 4#64),
      Flapjack.HolLoopExp.var 10])

def loopBody767_137 : HolLoopProg 64 :=
.mark loopBody767_136

def loopBody767_138 : HolLoopProg 64 :=
.seq loopBody767_137 loopBody767_1

def loopBody767_139 : HolLoopProg 64 :=
.mark loopBody767_138

def loopBody767_140 : HolLoopProg 64 :=
.seq loopBody767_139 loopBody767_1

def loopBody767_141 : HolLoopProg 64 :=
.mark loopBody767_140

def loopBody767_142 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody767_135 loopBody767_141 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody767_143 : HolLoopProg 64 :=
.mark loopBody767_142

def loopBody767_144 : HolLoopProg 64 :=
.seq loopBody767_143 loopBody767_1

def loopBody767_145 : HolLoopProg 64 :=
.mark loopBody767_144

def loopBody767_146 : HolLoopProg 64 :=
.seq loopBody767_129 loopBody767_145

def loopBody767_147 : HolLoopProg 64 :=
.mark loopBody767_146

def loopBody767_148 : HolLoopProg 64 :=
.seq loopBody767_127 loopBody767_147

def loopBody767_149 : HolLoopProg 64 :=
.mark loopBody767_148

def loopBody767_150 : HolLoopProg 64 :=
.seq loopBody767_121 loopBody767_149

def loopBody767_151 : HolLoopProg 64 :=
.mark loopBody767_150

def loopBody767_152 : HolLoopProg 64 :=
.seq loopBody767_119 loopBody767_151

def loopBody767_153 : HolLoopProg 64 :=
.mark loopBody767_152

def loopBody767_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody767_155 : HolLoopProg 64 :=
.mark loopBody767_154

def loopBody767_156 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 13 (Flapjack.RegImm.reg 14) loopBody767_123 loopBody767_125 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody767_157 : HolLoopProg 64 :=
.mark loopBody767_156

def loopBody767_158 : HolLoopProg 64 :=
.seq loopBody767_25 loopBody767_1

def loopBody767_159 : HolLoopProg 64 :=
.mark loopBody767_158

def loopBody767_160 : HolLoopProg 64 :=
.seq loopBody767_159 loopBody767_1

def loopBody767_161 : HolLoopProg 64 :=
.mark loopBody767_160

def loopBody767_162 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody767_161 loopBody767_1 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody767_163 : HolLoopProg 64 :=
.mark loopBody767_162

def loopBody767_164 : HolLoopProg 64 :=
.seq loopBody767_163 loopBody767_1

def loopBody767_165 : HolLoopProg 64 :=
.mark loopBody767_164

def loopBody767_166 : HolLoopProg 64 :=
.seq loopBody767_129 loopBody767_165

def loopBody767_167 : HolLoopProg 64 :=
.mark loopBody767_166

def loopBody767_168 : HolLoopProg 64 :=
.seq loopBody767_157 loopBody767_167

def loopBody767_169 : HolLoopProg 64 :=
.mark loopBody767_168

def loopBody767_170 : HolLoopProg 64 :=
.seq loopBody767_155 loopBody767_169

def loopBody767_171 : HolLoopProg 64 :=
.mark loopBody767_170

def loopBody767_172 : HolLoopProg 64 :=
.seq loopBody767_31 loopBody767_171

def loopBody767_173 : HolLoopProg 64 :=
.mark loopBody767_172

def loopBody767_174 : HolLoopProg 64 :=
.seq loopBody767_153 loopBody767_173

def loopBody767_175 : HolLoopProg 64 :=
.mark loopBody767_174

def loopBody767_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 9)

def loopBody767_177 : HolLoopProg 64 :=
.mark loopBody767_176

def loopBody767_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 14 14 12 13)

def loopBody767_179 : HolLoopProg 64 :=
.mark loopBody767_178

def loopBody767_180 : HolLoopProg 64 :=
.seq loopBody767_179 loopBody767_1

def loopBody767_181 : HolLoopProg 64 :=
.mark loopBody767_180

def loopBody767_182 : HolLoopProg 64 :=
.seq loopBody767_31 loopBody767_181

def loopBody767_183 : HolLoopProg 64 :=
.mark loopBody767_182

def loopBody767_184 : HolLoopProg 64 :=
.seq loopBody767_177 loopBody767_183

def loopBody767_185 : HolLoopProg 64 :=
.mark loopBody767_184

def loopBody767_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 14)

def loopBody767_187 : HolLoopProg 64 :=
.mark loopBody767_186

def loopBody767_188 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 15)

def loopBody767_189 : HolLoopProg 64 :=
.mark loopBody767_188

def loopBody767_190 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.const 500#64)

def loopBody767_191 : HolLoopProg 64 :=
.mark loopBody767_190

def loopBody767_192 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.const 1#64)

def loopBody767_193 : HolLoopProg 64 :=
.mark loopBody767_192

def loopBody767_194 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.const 0#64)

def loopBody767_195 : HolLoopProg 64 :=
.mark loopBody767_194

def loopBody767_196 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 17 (Flapjack.RegImm.reg 18) loopBody767_193 loopBody767_195 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody767_197 : HolLoopProg 64 :=
.mark loopBody767_196

def loopBody767_198 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 17)

def loopBody767_199 : HolLoopProg 64 :=
.mark loopBody767_198

def loopBody767_200 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 500#64)

def loopBody767_201 : HolLoopProg 64 :=
.mark loopBody767_200

def loopBody767_202 : HolLoopProg 64 :=
.seq loopBody767_201 loopBody767_1

def loopBody767_203 : HolLoopProg 64 :=
.mark loopBody767_202

def loopBody767_204 : HolLoopProg 64 :=
.seq loopBody767_203 loopBody767_1

def loopBody767_205 : HolLoopProg 64 :=
.mark loopBody767_204

def loopBody767_206 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 19 (Flapjack.RegImm.imm 0#64) loopBody767_205 loopBody767_1 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody767_207 : HolLoopProg 64 :=
.mark loopBody767_206

def loopBody767_208 : HolLoopProg 64 :=
.seq loopBody767_207 loopBody767_1

def loopBody767_209 : HolLoopProg 64 :=
.mark loopBody767_208

def loopBody767_210 : HolLoopProg 64 :=
.seq loopBody767_199 loopBody767_209

def loopBody767_211 : HolLoopProg 64 :=
.mark loopBody767_210

def loopBody767_212 : HolLoopProg 64 :=
.seq loopBody767_197 loopBody767_211

def loopBody767_213 : HolLoopProg 64 :=
.mark loopBody767_212

def loopBody767_214 : HolLoopProg 64 :=
.seq loopBody767_191 loopBody767_213

def loopBody767_215 : HolLoopProg 64 :=
.mark loopBody767_214

def loopBody767_216 : HolLoopProg 64 :=
.seq loopBody767_189 loopBody767_215

def loopBody767_217 : HolLoopProg 64 :=
.mark loopBody767_216

def loopBody767_218 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 15)

def loopBody767_219 : HolLoopProg 64 :=
.mark loopBody767_218

def loopBody767_220 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [16]

def loopBody767_221 : HolLoopProg 64 :=
.mark loopBody767_220

def loopBody767_222 : HolLoopProg 64 :=
.seq loopBody767_221 loopBody767_1

def loopBody767_223 : HolLoopProg 64 :=
.mark loopBody767_222

def loopBody767_224 : HolLoopProg 64 :=
.seq loopBody767_219 loopBody767_223

def loopBody767_225 : HolLoopProg 64 :=
.mark loopBody767_224

def loopBody767_226 : HolLoopProg 64 :=
.seq loopBody767_217 loopBody767_225

def loopBody767_227 : HolLoopProg 64 :=
.mark loopBody767_226

def loopBody767_228 : HolLoopProg 64 :=
.seq loopBody767_187 loopBody767_227

def loopBody767_229 : HolLoopProg 64 :=
.mark loopBody767_228

def loopBody767_230 : HolLoopProg 64 :=
.seq loopBody767_185 loopBody767_229

def loopBody767_231 : HolLoopProg 64 :=
.mark loopBody767_230

def loopBody767_232 : HolLoopProg 64 :=
.seq loopBody767_175 loopBody767_231

def loopBody767_233 : HolLoopProg 64 :=
.mark loopBody767_232

def loopBody767_234 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_233

def loopBody767_235 : HolLoopProg 64 :=
.mark loopBody767_234

def loopBody767_236 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_235

def loopBody767_237 : HolLoopProg 64 :=
.mark loopBody767_236

def loopBody767_238 : HolLoopProg 64 :=
.seq loopBody767_117 loopBody767_237

def loopBody767_239 : HolLoopProg 64 :=
.mark loopBody767_238

def loopBody767_240 : HolLoopProg 64 :=
.seq loopBody767_83 loopBody767_239

def loopBody767_241 : HolLoopProg 64 :=
.mark loopBody767_240

def loopBody767_242 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_241

def loopBody767_243 : HolLoopProg 64 :=
.mark loopBody767_242

def loopBody767_244 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_243

def loopBody767_245 : HolLoopProg 64 :=
.mark loopBody767_244

def loopBody767_246 : HolLoopProg 64 :=
.seq loopBody767_61 loopBody767_245

def loopBody767_247 : HolLoopProg 64 :=
.mark loopBody767_246

def loopBody767_248 : HolLoopProg 64 :=
.seq loopBody767_19 loopBody767_247

def loopBody767_249 : HolLoopProg 64 :=
.mark loopBody767_248

def loopBody767_250 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_249

def loopBody767_251 : HolLoopProg 64 :=
.mark loopBody767_250

def loopBody767_252 : HolLoopProg 64 :=
.seq loopBody767_17 loopBody767_251

def loopBody767_253 : HolLoopProg 64 :=
.mark loopBody767_252

def loopBody767_254 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_253

def loopBody767_255 : HolLoopProg 64 :=
.mark loopBody767_254

def loopBody767_256 : HolLoopProg 64 :=
.seq loopBody767_15 loopBody767_255

def loopBody767_257 : HolLoopProg 64 :=
.mark loopBody767_256

def loopBody767_258 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_257

def loopBody767_259 : HolLoopProg 64 :=
.mark loopBody767_258

def loopBody767_260 : HolLoopProg 64 :=
.seq loopBody767_1 loopBody767_259

def loopBody767_261 : HolLoopProg 64 :=
.mark loopBody767_260

def output767 : Nat × List Nat × HolLoopProg 64 :=
  (831, [0, 1, 2, 3, 4, 5, 6], loopBody767_261)
end InitECandidate.Proofs.FrontendStages.Loop
