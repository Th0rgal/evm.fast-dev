import InitECandidate.Proofs.FrontendStages.Loop.Translate337
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody353_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody353_1 : HolLoopProg 64 :=
.mark loopBody353_0

def loopBody353_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 184#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody353_3 : HolLoopProg 64 :=
.mark loopBody353_2

def loopBody353_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody353_5 : HolLoopProg 64 :=
.mark loopBody353_4

def loopBody353_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody353_7 : HolLoopProg 64 :=
.mark loopBody353_6

def loopBody353_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody353_9 : HolLoopProg 64 :=
.mark loopBody353_8

def loopBody353_10 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 186) ([4, 5]) (some (4, loopBody353_9, loopBody353_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody353_11 : HolLoopProg 64 :=
.mark loopBody353_10

def loopBody353_12 : HolLoopProg 64 :=
.seq loopBody353_11 loopBody353_1

def loopBody353_13 : HolLoopProg 64 :=
.mark loopBody353_12

def loopBody353_14 : HolLoopProg 64 :=
.seq loopBody353_7 loopBody353_13

def loopBody353_15 : HolLoopProg 64 :=
.mark loopBody353_14

def loopBody353_16 : HolLoopProg 64 :=
.seq loopBody353_5 loopBody353_15

def loopBody353_17 : HolLoopProg 64 :=
.mark loopBody353_16

def loopBody353_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody353_19 : HolLoopProg 64 :=
.mark loopBody353_18

def loopBody353_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody353_21 : HolLoopProg 64 :=
.mark loopBody353_20

def loopBody353_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody353_23 : HolLoopProg 64 :=
.mark loopBody353_22

def loopBody353_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody353_25 : HolLoopProg 64 :=
.mark loopBody353_24

def loopBody353_26 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody353_23 loopBody353_25 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody353_27 : HolLoopProg 64 :=
.mark loopBody353_26

def loopBody353_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody353_29 : HolLoopProg 64 :=
.mark loopBody353_28

def loopBody353_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody353_31 : HolLoopProg 64 :=
.mark loopBody353_30

def loopBody353_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody353_33 : HolLoopProg 64 :=
.mark loopBody353_32

def loopBody353_34 : HolLoopProg 64 :=
.seq loopBody353_33 loopBody353_1

def loopBody353_35 : HolLoopProg 64 :=
.mark loopBody353_34

def loopBody353_36 : HolLoopProg 64 :=
.seq loopBody353_31 loopBody353_35

def loopBody353_37 : HolLoopProg 64 :=
.mark loopBody353_36

def loopBody353_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody353_37 loopBody353_1 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody353_39 : HolLoopProg 64 :=
.mark loopBody353_38

def loopBody353_40 : HolLoopProg 64 :=
.seq loopBody353_39 loopBody353_1

def loopBody353_41 : HolLoopProg 64 :=
.mark loopBody353_40

def loopBody353_42 : HolLoopProg 64 :=
.seq loopBody353_29 loopBody353_41

def loopBody353_43 : HolLoopProg 64 :=
.mark loopBody353_42

def loopBody353_44 : HolLoopProg 64 :=
.seq loopBody353_27 loopBody353_43

def loopBody353_45 : HolLoopProg 64 :=
.mark loopBody353_44

def loopBody353_46 : HolLoopProg 64 :=
.seq loopBody353_21 loopBody353_45

def loopBody353_47 : HolLoopProg 64 :=
.mark loopBody353_46

def loopBody353_48 : HolLoopProg 64 :=
.seq loopBody353_19 loopBody353_47

def loopBody353_49 : HolLoopProg 64 :=
.mark loopBody353_48

def loopBody353_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody353_51 : HolLoopProg 64 :=
.mark loopBody353_50

def loopBody353_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 24#64]))

def loopBody353_53 : HolLoopProg 64 :=
.mark loopBody353_52

def loopBody353_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody353_55 : HolLoopProg 64 :=
.mark loopBody353_54

def loopBody353_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody353_57 : HolLoopProg 64 :=
.mark loopBody353_56

def loopBody353_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody353_59 : HolLoopProg 64 :=
.mark loopBody353_58

def loopBody353_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody353_61 : HolLoopProg 64 :=
.mark loopBody353_60

def loopBody353_62 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 8 (Flapjack.RegImm.reg 9) loopBody353_59 loopBody353_61 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody353_63 : HolLoopProg 64 :=
.mark loopBody353_62

def loopBody353_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody353_65 : HolLoopProg 64 :=
.mark loopBody353_64

def loopBody353_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody353_67 : HolLoopProg 64 :=
.mark loopBody353_66

def loopBody353_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody353_69 : HolLoopProg 64 :=
.mark loopBody353_68

def loopBody353_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody353_71 : HolLoopProg 64 :=
.mark loopBody353_70

def loopBody353_72 : HolLoopProg 64 :=
.call (some
  ([7, 8, 9],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 197) ([10, 11]) (some (10, loopBody353_71, loopBody353_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody353_73 : HolLoopProg 64 :=
.mark loopBody353_72

def loopBody353_74 : HolLoopProg 64 :=
.seq loopBody353_73 loopBody353_1

def loopBody353_75 : HolLoopProg 64 :=
.mark loopBody353_74

def loopBody353_76 : HolLoopProg 64 :=
.seq loopBody353_69 loopBody353_75

def loopBody353_77 : HolLoopProg 64 :=
.mark loopBody353_76

def loopBody353_78 : HolLoopProg 64 :=
.seq loopBody353_67 loopBody353_77

def loopBody353_79 : HolLoopProg 64 :=
.mark loopBody353_78

def loopBody353_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody353_81 : HolLoopProg 64 :=
.mark loopBody353_80

def loopBody353_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody353_83 : HolLoopProg 64 :=
.mark loopBody353_82

def loopBody353_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody353_85 : HolLoopProg 64 :=
.mark loopBody353_84

def loopBody353_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody353_87 : HolLoopProg 64 :=
.mark loopBody353_86

def loopBody353_88 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.reg 12) loopBody353_85 loopBody353_87 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody353_89 : HolLoopProg 64 :=
.mark loopBody353_88

def loopBody353_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody353_91 : HolLoopProg 64 :=
.mark loopBody353_90

def loopBody353_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 0)

def loopBody353_93 : HolLoopProg 64 :=
.mark loopBody353_92

def loopBody353_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 8)

def loopBody353_95 : HolLoopProg 64 :=
.mark loopBody353_94

def loopBody353_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody353_97 : HolLoopProg 64 :=
.mark loopBody353_96

def loopBody353_98 : HolLoopProg 64 :=
.call (some
  ([10],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 388) ([11, 12]) (some (11, loopBody353_97, loopBody353_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody353_99 : HolLoopProg 64 :=
.mark loopBody353_98

def loopBody353_100 : HolLoopProg 64 :=
.seq loopBody353_99 loopBody353_1

def loopBody353_101 : HolLoopProg 64 :=
.mark loopBody353_100

def loopBody353_102 : HolLoopProg 64 :=
.seq loopBody353_95 loopBody353_101

def loopBody353_103 : HolLoopProg 64 :=
.mark loopBody353_102

def loopBody353_104 : HolLoopProg 64 :=
.seq loopBody353_93 loopBody353_103

def loopBody353_105 : HolLoopProg 64 :=
.mark loopBody353_104

def loopBody353_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 184#64]),
        Flapjack.HolLoopExp.const 24#64]))

def loopBody353_107 : HolLoopProg 64 :=
.mark loopBody353_106

def loopBody353_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 10)

def loopBody353_109 : HolLoopProg 64 :=
.mark loopBody353_108

def loopBody353_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody353_111 : HolLoopProg 64 :=
.mark loopBody353_110

def loopBody353_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody353_113 : HolLoopProg 64 :=
.mark loopBody353_112

def loopBody353_114 : HolLoopProg 64 :=
.call (some
  ([11],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 192) ([12, 13, 14]) (some (12, loopBody353_113, loopBody353_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody353_115 : HolLoopProg 64 :=
.mark loopBody353_114

def loopBody353_116 : HolLoopProg 64 :=
.seq loopBody353_115 loopBody353_1

def loopBody353_117 : HolLoopProg 64 :=
.mark loopBody353_116

def loopBody353_118 : HolLoopProg 64 :=
.seq loopBody353_111 loopBody353_117

def loopBody353_119 : HolLoopProg 64 :=
.mark loopBody353_118

def loopBody353_120 : HolLoopProg 64 :=
.seq loopBody353_109 loopBody353_119

def loopBody353_121 : HolLoopProg 64 :=
.mark loopBody353_120

def loopBody353_122 : HolLoopProg 64 :=
.seq loopBody353_107 loopBody353_121

def loopBody353_123 : HolLoopProg 64 :=
.mark loopBody353_122

def loopBody353_124 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_123

def loopBody353_125 : HolLoopProg 64 :=
.mark loopBody353_124

def loopBody353_126 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_125

def loopBody353_127 : HolLoopProg 64 :=
.mark loopBody353_126

def loopBody353_128 : HolLoopProg 64 :=
.seq loopBody353_105 loopBody353_127

def loopBody353_129 : HolLoopProg 64 :=
.mark loopBody353_128

def loopBody353_130 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_129

def loopBody353_131 : HolLoopProg 64 :=
.mark loopBody353_130

def loopBody353_132 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_131

def loopBody353_133 : HolLoopProg 64 :=
.mark loopBody353_132

def loopBody353_134 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody353_133 loopBody353_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody353_135 : HolLoopProg 64 :=
.mark loopBody353_134

def loopBody353_136 : HolLoopProg 64 :=
.seq loopBody353_135 loopBody353_1

def loopBody353_137 : HolLoopProg 64 :=
.mark loopBody353_136

def loopBody353_138 : HolLoopProg 64 :=
.seq loopBody353_91 loopBody353_137

def loopBody353_139 : HolLoopProg 64 :=
.mark loopBody353_138

def loopBody353_140 : HolLoopProg 64 :=
.seq loopBody353_89 loopBody353_139

def loopBody353_141 : HolLoopProg 64 :=
.mark loopBody353_140

def loopBody353_142 : HolLoopProg 64 :=
.seq loopBody353_83 loopBody353_141

def loopBody353_143 : HolLoopProg 64 :=
.mark loopBody353_142

def loopBody353_144 : HolLoopProg 64 :=
.seq loopBody353_81 loopBody353_143

def loopBody353_145 : HolLoopProg 64 :=
.mark loopBody353_144

def loopBody353_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 1#64])

def loopBody353_147 : HolLoopProg 64 :=
.mark loopBody353_146

def loopBody353_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 10)

def loopBody353_149 : HolLoopProg 64 :=
.mark loopBody353_148

def loopBody353_150 : HolLoopProg 64 :=
.seq loopBody353_149 loopBody353_1

def loopBody353_151 : HolLoopProg 64 :=
.mark loopBody353_150

def loopBody353_152 : HolLoopProg 64 :=
.seq loopBody353_151 loopBody353_1

def loopBody353_153 : HolLoopProg 64 :=
.mark loopBody353_152

def loopBody353_154 : HolLoopProg 64 :=
.seq loopBody353_147 loopBody353_153

def loopBody353_155 : HolLoopProg 64 :=
.mark loopBody353_154

def loopBody353_156 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_155

def loopBody353_157 : HolLoopProg 64 :=
.mark loopBody353_156

def loopBody353_158 : HolLoopProg 64 :=
.seq loopBody353_145 loopBody353_157

def loopBody353_159 : HolLoopProg 64 :=
.mark loopBody353_158

def loopBody353_160 : HolLoopProg 64 :=
.seq loopBody353_79 loopBody353_159

def loopBody353_161 : HolLoopProg 64 :=
.mark loopBody353_160

def loopBody353_162 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_161

def loopBody353_163 : HolLoopProg 64 :=
.mark loopBody353_162

def loopBody353_164 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_163

def loopBody353_165 : HolLoopProg 64 :=
.mark loopBody353_164

def loopBody353_166 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_165

def loopBody353_167 : HolLoopProg 64 :=
.mark loopBody353_166

def loopBody353_168 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_167

def loopBody353_169 : HolLoopProg 64 :=
.mark loopBody353_168

def loopBody353_170 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_169

def loopBody353_171 : HolLoopProg 64 :=
.mark loopBody353_170

def loopBody353_172 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_171

def loopBody353_173 : HolLoopProg 64 :=
.mark loopBody353_172

def loopBody353_174 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody353_175 : HolLoopProg 64 :=
.mark loopBody353_174

def loopBody353_176 : HolLoopProg 64 :=
.seq loopBody353_173 loopBody353_175

def loopBody353_177 : HolLoopProg 64 :=
.mark loopBody353_176

def loopBody353_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody353_179 : HolLoopProg 64 :=
.mark loopBody353_178

def loopBody353_180 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody353_177 loopBody353_179 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody353_181 : HolLoopProg 64 :=
.mark loopBody353_180

def loopBody353_182 : HolLoopProg 64 :=
.seq loopBody353_181 loopBody353_1

def loopBody353_183 : HolLoopProg 64 :=
.mark loopBody353_182

def loopBody353_184 : HolLoopProg 64 :=
.seq loopBody353_65 loopBody353_183

def loopBody353_185 : HolLoopProg 64 :=
.mark loopBody353_184

def loopBody353_186 : HolLoopProg 64 :=
.seq loopBody353_63 loopBody353_185

def loopBody353_187 : HolLoopProg 64 :=
.mark loopBody353_186

def loopBody353_188 : HolLoopProg 64 :=
.seq loopBody353_57 loopBody353_187

def loopBody353_189 : HolLoopProg 64 :=
.mark loopBody353_188

def loopBody353_190 : HolLoopProg 64 :=
.seq loopBody353_55 loopBody353_189

def loopBody353_191 : HolLoopProg 64 :=
.mark loopBody353_190

def loopBody353_192 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody353_191 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody353_193 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody353_194 : HolLoopProg 64 :=
.mark loopBody353_193

def loopBody353_195 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody353_196 : HolLoopProg 64 :=
.mark loopBody353_195

def loopBody353_197 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody353_198 : HolLoopProg 64 :=
.mark loopBody353_197

def loopBody353_199 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.ln)) (some 385) ([8, 9]) (some (8, loopBody353_198, loopBody353_1, (Flapjack.Spt.ln)))

def loopBody353_200 : HolLoopProg 64 :=
.mark loopBody353_199

def loopBody353_201 : HolLoopProg 64 :=
.seq loopBody353_200 loopBody353_1

def loopBody353_202 : HolLoopProg 64 :=
.mark loopBody353_201

def loopBody353_203 : HolLoopProg 64 :=
.seq loopBody353_196 loopBody353_202

def loopBody353_204 : HolLoopProg 64 :=
.mark loopBody353_203

def loopBody353_205 : HolLoopProg 64 :=
.seq loopBody353_194 loopBody353_204

def loopBody353_206 : HolLoopProg 64 :=
.mark loopBody353_205

def loopBody353_207 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_206

def loopBody353_208 : HolLoopProg 64 :=
.mark loopBody353_207

def loopBody353_209 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_208

def loopBody353_210 : HolLoopProg 64 :=
.mark loopBody353_209

def loopBody353_211 : HolLoopProg 64 :=
.seq loopBody353_192 loopBody353_210

def loopBody353_212 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody353_213 : HolLoopProg 64 :=
.mark loopBody353_212

def loopBody353_214 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody353_215 : HolLoopProg 64 :=
.mark loopBody353_214

def loopBody353_216 : HolLoopProg 64 :=
.seq loopBody353_215 loopBody353_1

def loopBody353_217 : HolLoopProg 64 :=
.mark loopBody353_216

def loopBody353_218 : HolLoopProg 64 :=
.seq loopBody353_213 loopBody353_217

def loopBody353_219 : HolLoopProg 64 :=
.mark loopBody353_218

def loopBody353_220 : HolLoopProg 64 :=
.seq loopBody353_211 loopBody353_219

def loopBody353_221 : HolLoopProg 64 :=
.seq loopBody353_21 loopBody353_220

def loopBody353_222 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_221

def loopBody353_223 : HolLoopProg 64 :=
.seq loopBody353_53 loopBody353_222

def loopBody353_224 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_223

def loopBody353_225 : HolLoopProg 64 :=
.seq loopBody353_51 loopBody353_224

def loopBody353_226 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_225

def loopBody353_227 : HolLoopProg 64 :=
.seq loopBody353_49 loopBody353_226

def loopBody353_228 : HolLoopProg 64 :=
.seq loopBody353_17 loopBody353_227

def loopBody353_229 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_228

def loopBody353_230 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_229

def loopBody353_231 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_230

def loopBody353_232 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_231

def loopBody353_233 : HolLoopProg 64 :=
.seq loopBody353_3 loopBody353_232

def loopBody353_234 : HolLoopProg 64 :=
.seq loopBody353_1 loopBody353_233

def output353 : Nat × List Nat × HolLoopProg 64 :=
  (417, [0], loopBody353_234)
end InitECandidate.Proofs.FrontendStages.Loop
