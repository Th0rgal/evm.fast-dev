import InitECandidate.Proofs.FrontendStages.Loop.Translate229
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody245_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody245_1 : HolLoopProg 64 :=
.mark loopBody245_0

def loopBody245_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 32#64]))

def loopBody245_3 : HolLoopProg 64 :=
.mark loopBody245_2

def loopBody245_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 40#64]))

def loopBody245_5 : HolLoopProg 64 :=
.mark loopBody245_4

def loopBody245_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody245_7 : HolLoopProg 64 :=
.mark loopBody245_6

def loopBody245_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody245_9 : HolLoopProg 64 :=
.mark loopBody245_8

def loopBody245_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody245_11 : HolLoopProg 64 :=
.mark loopBody245_10

def loopBody245_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody245_13 : HolLoopProg 64 :=
.mark loopBody245_12

def loopBody245_14 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.RegImm.reg 9) loopBody245_11 loopBody245_13 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody245_15 : HolLoopProg 64 :=
.mark loopBody245_14

def loopBody245_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody245_17 : HolLoopProg 64 :=
.mark loopBody245_16

def loopBody245_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody245_19 : HolLoopProg 64 :=
.mark loopBody245_18

def loopBody245_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody245_21 : HolLoopProg 64 :=
.mark loopBody245_20

def loopBody245_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody245_23 : HolLoopProg 64 :=
.mark loopBody245_22

def loopBody245_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody245_25 : HolLoopProg 64 :=
.mark loopBody245_24

def loopBody245_26 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 79) ([8, 9, 10]) (some (8, loopBody245_25, loopBody245_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody245_27 : HolLoopProg 64 :=
.mark loopBody245_26

def loopBody245_28 : HolLoopProg 64 :=
.seq loopBody245_27 loopBody245_1

def loopBody245_29 : HolLoopProg 64 :=
.mark loopBody245_28

def loopBody245_30 : HolLoopProg 64 :=
.seq loopBody245_23 loopBody245_29

def loopBody245_31 : HolLoopProg 64 :=
.mark loopBody245_30

def loopBody245_32 : HolLoopProg 64 :=
.seq loopBody245_21 loopBody245_31

def loopBody245_33 : HolLoopProg 64 :=
.mark loopBody245_32

def loopBody245_34 : HolLoopProg 64 :=
.seq loopBody245_19 loopBody245_33

def loopBody245_35 : HolLoopProg 64 :=
.mark loopBody245_34

def loopBody245_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody245_37 : HolLoopProg 64 :=
.mark loopBody245_36

def loopBody245_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody245_39 : HolLoopProg 64 :=
.mark loopBody245_38

def loopBody245_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody245_41 : HolLoopProg 64 :=
.mark loopBody245_40

def loopBody245_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody245_43 : HolLoopProg 64 :=
.mark loopBody245_42

def loopBody245_44 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.reg 10) loopBody245_41 loopBody245_43 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody245_45 : HolLoopProg 64 :=
.mark loopBody245_44

def loopBody245_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody245_47 : HolLoopProg 64 :=
.mark loopBody245_46

def loopBody245_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64])

def loopBody245_49 : HolLoopProg 64 :=
.mark loopBody245_48

def loopBody245_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody245_51 : HolLoopProg 64 :=
.mark loopBody245_50

def loopBody245_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 9)

def loopBody245_53 : HolLoopProg 64 :=
.mark loopBody245_52

def loopBody245_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 8) 10

def loopBody245_55 : HolLoopProg 64 :=
.mark loopBody245_54

def loopBody245_56 : HolLoopProg 64 :=
.seq loopBody245_55 loopBody245_1

def loopBody245_57 : HolLoopProg 64 :=
.mark loopBody245_56

def loopBody245_58 : HolLoopProg 64 :=
.seq loopBody245_53 loopBody245_57

def loopBody245_59 : HolLoopProg 64 :=
.mark loopBody245_58

def loopBody245_60 : HolLoopProg 64 :=
.seq loopBody245_59 loopBody245_1

def loopBody245_61 : HolLoopProg 64 :=
.mark loopBody245_60

def loopBody245_62 : HolLoopProg 64 :=
.seq loopBody245_51 loopBody245_61

def loopBody245_63 : HolLoopProg 64 :=
.mark loopBody245_62

def loopBody245_64 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_63

def loopBody245_65 : HolLoopProg 64 :=
.mark loopBody245_64

def loopBody245_66 : HolLoopProg 64 :=
.seq loopBody245_49 loopBody245_65

def loopBody245_67 : HolLoopProg 64 :=
.mark loopBody245_66

def loopBody245_68 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_67

def loopBody245_69 : HolLoopProg 64 :=
.mark loopBody245_68

def loopBody245_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 56#64])

def loopBody245_71 : HolLoopProg 64 :=
.mark loopBody245_70

def loopBody245_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody245_73 : HolLoopProg 64 :=
.mark loopBody245_72

def loopBody245_74 : HolLoopProg 64 :=
.seq loopBody245_73 loopBody245_61

def loopBody245_75 : HolLoopProg 64 :=
.mark loopBody245_74

def loopBody245_76 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_75

def loopBody245_77 : HolLoopProg 64 :=
.mark loopBody245_76

def loopBody245_78 : HolLoopProg 64 :=
.seq loopBody245_71 loopBody245_77

def loopBody245_79 : HolLoopProg 64 :=
.mark loopBody245_78

def loopBody245_80 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_79

def loopBody245_81 : HolLoopProg 64 :=
.mark loopBody245_80

def loopBody245_82 : HolLoopProg 64 :=
.seq loopBody245_69 loopBody245_81

def loopBody245_83 : HolLoopProg 64 :=
.mark loopBody245_82

def loopBody245_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 0)

def loopBody245_85 : HolLoopProg 64 :=
.mark loopBody245_84

def loopBody245_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody245_87 : HolLoopProg 64 :=
.mark loopBody245_86

def loopBody245_88 : HolLoopProg 64 :=
.seq loopBody245_87 loopBody245_1

def loopBody245_89 : HolLoopProg 64 :=
.mark loopBody245_88

def loopBody245_90 : HolLoopProg 64 :=
.seq loopBody245_85 loopBody245_89

def loopBody245_91 : HolLoopProg 64 :=
.mark loopBody245_90

def loopBody245_92 : HolLoopProg 64 :=
.seq loopBody245_83 loopBody245_91

def loopBody245_93 : HolLoopProg 64 :=
.mark loopBody245_92

def loopBody245_94 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody245_93 loopBody245_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody245_95 : HolLoopProg 64 :=
.mark loopBody245_94

def loopBody245_96 : HolLoopProg 64 :=
.seq loopBody245_95 loopBody245_1

def loopBody245_97 : HolLoopProg 64 :=
.mark loopBody245_96

def loopBody245_98 : HolLoopProg 64 :=
.seq loopBody245_47 loopBody245_97

def loopBody245_99 : HolLoopProg 64 :=
.mark loopBody245_98

def loopBody245_100 : HolLoopProg 64 :=
.seq loopBody245_45 loopBody245_99

def loopBody245_101 : HolLoopProg 64 :=
.mark loopBody245_100

def loopBody245_102 : HolLoopProg 64 :=
.seq loopBody245_39 loopBody245_101

def loopBody245_103 : HolLoopProg 64 :=
.mark loopBody245_102

def loopBody245_104 : HolLoopProg 64 :=
.seq loopBody245_37 loopBody245_103

def loopBody245_105 : HolLoopProg 64 :=
.mark loopBody245_104

def loopBody245_106 : HolLoopProg 64 :=
.seq loopBody245_35 loopBody245_105

def loopBody245_107 : HolLoopProg 64 :=
.mark loopBody245_106

def loopBody245_108 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_107

def loopBody245_109 : HolLoopProg 64 :=
.mark loopBody245_108

def loopBody245_110 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_109

def loopBody245_111 : HolLoopProg 64 :=
.mark loopBody245_110

def loopBody245_112 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.RegImm.imm 0#64) loopBody245_111 loopBody245_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody245_113 : HolLoopProg 64 :=
.mark loopBody245_112

def loopBody245_114 : HolLoopProg 64 :=
.seq loopBody245_113 loopBody245_1

def loopBody245_115 : HolLoopProg 64 :=
.mark loopBody245_114

def loopBody245_116 : HolLoopProg 64 :=
.seq loopBody245_17 loopBody245_115

def loopBody245_117 : HolLoopProg 64 :=
.mark loopBody245_116

def loopBody245_118 : HolLoopProg 64 :=
.seq loopBody245_15 loopBody245_117

def loopBody245_119 : HolLoopProg 64 :=
.mark loopBody245_118

def loopBody245_120 : HolLoopProg 64 :=
.seq loopBody245_9 loopBody245_119

def loopBody245_121 : HolLoopProg 64 :=
.mark loopBody245_120

def loopBody245_122 : HolLoopProg 64 :=
.seq loopBody245_7 loopBody245_121

def loopBody245_123 : HolLoopProg 64 :=
.mark loopBody245_122

def loopBody245_124 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody245_125 : HolLoopProg 64 :=
.mark loopBody245_124

def loopBody245_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody245_127 : HolLoopProg 64 :=
.mark loopBody245_126

def loopBody245_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody245_129 : HolLoopProg 64 :=
.mark loopBody245_128

def loopBody245_130 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 287) ([8, 9, 10, 11]) (some (8, loopBody245_25, loopBody245_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody245_131 : HolLoopProg 64 :=
.mark loopBody245_130

def loopBody245_132 : HolLoopProg 64 :=
.seq loopBody245_131 loopBody245_1

def loopBody245_133 : HolLoopProg 64 :=
.mark loopBody245_132

def loopBody245_134 : HolLoopProg 64 :=
.seq loopBody245_129 loopBody245_133

def loopBody245_135 : HolLoopProg 64 :=
.mark loopBody245_134

def loopBody245_136 : HolLoopProg 64 :=
.seq loopBody245_127 loopBody245_135

def loopBody245_137 : HolLoopProg 64 :=
.mark loopBody245_136

def loopBody245_138 : HolLoopProg 64 :=
.seq loopBody245_125 loopBody245_137

def loopBody245_139 : HolLoopProg 64 :=
.mark loopBody245_138

def loopBody245_140 : HolLoopProg 64 :=
.seq loopBody245_19 loopBody245_139

def loopBody245_141 : HolLoopProg 64 :=
.mark loopBody245_140

def loopBody245_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.var 7])

def loopBody245_143 : HolLoopProg 64 :=
.mark loopBody245_142

def loopBody245_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.var 7])

def loopBody245_145 : HolLoopProg 64 :=
.mark loopBody245_144

def loopBody245_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64]))

def loopBody245_147 : HolLoopProg 64 :=
.mark loopBody245_146

def loopBody245_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 56#64]))

def loopBody245_149 : HolLoopProg 64 :=
.mark loopBody245_148

def loopBody245_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 7])

def loopBody245_151 : HolLoopProg 64 :=
.mark loopBody245_150

def loopBody245_152 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 7])

def loopBody245_153 : HolLoopProg 64 :=
.mark loopBody245_152

def loopBody245_154 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody245_155 : HolLoopProg 64 :=
.mark loopBody245_154

def loopBody245_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody245_157 : HolLoopProg 64 :=
.mark loopBody245_156

def loopBody245_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody245_159 : HolLoopProg 64 :=
.mark loopBody245_158

def loopBody245_160 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 308) ([9, 10, 11, 12, 13, 14, 15, 16]) (some (9, loopBody245_159, loopBody245_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody245_161 : HolLoopProg 64 :=
.mark loopBody245_160

def loopBody245_162 : HolLoopProg 64 :=
.seq loopBody245_161 loopBody245_1

def loopBody245_163 : HolLoopProg 64 :=
.mark loopBody245_162

def loopBody245_164 : HolLoopProg 64 :=
.seq loopBody245_157 loopBody245_163

def loopBody245_165 : HolLoopProg 64 :=
.mark loopBody245_164

def loopBody245_166 : HolLoopProg 64 :=
.seq loopBody245_155 loopBody245_165

def loopBody245_167 : HolLoopProg 64 :=
.mark loopBody245_166

def loopBody245_168 : HolLoopProg 64 :=
.seq loopBody245_153 loopBody245_167

def loopBody245_169 : HolLoopProg 64 :=
.mark loopBody245_168

def loopBody245_170 : HolLoopProg 64 :=
.seq loopBody245_151 loopBody245_169

def loopBody245_171 : HolLoopProg 64 :=
.mark loopBody245_170

def loopBody245_172 : HolLoopProg 64 :=
.seq loopBody245_149 loopBody245_171

def loopBody245_173 : HolLoopProg 64 :=
.mark loopBody245_172

def loopBody245_174 : HolLoopProg 64 :=
.seq loopBody245_147 loopBody245_173

def loopBody245_175 : HolLoopProg 64 :=
.mark loopBody245_174

def loopBody245_176 : HolLoopProg 64 :=
.seq loopBody245_145 loopBody245_175

def loopBody245_177 : HolLoopProg 64 :=
.mark loopBody245_176

def loopBody245_178 : HolLoopProg 64 :=
.seq loopBody245_143 loopBody245_177

def loopBody245_179 : HolLoopProg 64 :=
.mark loopBody245_178

def loopBody245_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody245_181 : HolLoopProg 64 :=
.mark loopBody245_180

def loopBody245_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody245_183 : HolLoopProg 64 :=
.mark loopBody245_182

def loopBody245_184 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.RegImm.reg 11) loopBody245_183 loopBody245_39 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody245_185 : HolLoopProg 64 :=
.mark loopBody245_184

def loopBody245_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody245_187 : HolLoopProg 64 :=
.mark loopBody245_186

def loopBody245_188 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody245_189 : HolLoopProg 64 :=
.mark loopBody245_188

def loopBody245_190 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 7)

def loopBody245_191 : HolLoopProg 64 :=
.mark loopBody245_190

def loopBody245_192 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody245_193 : HolLoopProg 64 :=
.mark loopBody245_192

def loopBody245_194 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 293) [9, 10, 11] none

def loopBody245_195 : HolLoopProg 64 :=
.mark loopBody245_194

def loopBody245_196 : HolLoopProg 64 :=
.seq loopBody245_195 loopBody245_1

def loopBody245_197 : HolLoopProg 64 :=
.mark loopBody245_196

def loopBody245_198 : HolLoopProg 64 :=
.seq loopBody245_193 loopBody245_197

def loopBody245_199 : HolLoopProg 64 :=
.mark loopBody245_198

def loopBody245_200 : HolLoopProg 64 :=
.seq loopBody245_191 loopBody245_199

def loopBody245_201 : HolLoopProg 64 :=
.mark loopBody245_200

def loopBody245_202 : HolLoopProg 64 :=
.seq loopBody245_189 loopBody245_201

def loopBody245_203 : HolLoopProg 64 :=
.mark loopBody245_202

def loopBody245_204 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.RegImm.imm 0#64) loopBody245_203 loopBody245_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  Flapjack.Spt.ln)

def loopBody245_205 : HolLoopProg 64 :=
.mark loopBody245_204

def loopBody245_206 : HolLoopProg 64 :=
.seq loopBody245_205 loopBody245_1

def loopBody245_207 : HolLoopProg 64 :=
.mark loopBody245_206

def loopBody245_208 : HolLoopProg 64 :=
.seq loopBody245_187 loopBody245_207

def loopBody245_209 : HolLoopProg 64 :=
.mark loopBody245_208

def loopBody245_210 : HolLoopProg 64 :=
.seq loopBody245_185 loopBody245_209

def loopBody245_211 : HolLoopProg 64 :=
.mark loopBody245_210

def loopBody245_212 : HolLoopProg 64 :=
.seq loopBody245_181 loopBody245_211

def loopBody245_213 : HolLoopProg 64 :=
.mark loopBody245_212

def loopBody245_214 : HolLoopProg 64 :=
.seq loopBody245_39 loopBody245_213

def loopBody245_215 : HolLoopProg 64 :=
.mark loopBody245_214

def loopBody245_216 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 8)

def loopBody245_217 : HolLoopProg 64 :=
.mark loopBody245_216

def loopBody245_218 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9]

def loopBody245_219 : HolLoopProg 64 :=
.mark loopBody245_218

def loopBody245_220 : HolLoopProg 64 :=
.seq loopBody245_219 loopBody245_1

def loopBody245_221 : HolLoopProg 64 :=
.mark loopBody245_220

def loopBody245_222 : HolLoopProg 64 :=
.seq loopBody245_217 loopBody245_221

def loopBody245_223 : HolLoopProg 64 :=
.mark loopBody245_222

def loopBody245_224 : HolLoopProg 64 :=
.seq loopBody245_215 loopBody245_223

def loopBody245_225 : HolLoopProg 64 :=
.mark loopBody245_224

def loopBody245_226 : HolLoopProg 64 :=
.seq loopBody245_179 loopBody245_225

def loopBody245_227 : HolLoopProg 64 :=
.mark loopBody245_226

def loopBody245_228 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_227

def loopBody245_229 : HolLoopProg 64 :=
.mark loopBody245_228

def loopBody245_230 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_229

def loopBody245_231 : HolLoopProg 64 :=
.mark loopBody245_230

def loopBody245_232 : HolLoopProg 64 :=
.seq loopBody245_141 loopBody245_231

def loopBody245_233 : HolLoopProg 64 :=
.mark loopBody245_232

def loopBody245_234 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_233

def loopBody245_235 : HolLoopProg 64 :=
.mark loopBody245_234

def loopBody245_236 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_235

def loopBody245_237 : HolLoopProg 64 :=
.mark loopBody245_236

def loopBody245_238 : HolLoopProg 64 :=
.seq loopBody245_123 loopBody245_237

def loopBody245_239 : HolLoopProg 64 :=
.mark loopBody245_238

def loopBody245_240 : HolLoopProg 64 :=
.seq loopBody245_5 loopBody245_239

def loopBody245_241 : HolLoopProg 64 :=
.mark loopBody245_240

def loopBody245_242 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_241

def loopBody245_243 : HolLoopProg 64 :=
.mark loopBody245_242

def loopBody245_244 : HolLoopProg 64 :=
.seq loopBody245_3 loopBody245_243

def loopBody245_245 : HolLoopProg 64 :=
.mark loopBody245_244

def loopBody245_246 : HolLoopProg 64 :=
.seq loopBody245_1 loopBody245_245

def loopBody245_247 : HolLoopProg 64 :=
.mark loopBody245_246

def output245 : Nat × List Nat × HolLoopProg 64 :=
  (309, [0, 1, 2, 3, 4], loopBody245_247)
end InitECandidate.Proofs.FrontendStages.Loop
