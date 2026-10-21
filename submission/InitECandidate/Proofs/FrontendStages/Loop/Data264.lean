import InitECandidate.Proofs.FrontendStages.Loop.Translate248
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody264_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody264_1 : HolLoopProg 64 :=
.mark loopBody264_0

def loopBody264_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody264_3 : HolLoopProg 64 :=
.mark loopBody264_2

def loopBody264_4 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (4, loopBody264_3, loopBody264_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody264_5 : HolLoopProg 64 :=
.mark loopBody264_4

def loopBody264_6 : HolLoopProg 64 :=
.seq loopBody264_5 loopBody264_1

def loopBody264_7 : HolLoopProg 64 :=
.mark loopBody264_6

def loopBody264_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody264_9 : HolLoopProg 64 :=
.mark loopBody264_8

def loopBody264_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody264_11 : HolLoopProg 64 :=
.mark loopBody264_10

def loopBody264_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody264_13 : HolLoopProg 64 :=
.mark loopBody264_12

def loopBody264_14 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 304) ([5, 6]) (some (5, loopBody264_13, loopBody264_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody264_15 : HolLoopProg 64 :=
.mark loopBody264_14

def loopBody264_16 : HolLoopProg 64 :=
.seq loopBody264_15 loopBody264_1

def loopBody264_17 : HolLoopProg 64 :=
.mark loopBody264_16

def loopBody264_18 : HolLoopProg 64 :=
.seq loopBody264_11 loopBody264_17

def loopBody264_19 : HolLoopProg 64 :=
.mark loopBody264_18

def loopBody264_20 : HolLoopProg 64 :=
.seq loopBody264_9 loopBody264_19

def loopBody264_21 : HolLoopProg 64 :=
.mark loopBody264_20

def loopBody264_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody264_23 : HolLoopProg 64 :=
.mark loopBody264_22

def loopBody264_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody264_25 : HolLoopProg 64 :=
.mark loopBody264_24

def loopBody264_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody264_27 : HolLoopProg 64 :=
.mark loopBody264_26

def loopBody264_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody264_29 : HolLoopProg 64 :=
.mark loopBody264_28

def loopBody264_30 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody264_27 loopBody264_29 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody264_31 : HolLoopProg 64 :=
.mark loopBody264_30

def loopBody264_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody264_33 : HolLoopProg 64 :=
.mark loopBody264_32

def loopBody264_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 160#64]))

def loopBody264_35 : HolLoopProg 64 :=
.mark loopBody264_34

def loopBody264_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody264_37 : HolLoopProg 64 :=
.mark loopBody264_36

def loopBody264_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody264_39 : HolLoopProg 64 :=
.mark loopBody264_38

def loopBody264_40 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 177) ([7, 8]) (some (7, loopBody264_39, loopBody264_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody264_41 : HolLoopProg 64 :=
.mark loopBody264_40

def loopBody264_42 : HolLoopProg 64 :=
.seq loopBody264_41 loopBody264_1

def loopBody264_43 : HolLoopProg 64 :=
.mark loopBody264_42

def loopBody264_44 : HolLoopProg 64 :=
.seq loopBody264_37 loopBody264_43

def loopBody264_45 : HolLoopProg 64 :=
.mark loopBody264_44

def loopBody264_46 : HolLoopProg 64 :=
.seq loopBody264_35 loopBody264_45

def loopBody264_47 : HolLoopProg 64 :=
.mark loopBody264_46

def loopBody264_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody264_49 : HolLoopProg 64 :=
.mark loopBody264_48

def loopBody264_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 160#64]))

def loopBody264_51 : HolLoopProg 64 :=
.mark loopBody264_50

def loopBody264_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody264_53 : HolLoopProg 64 :=
.mark loopBody264_52

def loopBody264_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody264_55 : HolLoopProg 64 :=
.mark loopBody264_54

def loopBody264_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody264_57 : HolLoopProg 64 :=
.mark loopBody264_56

def loopBody264_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody264_59 : HolLoopProg 64 :=
.mark loopBody264_58

def loopBody264_60 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 316) ([8, 9, 10, 11, 12]) (some (8, loopBody264_59, loopBody264_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody264_61 : HolLoopProg 64 :=
.mark loopBody264_60

def loopBody264_62 : HolLoopProg 64 :=
.seq loopBody264_61 loopBody264_1

def loopBody264_63 : HolLoopProg 64 :=
.mark loopBody264_62

def loopBody264_64 : HolLoopProg 64 :=
.seq loopBody264_57 loopBody264_63

def loopBody264_65 : HolLoopProg 64 :=
.mark loopBody264_64

def loopBody264_66 : HolLoopProg 64 :=
.seq loopBody264_55 loopBody264_65

def loopBody264_67 : HolLoopProg 64 :=
.mark loopBody264_66

def loopBody264_68 : HolLoopProg 64 :=
.seq loopBody264_53 loopBody264_67

def loopBody264_69 : HolLoopProg 64 :=
.mark loopBody264_68

def loopBody264_70 : HolLoopProg 64 :=
.seq loopBody264_51 loopBody264_69

def loopBody264_71 : HolLoopProg 64 :=
.mark loopBody264_70

def loopBody264_72 : HolLoopProg 64 :=
.seq loopBody264_49 loopBody264_71

def loopBody264_73 : HolLoopProg 64 :=
.mark loopBody264_72

def loopBody264_74 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_73

def loopBody264_75 : HolLoopProg 64 :=
.mark loopBody264_74

def loopBody264_76 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_75

def loopBody264_77 : HolLoopProg 64 :=
.mark loopBody264_76

def loopBody264_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody264_79 : HolLoopProg 64 :=
.mark loopBody264_78

def loopBody264_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 7)

def loopBody264_81 : HolLoopProg 64 :=
.mark loopBody264_80

def loopBody264_82 : HolLoopProg 64 :=
.seq loopBody264_81 loopBody264_1

def loopBody264_83 : HolLoopProg 64 :=
.mark loopBody264_82

def loopBody264_84 : HolLoopProg 64 :=
.seq loopBody264_83 loopBody264_1

def loopBody264_85 : HolLoopProg 64 :=
.mark loopBody264_84

def loopBody264_86 : HolLoopProg 64 :=
.seq loopBody264_79 loopBody264_85

def loopBody264_87 : HolLoopProg 64 :=
.mark loopBody264_86

def loopBody264_88 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_87

def loopBody264_89 : HolLoopProg 64 :=
.mark loopBody264_88

def loopBody264_90 : HolLoopProg 64 :=
.seq loopBody264_77 loopBody264_89

def loopBody264_91 : HolLoopProg 64 :=
.mark loopBody264_90

def loopBody264_92 : HolLoopProg 64 :=
.seq loopBody264_47 loopBody264_91

def loopBody264_93 : HolLoopProg 64 :=
.mark loopBody264_92

def loopBody264_94 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_93

def loopBody264_95 : HolLoopProg 64 :=
.mark loopBody264_94

def loopBody264_96 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_95

def loopBody264_97 : HolLoopProg 64 :=
.mark loopBody264_96

def loopBody264_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody264_99 : HolLoopProg 64 :=
.mark loopBody264_98

def loopBody264_100 : HolLoopProg 64 :=
.seq loopBody264_97 loopBody264_99

def loopBody264_101 : HolLoopProg 64 :=
.mark loopBody264_100

def loopBody264_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody264_103 : HolLoopProg 64 :=
.mark loopBody264_102

def loopBody264_104 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody264_101 loopBody264_103 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody264_105 : HolLoopProg 64 :=
.mark loopBody264_104

def loopBody264_106 : HolLoopProg 64 :=
.seq loopBody264_105 loopBody264_1

def loopBody264_107 : HolLoopProg 64 :=
.mark loopBody264_106

def loopBody264_108 : HolLoopProg 64 :=
.seq loopBody264_33 loopBody264_107

def loopBody264_109 : HolLoopProg 64 :=
.mark loopBody264_108

def loopBody264_110 : HolLoopProg 64 :=
.seq loopBody264_31 loopBody264_109

def loopBody264_111 : HolLoopProg 64 :=
.mark loopBody264_110

def loopBody264_112 : HolLoopProg 64 :=
.seq loopBody264_25 loopBody264_111

def loopBody264_113 : HolLoopProg 64 :=
.mark loopBody264_112

def loopBody264_114 : HolLoopProg 64 :=
.seq loopBody264_23 loopBody264_113

def loopBody264_115 : HolLoopProg 64 :=
.mark loopBody264_114

def loopBody264_116 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody264_115 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody264_117 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody264_118 : HolLoopProg 64 :=
.mark loopBody264_117

def loopBody264_119 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody264_120 : HolLoopProg 64 :=
.mark loopBody264_119

def loopBody264_121 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 327) ([7, 8]) (some (7, loopBody264_39, loopBody264_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody264_122 : HolLoopProg 64 :=
.mark loopBody264_121

def loopBody264_123 : HolLoopProg 64 :=
.seq loopBody264_122 loopBody264_1

def loopBody264_124 : HolLoopProg 64 :=
.mark loopBody264_123

def loopBody264_125 : HolLoopProg 64 :=
.seq loopBody264_120 loopBody264_124

def loopBody264_126 : HolLoopProg 64 :=
.mark loopBody264_125

def loopBody264_127 : HolLoopProg 64 :=
.seq loopBody264_118 loopBody264_126

def loopBody264_128 : HolLoopProg 64 :=
.mark loopBody264_127

def loopBody264_129 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_128

def loopBody264_130 : HolLoopProg 64 :=
.mark loopBody264_129

def loopBody264_131 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_130

def loopBody264_132 : HolLoopProg 64 :=
.mark loopBody264_131

def loopBody264_133 : HolLoopProg 64 :=
.seq loopBody264_116 loopBody264_132

def loopBody264_134 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody264_135 : HolLoopProg 64 :=
.mark loopBody264_134

def loopBody264_136 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 70) ([7]) (some (7, loopBody264_39, loopBody264_1, (Flapjack.Spt.ln)))

def loopBody264_137 : HolLoopProg 64 :=
.mark loopBody264_136

def loopBody264_138 : HolLoopProg 64 :=
.seq loopBody264_137 loopBody264_1

def loopBody264_139 : HolLoopProg 64 :=
.mark loopBody264_138

def loopBody264_140 : HolLoopProg 64 :=
.seq loopBody264_135 loopBody264_139

def loopBody264_141 : HolLoopProg 64 :=
.mark loopBody264_140

def loopBody264_142 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_141

def loopBody264_143 : HolLoopProg 64 :=
.mark loopBody264_142

def loopBody264_144 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_143

def loopBody264_145 : HolLoopProg 64 :=
.mark loopBody264_144

def loopBody264_146 : HolLoopProg 64 :=
.seq loopBody264_133 loopBody264_145

def loopBody264_147 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody264_148 : HolLoopProg 64 :=
.mark loopBody264_147

def loopBody264_149 : HolLoopProg 64 :=
.seq loopBody264_148 loopBody264_1

def loopBody264_150 : HolLoopProg 64 :=
.mark loopBody264_149

def loopBody264_151 : HolLoopProg 64 :=
.seq loopBody264_11 loopBody264_150

def loopBody264_152 : HolLoopProg 64 :=
.mark loopBody264_151

def loopBody264_153 : HolLoopProg 64 :=
.seq loopBody264_146 loopBody264_152

def loopBody264_154 : HolLoopProg 64 :=
.seq loopBody264_9 loopBody264_153

def loopBody264_155 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_154

def loopBody264_156 : HolLoopProg 64 :=
.seq loopBody264_21 loopBody264_155

def loopBody264_157 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_156

def loopBody264_158 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_157

def loopBody264_159 : HolLoopProg 64 :=
.seq loopBody264_7 loopBody264_158

def loopBody264_160 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_159

def loopBody264_161 : HolLoopProg 64 :=
.seq loopBody264_1 loopBody264_160

def output264 : Nat × List Nat × HolLoopProg 64 :=
  (328, [0, 1, 2], loopBody264_161)
end InitECandidate.Proofs.FrontendStages.Loop
