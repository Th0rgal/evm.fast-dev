import InitECandidate.Proofs.FrontendStages.Loop.Translate209
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody225_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody225_1 : HolLoopProg 64 :=
.mark loopBody225_0

def loopBody225_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 4#64)

def loopBody225_3 : HolLoopProg 64 :=
.mark loopBody225_2

def loopBody225_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody225_5 : HolLoopProg 64 :=
.mark loopBody225_4

def loopBody225_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.const 2#64])

def loopBody225_7 : HolLoopProg 64 :=
.mark loopBody225_6

def loopBody225_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody225_9 : HolLoopProg 64 :=
.mark loopBody225_8

def loopBody225_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody225_11 : HolLoopProg 64 :=
.mark loopBody225_10

def loopBody225_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.RegImm.reg 5) loopBody225_9 loopBody225_11 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))

def loopBody225_13 : HolLoopProg 64 :=
.mark loopBody225_12

def loopBody225_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody225_15 : HolLoopProg 64 :=
.mark loopBody225_14

def loopBody225_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 1#64))

def loopBody225_17 : HolLoopProg 64 :=
.mark loopBody225_16

def loopBody225_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 3)

def loopBody225_19 : HolLoopProg 64 :=
.mark loopBody225_18

def loopBody225_20 : HolLoopProg 64 :=
.seq loopBody225_19 loopBody225_1

def loopBody225_21 : HolLoopProg 64 :=
.mark loopBody225_20

def loopBody225_22 : HolLoopProg 64 :=
.seq loopBody225_21 loopBody225_1

def loopBody225_23 : HolLoopProg 64 :=
.mark loopBody225_22

def loopBody225_24 : HolLoopProg 64 :=
.seq loopBody225_17 loopBody225_23

def loopBody225_25 : HolLoopProg 64 :=
.mark loopBody225_24

def loopBody225_26 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_25

def loopBody225_27 : HolLoopProg 64 :=
.mark loopBody225_26

def loopBody225_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody225_29 : HolLoopProg 64 :=
.mark loopBody225_28

def loopBody225_30 : HolLoopProg 64 :=
.seq loopBody225_27 loopBody225_29

def loopBody225_31 : HolLoopProg 64 :=
.mark loopBody225_30

def loopBody225_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody225_33 : HolLoopProg 64 :=
.mark loopBody225_32

def loopBody225_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody225_31 loopBody225_33 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody225_35 : HolLoopProg 64 :=
.mark loopBody225_34

def loopBody225_36 : HolLoopProg 64 :=
.seq loopBody225_35 loopBody225_1

def loopBody225_37 : HolLoopProg 64 :=
.mark loopBody225_36

def loopBody225_38 : HolLoopProg 64 :=
.seq loopBody225_15 loopBody225_37

def loopBody225_39 : HolLoopProg 64 :=
.mark loopBody225_38

def loopBody225_40 : HolLoopProg 64 :=
.seq loopBody225_13 loopBody225_39

def loopBody225_41 : HolLoopProg 64 :=
.mark loopBody225_40

def loopBody225_42 : HolLoopProg 64 :=
.seq loopBody225_7 loopBody225_41

def loopBody225_43 : HolLoopProg 64 :=
.mark loopBody225_42

def loopBody225_44 : HolLoopProg 64 :=
.seq loopBody225_5 loopBody225_43

def loopBody225_45 : HolLoopProg 64 :=
.mark loopBody225_44

def loopBody225_46 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) loopBody225_45 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody225_47 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 32#64)

def loopBody225_48 : HolLoopProg 64 :=
.mark loopBody225_47

def loopBody225_49 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody225_50 : HolLoopProg 64 :=
.mark loopBody225_49

def loopBody225_51 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody225_52 : HolLoopProg 64 :=
.mark loopBody225_51

def loopBody225_53 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 182) ([4, 5]) (some (4, loopBody225_52, loopBody225_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody225_54 : HolLoopProg 64 :=
.mark loopBody225_53

def loopBody225_55 : HolLoopProg 64 :=
.seq loopBody225_54 loopBody225_1

def loopBody225_56 : HolLoopProg 64 :=
.mark loopBody225_55

def loopBody225_57 : HolLoopProg 64 :=
.seq loopBody225_50 loopBody225_56

def loopBody225_58 : HolLoopProg 64 :=
.mark loopBody225_57

def loopBody225_59 : HolLoopProg 64 :=
.seq loopBody225_48 loopBody225_58

def loopBody225_60 : HolLoopProg 64 :=
.mark loopBody225_59

def loopBody225_61 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody225_62 : HolLoopProg 64 :=
.mark loopBody225_61

def loopBody225_63 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody225_64 : HolLoopProg 64 :=
.mark loopBody225_63

def loopBody225_65 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody225_66 : HolLoopProg 64 :=
.mark loopBody225_65

def loopBody225_67 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.RegImm.reg 7) loopBody225_64 loopBody225_66 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody225_68 : HolLoopProg 64 :=
.mark loopBody225_67

def loopBody225_69 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody225_70 : HolLoopProg 64 :=
.mark loopBody225_69

def loopBody225_71 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody225_72 : HolLoopProg 64 :=
.mark loopBody225_71

def loopBody225_73 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody225_74 : HolLoopProg 64 :=
.mark loopBody225_73

def loopBody225_75 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 152#64]))

def loopBody225_76 : HolLoopProg 64 :=
.mark loopBody225_75

def loopBody225_77 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody225_78 : HolLoopProg 64 :=
.mark loopBody225_77

def loopBody225_79 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 158) ([6, 7, 8]) (some (6, loopBody225_78, loopBody225_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody225_80 : HolLoopProg 64 :=
.mark loopBody225_79

def loopBody225_81 : HolLoopProg 64 :=
.seq loopBody225_80 loopBody225_1

def loopBody225_82 : HolLoopProg 64 :=
.mark loopBody225_81

def loopBody225_83 : HolLoopProg 64 :=
.seq loopBody225_76 loopBody225_82

def loopBody225_84 : HolLoopProg 64 :=
.mark loopBody225_83

def loopBody225_85 : HolLoopProg 64 :=
.seq loopBody225_74 loopBody225_84

def loopBody225_86 : HolLoopProg 64 :=
.mark loopBody225_85

def loopBody225_87 : HolLoopProg 64 :=
.seq loopBody225_72 loopBody225_86

def loopBody225_88 : HolLoopProg 64 :=
.mark loopBody225_87

def loopBody225_89 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_88

def loopBody225_90 : HolLoopProg 64 :=
.mark loopBody225_89

def loopBody225_91 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_90

def loopBody225_92 : HolLoopProg 64 :=
.mark loopBody225_91

def loopBody225_93 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody225_94 : HolLoopProg 64 :=
.mark loopBody225_93

def loopBody225_95 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 152#64]))

def loopBody225_96 : HolLoopProg 64 :=
.mark loopBody225_95

def loopBody225_97 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 0,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64)])

def loopBody225_98 : HolLoopProg 64 :=
.mark loopBody225_97

def loopBody225_99 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 192) ([6, 7, 8]) (some (6, loopBody225_78, loopBody225_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody225_100 : HolLoopProg 64 :=
.mark loopBody225_99

def loopBody225_101 : HolLoopProg 64 :=
.seq loopBody225_100 loopBody225_1

def loopBody225_102 : HolLoopProg 64 :=
.mark loopBody225_101

def loopBody225_103 : HolLoopProg 64 :=
.seq loopBody225_98 loopBody225_102

def loopBody225_104 : HolLoopProg 64 :=
.mark loopBody225_103

def loopBody225_105 : HolLoopProg 64 :=
.seq loopBody225_96 loopBody225_104

def loopBody225_106 : HolLoopProg 64 :=
.mark loopBody225_105

def loopBody225_107 : HolLoopProg 64 :=
.seq loopBody225_94 loopBody225_106

def loopBody225_108 : HolLoopProg 64 :=
.mark loopBody225_107

def loopBody225_109 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_108

def loopBody225_110 : HolLoopProg 64 :=
.mark loopBody225_109

def loopBody225_111 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_110

def loopBody225_112 : HolLoopProg 64 :=
.mark loopBody225_111

def loopBody225_113 : HolLoopProg 64 :=
.seq loopBody225_92 loopBody225_112

def loopBody225_114 : HolLoopProg 64 :=
.mark loopBody225_113

def loopBody225_115 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody225_116 : HolLoopProg 64 :=
.mark loopBody225_115

def loopBody225_117 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 5)

def loopBody225_118 : HolLoopProg 64 :=
.mark loopBody225_117

def loopBody225_119 : HolLoopProg 64 :=
.seq loopBody225_118 loopBody225_1

def loopBody225_120 : HolLoopProg 64 :=
.mark loopBody225_119

def loopBody225_121 : HolLoopProg 64 :=
.seq loopBody225_120 loopBody225_1

def loopBody225_122 : HolLoopProg 64 :=
.mark loopBody225_121

def loopBody225_123 : HolLoopProg 64 :=
.seq loopBody225_116 loopBody225_122

def loopBody225_124 : HolLoopProg 64 :=
.mark loopBody225_123

def loopBody225_125 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_124

def loopBody225_126 : HolLoopProg 64 :=
.mark loopBody225_125

def loopBody225_127 : HolLoopProg 64 :=
.seq loopBody225_114 loopBody225_126

def loopBody225_128 : HolLoopProg 64 :=
.mark loopBody225_127

def loopBody225_129 : HolLoopProg 64 :=
.seq loopBody225_128 loopBody225_29

def loopBody225_130 : HolLoopProg 64 :=
.mark loopBody225_129

def loopBody225_131 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody225_130 loopBody225_33 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody225_132 : HolLoopProg 64 :=
.mark loopBody225_131

def loopBody225_133 : HolLoopProg 64 :=
.seq loopBody225_132 loopBody225_1

def loopBody225_134 : HolLoopProg 64 :=
.mark loopBody225_133

def loopBody225_135 : HolLoopProg 64 :=
.seq loopBody225_70 loopBody225_134

def loopBody225_136 : HolLoopProg 64 :=
.mark loopBody225_135

def loopBody225_137 : HolLoopProg 64 :=
.seq loopBody225_68 loopBody225_136

def loopBody225_138 : HolLoopProg 64 :=
.mark loopBody225_137

def loopBody225_139 : HolLoopProg 64 :=
.seq loopBody225_62 loopBody225_138

def loopBody225_140 : HolLoopProg 64 :=
.mark loopBody225_139

def loopBody225_141 : HolLoopProg 64 :=
.seq loopBody225_15 loopBody225_140

def loopBody225_142 : HolLoopProg 64 :=
.mark loopBody225_141

def loopBody225_143 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody225_142 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody225_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody225_145 : HolLoopProg 64 :=
.mark loopBody225_144

def loopBody225_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody225_147 : HolLoopProg 64 :=
.mark loopBody225_146

def loopBody225_148 : HolLoopProg 64 :=
.seq loopBody225_147 loopBody225_1

def loopBody225_149 : HolLoopProg 64 :=
.mark loopBody225_148

def loopBody225_150 : HolLoopProg 64 :=
.seq loopBody225_145 loopBody225_149

def loopBody225_151 : HolLoopProg 64 :=
.mark loopBody225_150

def loopBody225_152 : HolLoopProg 64 :=
.seq loopBody225_143 loopBody225_151

def loopBody225_153 : HolLoopProg 64 :=
.seq loopBody225_11 loopBody225_152

def loopBody225_154 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_153

def loopBody225_155 : HolLoopProg 64 :=
.seq loopBody225_60 loopBody225_154

def loopBody225_156 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_155

def loopBody225_157 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_156

def loopBody225_158 : HolLoopProg 64 :=
.seq loopBody225_46 loopBody225_157

def loopBody225_159 : HolLoopProg 64 :=
.seq loopBody225_3 loopBody225_158

def loopBody225_160 : HolLoopProg 64 :=
.seq loopBody225_1 loopBody225_159

def output225 : Nat × List Nat × HolLoopProg 64 :=
  (289, [0, 1], loopBody225_160)
end InitECandidate.Proofs.FrontendStages.Loop
