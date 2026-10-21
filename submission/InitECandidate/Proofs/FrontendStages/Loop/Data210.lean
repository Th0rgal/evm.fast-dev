import InitECandidate.Proofs.FrontendStages.Loop.Translate194
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody210_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 256#64)

def loopBody210_1 : HolLoopProg 64 :=
.mark loopBody210_0

def loopBody210_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody210_3 : HolLoopProg 64 :=
.mark loopBody210_2

def loopBody210_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody210_5 : HolLoopProg 64 :=
.mark loopBody210_4

def loopBody210_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody210_7 : HolLoopProg 64 :=
.mark loopBody210_6

def loopBody210_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 3 (Flapjack.RegImm.reg 4) loopBody210_5 loopBody210_7 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody210_9 : HolLoopProg 64 :=
.mark loopBody210_8

def loopBody210_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody210_11 : HolLoopProg 64 :=
.mark loopBody210_10

def loopBody210_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody210_13 : HolLoopProg 64 :=
.mark loopBody210_12

def loopBody210_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody210_15 : HolLoopProg 64 :=
.mark loopBody210_14

def loopBody210_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 2)

def loopBody210_17 : HolLoopProg 64 :=
.mark loopBody210_16

def loopBody210_18 : HolLoopProg 64 :=
.seq loopBody210_17 loopBody210_13

def loopBody210_19 : HolLoopProg 64 :=
.mark loopBody210_18

def loopBody210_20 : HolLoopProg 64 :=
.seq loopBody210_19 loopBody210_13

def loopBody210_21 : HolLoopProg 64 :=
.mark loopBody210_20

def loopBody210_22 : HolLoopProg 64 :=
.seq loopBody210_15 loopBody210_21

def loopBody210_23 : HolLoopProg 64 :=
.mark loopBody210_22

def loopBody210_24 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_23

def loopBody210_25 : HolLoopProg 64 :=
.mark loopBody210_24

def loopBody210_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 4#64)

def loopBody210_27 : HolLoopProg 64 :=
.mark loopBody210_26

def loopBody210_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody210_29 : HolLoopProg 64 :=
.mark loopBody210_28

def loopBody210_30 : HolLoopProg 64 :=
.seq loopBody210_27 loopBody210_29

def loopBody210_31 : HolLoopProg 64 :=
.mark loopBody210_30

def loopBody210_32 : HolLoopProg 64 :=
.seq loopBody210_25 loopBody210_31

def loopBody210_33 : HolLoopProg 64 :=
.mark loopBody210_32

def loopBody210_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody210_33 loopBody210_13 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody210_35 : HolLoopProg 64 :=
.mark loopBody210_34

def loopBody210_36 : HolLoopProg 64 :=
.seq loopBody210_35 loopBody210_13

def loopBody210_37 : HolLoopProg 64 :=
.mark loopBody210_36

def loopBody210_38 : HolLoopProg 64 :=
.seq loopBody210_11 loopBody210_37

def loopBody210_39 : HolLoopProg 64 :=
.mark loopBody210_38

def loopBody210_40 : HolLoopProg 64 :=
.seq loopBody210_9 loopBody210_39

def loopBody210_41 : HolLoopProg 64 :=
.mark loopBody210_40

def loopBody210_42 : HolLoopProg 64 :=
.seq loopBody210_3 loopBody210_41

def loopBody210_43 : HolLoopProg 64 :=
.mark loopBody210_42

def loopBody210_44 : HolLoopProg 64 :=
.seq loopBody210_1 loopBody210_43

def loopBody210_45 : HolLoopProg 64 :=
.mark loopBody210_44

def loopBody210_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 3#64),
      Flapjack.HolLoopExp.const 8#64])

def loopBody210_47 : HolLoopProg 64 :=
.mark loopBody210_46

def loopBody210_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody210_49 : HolLoopProg 64 :=
.mark loopBody210_48

def loopBody210_50 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([3]) (some (3, loopBody210_49, loopBody210_13, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody210_51 : HolLoopProg 64 :=
.mark loopBody210_50

def loopBody210_52 : HolLoopProg 64 :=
.seq loopBody210_51 loopBody210_13

def loopBody210_53 : HolLoopProg 64 :=
.mark loopBody210_52

def loopBody210_54 : HolLoopProg 64 :=
.seq loopBody210_47 loopBody210_53

def loopBody210_55 : HolLoopProg 64 :=
.mark loopBody210_54

def loopBody210_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 5#64),
      Flapjack.HolLoopExp.const 32#64])

def loopBody210_57 : HolLoopProg 64 :=
.mark loopBody210_56

def loopBody210_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody210_59 : HolLoopProg 64 :=
.mark loopBody210_58

def loopBody210_60 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody210_59, loopBody210_13, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody210_61 : HolLoopProg 64 :=
.mark loopBody210_60

def loopBody210_62 : HolLoopProg 64 :=
.seq loopBody210_61 loopBody210_13

def loopBody210_63 : HolLoopProg 64 :=
.mark loopBody210_62

def loopBody210_64 : HolLoopProg 64 :=
.seq loopBody210_57 loopBody210_63

def loopBody210_65 : HolLoopProg 64 :=
.mark loopBody210_64

def loopBody210_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody210_67 : HolLoopProg 64 :=
.mark loopBody210_66

def loopBody210_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody210_69 : HolLoopProg 64 :=
.mark loopBody210_68

def loopBody210_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody210_71 : HolLoopProg 64 :=
.mark loopBody210_70

def loopBody210_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody210_73 : HolLoopProg 64 :=
.mark loopBody210_72

def loopBody210_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody210_75 : HolLoopProg 64 :=
.mark loopBody210_74

def loopBody210_76 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 6 (Flapjack.RegImm.reg 7) loopBody210_73 loopBody210_75 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody210_77 : HolLoopProg 64 :=
.mark loopBody210_76

def loopBody210_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody210_79 : HolLoopProg 64 :=
.mark loopBody210_78

def loopBody210_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody210_81 : HolLoopProg 64 :=
.mark loopBody210_80

def loopBody210_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody210_83 : HolLoopProg 64 :=
.mark loopBody210_82

def loopBody210_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody210_85 : HolLoopProg 64 :=
.mark loopBody210_84

def loopBody210_86 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 270) ([6, 7]) (some (6, loopBody210_85, loopBody210_13, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody210_87 : HolLoopProg 64 :=
.mark loopBody210_86

def loopBody210_88 : HolLoopProg 64 :=
.seq loopBody210_87 loopBody210_13

def loopBody210_89 : HolLoopProg 64 :=
.mark loopBody210_88

def loopBody210_90 : HolLoopProg 64 :=
.seq loopBody210_83 loopBody210_89

def loopBody210_91 : HolLoopProg 64 :=
.mark loopBody210_90

def loopBody210_92 : HolLoopProg 64 :=
.seq loopBody210_81 loopBody210_91

def loopBody210_93 : HolLoopProg 64 :=
.mark loopBody210_92

def loopBody210_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 2,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 3#64)])

def loopBody210_95 : HolLoopProg 64 :=
.mark loopBody210_94

def loopBody210_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody210_97 : HolLoopProg 64 :=
.mark loopBody210_96

def loopBody210_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody210_99 : HolLoopProg 64 :=
.mark loopBody210_98

def loopBody210_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 6) 8

def loopBody210_101 : HolLoopProg 64 :=
.mark loopBody210_100

def loopBody210_102 : HolLoopProg 64 :=
.seq loopBody210_101 loopBody210_13

def loopBody210_103 : HolLoopProg 64 :=
.mark loopBody210_102

def loopBody210_104 : HolLoopProg 64 :=
.seq loopBody210_99 loopBody210_103

def loopBody210_105 : HolLoopProg 64 :=
.mark loopBody210_104

def loopBody210_106 : HolLoopProg 64 :=
.seq loopBody210_105 loopBody210_13

def loopBody210_107 : HolLoopProg 64 :=
.mark loopBody210_106

def loopBody210_108 : HolLoopProg 64 :=
.seq loopBody210_97 loopBody210_107

def loopBody210_109 : HolLoopProg 64 :=
.mark loopBody210_108

def loopBody210_110 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_109

def loopBody210_111 : HolLoopProg 64 :=
.mark loopBody210_110

def loopBody210_112 : HolLoopProg 64 :=
.seq loopBody210_95 loopBody210_111

def loopBody210_113 : HolLoopProg 64 :=
.mark loopBody210_112

def loopBody210_114 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_113

def loopBody210_115 : HolLoopProg 64 :=
.mark loopBody210_114

def loopBody210_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody210_117 : HolLoopProg 64 :=
.mark loopBody210_116

def loopBody210_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 0,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody210_119 : HolLoopProg 64 :=
.mark loopBody210_118

def loopBody210_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 3,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)])

def loopBody210_121 : HolLoopProg 64 :=
.mark loopBody210_120

def loopBody210_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody210_123 : HolLoopProg 64 :=
.mark loopBody210_122

def loopBody210_124 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 158) ([7, 8, 9]) (some (7, loopBody210_123, loopBody210_13, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody210_125 : HolLoopProg 64 :=
.mark loopBody210_124

def loopBody210_126 : HolLoopProg 64 :=
.seq loopBody210_125 loopBody210_13

def loopBody210_127 : HolLoopProg 64 :=
.mark loopBody210_126

def loopBody210_128 : HolLoopProg 64 :=
.seq loopBody210_121 loopBody210_127

def loopBody210_129 : HolLoopProg 64 :=
.mark loopBody210_128

def loopBody210_130 : HolLoopProg 64 :=
.seq loopBody210_119 loopBody210_129

def loopBody210_131 : HolLoopProg 64 :=
.mark loopBody210_130

def loopBody210_132 : HolLoopProg 64 :=
.seq loopBody210_117 loopBody210_131

def loopBody210_133 : HolLoopProg 64 :=
.mark loopBody210_132

def loopBody210_134 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_133

def loopBody210_135 : HolLoopProg 64 :=
.mark loopBody210_134

def loopBody210_136 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_135

def loopBody210_137 : HolLoopProg 64 :=
.mark loopBody210_136

def loopBody210_138 : HolLoopProg 64 :=
.seq loopBody210_115 loopBody210_137

def loopBody210_139 : HolLoopProg 64 :=
.mark loopBody210_138

def loopBody210_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody210_141 : HolLoopProg 64 :=
.mark loopBody210_140

def loopBody210_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 6)

def loopBody210_143 : HolLoopProg 64 :=
.mark loopBody210_142

def loopBody210_144 : HolLoopProg 64 :=
.seq loopBody210_143 loopBody210_13

def loopBody210_145 : HolLoopProg 64 :=
.mark loopBody210_144

def loopBody210_146 : HolLoopProg 64 :=
.seq loopBody210_145 loopBody210_13

def loopBody210_147 : HolLoopProg 64 :=
.mark loopBody210_146

def loopBody210_148 : HolLoopProg 64 :=
.seq loopBody210_141 loopBody210_147

def loopBody210_149 : HolLoopProg 64 :=
.mark loopBody210_148

def loopBody210_150 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_149

def loopBody210_151 : HolLoopProg 64 :=
.mark loopBody210_150

def loopBody210_152 : HolLoopProg 64 :=
.seq loopBody210_139 loopBody210_151

def loopBody210_153 : HolLoopProg 64 :=
.mark loopBody210_152

def loopBody210_154 : HolLoopProg 64 :=
.seq loopBody210_93 loopBody210_153

def loopBody210_155 : HolLoopProg 64 :=
.mark loopBody210_154

def loopBody210_156 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_155

def loopBody210_157 : HolLoopProg 64 :=
.mark loopBody210_156

def loopBody210_158 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_157

def loopBody210_159 : HolLoopProg 64 :=
.mark loopBody210_158

def loopBody210_160 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody210_161 : HolLoopProg 64 :=
.mark loopBody210_160

def loopBody210_162 : HolLoopProg 64 :=
.seq loopBody210_159 loopBody210_161

def loopBody210_163 : HolLoopProg 64 :=
.mark loopBody210_162

def loopBody210_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody210_165 : HolLoopProg 64 :=
.mark loopBody210_164

def loopBody210_166 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody210_163 loopBody210_165 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody210_167 : HolLoopProg 64 :=
.mark loopBody210_166

def loopBody210_168 : HolLoopProg 64 :=
.seq loopBody210_167 loopBody210_13

def loopBody210_169 : HolLoopProg 64 :=
.mark loopBody210_168

def loopBody210_170 : HolLoopProg 64 :=
.seq loopBody210_79 loopBody210_169

def loopBody210_171 : HolLoopProg 64 :=
.mark loopBody210_170

def loopBody210_172 : HolLoopProg 64 :=
.seq loopBody210_77 loopBody210_171

def loopBody210_173 : HolLoopProg 64 :=
.mark loopBody210_172

def loopBody210_174 : HolLoopProg 64 :=
.seq loopBody210_71 loopBody210_173

def loopBody210_175 : HolLoopProg 64 :=
.mark loopBody210_174

def loopBody210_176 : HolLoopProg 64 :=
.seq loopBody210_69 loopBody210_175

def loopBody210_177 : HolLoopProg 64 :=
.mark loopBody210_176

def loopBody210_178 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody210_177 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody210_179 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody210_180 : HolLoopProg 64 :=
.mark loopBody210_179

def loopBody210_181 : HolLoopProg 64 :=
.seq loopBody210_180 loopBody210_13

def loopBody210_182 : HolLoopProg 64 :=
.mark loopBody210_181

def loopBody210_183 : HolLoopProg 64 :=
.seq loopBody210_182 loopBody210_13

def loopBody210_184 : HolLoopProg 64 :=
.mark loopBody210_183

def loopBody210_185 : HolLoopProg 64 :=
.seq loopBody210_178 loopBody210_184

def loopBody210_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.var 2,
              Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4)
                (Flapjack.HolLoopExp.const 3#64)]),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody210_187 : HolLoopProg 64 :=
.mark loopBody210_186

def loopBody210_188 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 3,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])
        (Flapjack.HolLoopExp.const 5#64)])

def loopBody210_189 : HolLoopProg 64 :=
.mark loopBody210_188

def loopBody210_190 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 32#64)

def loopBody210_191 : HolLoopProg 64 :=
.mark loopBody210_190

def loopBody210_192 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 79) ([6, 7, 8]) (some (6, loopBody210_85, loopBody210_13, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody210_193 : HolLoopProg 64 :=
.mark loopBody210_192

def loopBody210_194 : HolLoopProg 64 :=
.seq loopBody210_193 loopBody210_13

def loopBody210_195 : HolLoopProg 64 :=
.mark loopBody210_194

def loopBody210_196 : HolLoopProg 64 :=
.seq loopBody210_191 loopBody210_195

def loopBody210_197 : HolLoopProg 64 :=
.mark loopBody210_196

def loopBody210_198 : HolLoopProg 64 :=
.seq loopBody210_189 loopBody210_197

def loopBody210_199 : HolLoopProg 64 :=
.mark loopBody210_198

def loopBody210_200 : HolLoopProg 64 :=
.seq loopBody210_187 loopBody210_199

def loopBody210_201 : HolLoopProg 64 :=
.mark loopBody210_200

def loopBody210_202 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody210_203 : HolLoopProg 64 :=
.mark loopBody210_202

def loopBody210_204 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody210_205 : HolLoopProg 64 :=
.mark loopBody210_204

def loopBody210_206 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody210_207 : HolLoopProg 64 :=
.mark loopBody210_206

def loopBody210_208 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody210_205 loopBody210_207 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody210_209 : HolLoopProg 64 :=
.mark loopBody210_208

def loopBody210_210 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody210_211 : HolLoopProg 64 :=
.mark loopBody210_210

def loopBody210_212 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 2#64)

def loopBody210_213 : HolLoopProg 64 :=
.mark loopBody210_212

def loopBody210_214 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody210_215 : HolLoopProg 64 :=
.mark loopBody210_214

def loopBody210_216 : HolLoopProg 64 :=
.seq loopBody210_215 loopBody210_13

def loopBody210_217 : HolLoopProg 64 :=
.mark loopBody210_216

def loopBody210_218 : HolLoopProg 64 :=
.seq loopBody210_217 loopBody210_13

def loopBody210_219 : HolLoopProg 64 :=
.mark loopBody210_218

def loopBody210_220 : HolLoopProg 64 :=
.seq loopBody210_213 loopBody210_219

def loopBody210_221 : HolLoopProg 64 :=
.mark loopBody210_220

def loopBody210_222 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_221

def loopBody210_223 : HolLoopProg 64 :=
.mark loopBody210_222

def loopBody210_224 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 4#64)

def loopBody210_225 : HolLoopProg 64 :=
.mark loopBody210_224

def loopBody210_226 : HolLoopProg 64 :=
.seq loopBody210_225 loopBody210_85

def loopBody210_227 : HolLoopProg 64 :=
.mark loopBody210_226

def loopBody210_228 : HolLoopProg 64 :=
.seq loopBody210_223 loopBody210_227

def loopBody210_229 : HolLoopProg 64 :=
.mark loopBody210_228

def loopBody210_230 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody210_229 loopBody210_13 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody210_231 : HolLoopProg 64 :=
.mark loopBody210_230

def loopBody210_232 : HolLoopProg 64 :=
.seq loopBody210_231 loopBody210_13

def loopBody210_233 : HolLoopProg 64 :=
.mark loopBody210_232

def loopBody210_234 : HolLoopProg 64 :=
.seq loopBody210_211 loopBody210_233

def loopBody210_235 : HolLoopProg 64 :=
.mark loopBody210_234

def loopBody210_236 : HolLoopProg 64 :=
.seq loopBody210_209 loopBody210_235

def loopBody210_237 : HolLoopProg 64 :=
.mark loopBody210_236

def loopBody210_238 : HolLoopProg 64 :=
.seq loopBody210_203 loopBody210_237

def loopBody210_239 : HolLoopProg 64 :=
.mark loopBody210_238

def loopBody210_240 : HolLoopProg 64 :=
.seq loopBody210_97 loopBody210_239

def loopBody210_241 : HolLoopProg 64 :=
.mark loopBody210_240

def loopBody210_242 : HolLoopProg 64 :=
.seq loopBody210_241 loopBody210_151

def loopBody210_243 : HolLoopProg 64 :=
.mark loopBody210_242

def loopBody210_244 : HolLoopProg 64 :=
.seq loopBody210_201 loopBody210_243

def loopBody210_245 : HolLoopProg 64 :=
.mark loopBody210_244

def loopBody210_246 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_245

def loopBody210_247 : HolLoopProg 64 :=
.mark loopBody210_246

def loopBody210_248 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_247

def loopBody210_249 : HolLoopProg 64 :=
.mark loopBody210_248

def loopBody210_250 : HolLoopProg 64 :=
.seq loopBody210_249 loopBody210_161

def loopBody210_251 : HolLoopProg 64 :=
.mark loopBody210_250

def loopBody210_252 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody210_251 loopBody210_165 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody210_253 : HolLoopProg 64 :=
.mark loopBody210_252

def loopBody210_254 : HolLoopProg 64 :=
.seq loopBody210_253 loopBody210_13

def loopBody210_255 : HolLoopProg 64 :=
.mark loopBody210_254

def loopBody210_256 : HolLoopProg 64 :=
.seq loopBody210_79 loopBody210_255

def loopBody210_257 : HolLoopProg 64 :=
.mark loopBody210_256

def loopBody210_258 : HolLoopProg 64 :=
.seq loopBody210_77 loopBody210_257

def loopBody210_259 : HolLoopProg 64 :=
.mark loopBody210_258

def loopBody210_260 : HolLoopProg 64 :=
.seq loopBody210_71 loopBody210_259

def loopBody210_261 : HolLoopProg 64 :=
.mark loopBody210_260

def loopBody210_262 : HolLoopProg 64 :=
.seq loopBody210_69 loopBody210_261

def loopBody210_263 : HolLoopProg 64 :=
.mark loopBody210_262

def loopBody210_264 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody210_263 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody210_265 : HolLoopProg 64 :=
.seq loopBody210_185 loopBody210_264

def loopBody210_266 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody210_267 : HolLoopProg 64 :=
.mark loopBody210_266

def loopBody210_268 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody210_269 : HolLoopProg 64 :=
.mark loopBody210_268

def loopBody210_270 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6]

def loopBody210_271 : HolLoopProg 64 :=
.mark loopBody210_270

def loopBody210_272 : HolLoopProg 64 :=
.seq loopBody210_271 loopBody210_13

def loopBody210_273 : HolLoopProg 64 :=
.mark loopBody210_272

def loopBody210_274 : HolLoopProg 64 :=
.seq loopBody210_269 loopBody210_273

def loopBody210_275 : HolLoopProg 64 :=
.mark loopBody210_274

def loopBody210_276 : HolLoopProg 64 :=
.seq loopBody210_267 loopBody210_275

def loopBody210_277 : HolLoopProg 64 :=
.mark loopBody210_276

def loopBody210_278 : HolLoopProg 64 :=
.seq loopBody210_265 loopBody210_277

def loopBody210_279 : HolLoopProg 64 :=
.seq loopBody210_67 loopBody210_278

def loopBody210_280 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_279

def loopBody210_281 : HolLoopProg 64 :=
.seq loopBody210_65 loopBody210_280

def loopBody210_282 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_281

def loopBody210_283 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_282

def loopBody210_284 : HolLoopProg 64 :=
.seq loopBody210_55 loopBody210_283

def loopBody210_285 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_284

def loopBody210_286 : HolLoopProg 64 :=
.seq loopBody210_13 loopBody210_285

def loopBody210_287 : HolLoopProg 64 :=
.seq loopBody210_45 loopBody210_286

def output210 : Nat × List Nat × HolLoopProg 64 :=
  (274, [0, 1], loopBody210_287)
end InitECandidate.Proofs.FrontendStages.Loop
