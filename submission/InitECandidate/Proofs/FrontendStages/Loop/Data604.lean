import InitECandidate.Proofs.FrontendStages.Loop.Translate588
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody604_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody604_1 : HolLoopProg 64 :=
.mark loopBody604_0

def loopBody604_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody604_3 : HolLoopProg 64 :=
.mark loopBody604_2

def loopBody604_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody604_5 : HolLoopProg 64 :=
.mark loopBody604_4

def loopBody604_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody604_7 : HolLoopProg 64 :=
.mark loopBody604_6

def loopBody604_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody604_9 : HolLoopProg 64 :=
.mark loopBody604_8

def loopBody604_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody604_11 : HolLoopProg 64 :=
.mark loopBody604_10

def loopBody604_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.RegImm.reg 7) loopBody604_9 loopBody604_11 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody604_13 : HolLoopProg 64 :=
.mark loopBody604_12

def loopBody604_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody604_15 : HolLoopProg 64 :=
.mark loopBody604_14

def loopBody604_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 2,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)]))

def loopBody604_17 : HolLoopProg 64 :=
.mark loopBody604_16

def loopBody604_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 2,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody604_19 : HolLoopProg 64 :=
.mark loopBody604_18

def loopBody604_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 2,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody604_21 : HolLoopProg 64 :=
.mark loopBody604_20

def loopBody604_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 2,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody604_23 : HolLoopProg 64 :=
.mark loopBody604_22

def loopBody604_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 3,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)]))

def loopBody604_25 : HolLoopProg 64 :=
.mark loopBody604_24

def loopBody604_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 3,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody604_27 : HolLoopProg 64 :=
.mark loopBody604_26

def loopBody604_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 3,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody604_29 : HolLoopProg 64 :=
.mark loopBody604_28

def loopBody604_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 3,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody604_31 : HolLoopProg 64 :=
.mark loopBody604_30

def loopBody604_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody604_33 : HolLoopProg 64 :=
.mark loopBody604_32

def loopBody604_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 6)

def loopBody604_35 : HolLoopProg 64 :=
.mark loopBody604_34

def loopBody604_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 7)

def loopBody604_37 : HolLoopProg 64 :=
.mark loopBody604_36

def loopBody604_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 8)

def loopBody604_39 : HolLoopProg 64 :=
.mark loopBody604_38

def loopBody604_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 9)

def loopBody604_41 : HolLoopProg 64 :=
.mark loopBody604_40

def loopBody604_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 10)

def loopBody604_43 : HolLoopProg 64 :=
.mark loopBody604_42

def loopBody604_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 23 (Flapjack.HolLoopExp.var 11)

def loopBody604_45 : HolLoopProg 64 :=
.mark loopBody604_44

def loopBody604_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 24 (Flapjack.HolLoopExp.var 12)

def loopBody604_47 : HolLoopProg 64 :=
.mark loopBody604_46

def loopBody604_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 17

def loopBody604_49 : HolLoopProg 64 :=
.mark loopBody604_48

def loopBody604_50 : HolLoopProg 64 :=
.call (some
  ([13, 14, 15, 16],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 654) ([17, 18, 19, 20, 21, 22, 23, 24]) (some (17, loopBody604_49, loopBody604_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))

def loopBody604_51 : HolLoopProg 64 :=
.mark loopBody604_50

def loopBody604_52 : HolLoopProg 64 :=
.seq loopBody604_51 loopBody604_1

def loopBody604_53 : HolLoopProg 64 :=
.mark loopBody604_52

def loopBody604_54 : HolLoopProg 64 :=
.seq loopBody604_47 loopBody604_53

def loopBody604_55 : HolLoopProg 64 :=
.mark loopBody604_54

def loopBody604_56 : HolLoopProg 64 :=
.seq loopBody604_45 loopBody604_55

def loopBody604_57 : HolLoopProg 64 :=
.mark loopBody604_56

def loopBody604_58 : HolLoopProg 64 :=
.seq loopBody604_43 loopBody604_57

def loopBody604_59 : HolLoopProg 64 :=
.mark loopBody604_58

def loopBody604_60 : HolLoopProg 64 :=
.seq loopBody604_41 loopBody604_59

def loopBody604_61 : HolLoopProg 64 :=
.mark loopBody604_60

def loopBody604_62 : HolLoopProg 64 :=
.seq loopBody604_39 loopBody604_61

def loopBody604_63 : HolLoopProg 64 :=
.mark loopBody604_62

def loopBody604_64 : HolLoopProg 64 :=
.seq loopBody604_37 loopBody604_63

def loopBody604_65 : HolLoopProg 64 :=
.mark loopBody604_64

def loopBody604_66 : HolLoopProg 64 :=
.seq loopBody604_35 loopBody604_65

def loopBody604_67 : HolLoopProg 64 :=
.mark loopBody604_66

def loopBody604_68 : HolLoopProg 64 :=
.seq loopBody604_33 loopBody604_67

def loopBody604_69 : HolLoopProg 64 :=
.mark loopBody604_68

def loopBody604_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 1,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)])

def loopBody604_71 : HolLoopProg 64 :=
.mark loopBody604_70

def loopBody604_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 13)

def loopBody604_73 : HolLoopProg 64 :=
.mark loopBody604_72

def loopBody604_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 14)

def loopBody604_75 : HolLoopProg 64 :=
.mark loopBody604_74

def loopBody604_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 15)

def loopBody604_77 : HolLoopProg 64 :=
.mark loopBody604_76

def loopBody604_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 16)

def loopBody604_79 : HolLoopProg 64 :=
.mark loopBody604_78

def loopBody604_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 18)

def loopBody604_81 : HolLoopProg 64 :=
.mark loopBody604_80

def loopBody604_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 17) 22

def loopBody604_83 : HolLoopProg 64 :=
.mark loopBody604_82

def loopBody604_84 : HolLoopProg 64 :=
.seq loopBody604_83 loopBody604_1

def loopBody604_85 : HolLoopProg 64 :=
.mark loopBody604_84

def loopBody604_86 : HolLoopProg 64 :=
.seq loopBody604_81 loopBody604_85

def loopBody604_87 : HolLoopProg 64 :=
.mark loopBody604_86

def loopBody604_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 19)

def loopBody604_89 : HolLoopProg 64 :=
.mark loopBody604_88

def loopBody604_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 17, Flapjack.HolLoopExp.const 8#64]) 22

def loopBody604_91 : HolLoopProg 64 :=
.mark loopBody604_90

def loopBody604_92 : HolLoopProg 64 :=
.seq loopBody604_91 loopBody604_1

def loopBody604_93 : HolLoopProg 64 :=
.mark loopBody604_92

def loopBody604_94 : HolLoopProg 64 :=
.seq loopBody604_89 loopBody604_93

def loopBody604_95 : HolLoopProg 64 :=
.mark loopBody604_94

def loopBody604_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 20)

def loopBody604_97 : HolLoopProg 64 :=
.mark loopBody604_96

def loopBody604_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 17, Flapjack.HolLoopExp.const 16#64]) 22

def loopBody604_99 : HolLoopProg 64 :=
.mark loopBody604_98

def loopBody604_100 : HolLoopProg 64 :=
.seq loopBody604_99 loopBody604_1

def loopBody604_101 : HolLoopProg 64 :=
.mark loopBody604_100

def loopBody604_102 : HolLoopProg 64 :=
.seq loopBody604_97 loopBody604_101

def loopBody604_103 : HolLoopProg 64 :=
.mark loopBody604_102

def loopBody604_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 21)

def loopBody604_105 : HolLoopProg 64 :=
.mark loopBody604_104

def loopBody604_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 17, Flapjack.HolLoopExp.const 24#64]) 22

def loopBody604_107 : HolLoopProg 64 :=
.mark loopBody604_106

def loopBody604_108 : HolLoopProg 64 :=
.seq loopBody604_107 loopBody604_1

def loopBody604_109 : HolLoopProg 64 :=
.mark loopBody604_108

def loopBody604_110 : HolLoopProg 64 :=
.seq loopBody604_105 loopBody604_109

def loopBody604_111 : HolLoopProg 64 :=
.mark loopBody604_110

def loopBody604_112 : HolLoopProg 64 :=
.seq loopBody604_111 loopBody604_1

def loopBody604_113 : HolLoopProg 64 :=
.mark loopBody604_112

def loopBody604_114 : HolLoopProg 64 :=
.seq loopBody604_103 loopBody604_113

def loopBody604_115 : HolLoopProg 64 :=
.mark loopBody604_114

def loopBody604_116 : HolLoopProg 64 :=
.seq loopBody604_95 loopBody604_115

def loopBody604_117 : HolLoopProg 64 :=
.mark loopBody604_116

def loopBody604_118 : HolLoopProg 64 :=
.seq loopBody604_87 loopBody604_117

def loopBody604_119 : HolLoopProg 64 :=
.mark loopBody604_118

def loopBody604_120 : HolLoopProg 64 :=
.seq loopBody604_79 loopBody604_119

def loopBody604_121 : HolLoopProg 64 :=
.mark loopBody604_120

def loopBody604_122 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_121

def loopBody604_123 : HolLoopProg 64 :=
.mark loopBody604_122

def loopBody604_124 : HolLoopProg 64 :=
.seq loopBody604_77 loopBody604_123

def loopBody604_125 : HolLoopProg 64 :=
.mark loopBody604_124

def loopBody604_126 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_125

def loopBody604_127 : HolLoopProg 64 :=
.mark loopBody604_126

def loopBody604_128 : HolLoopProg 64 :=
.seq loopBody604_75 loopBody604_127

def loopBody604_129 : HolLoopProg 64 :=
.mark loopBody604_128

def loopBody604_130 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_129

def loopBody604_131 : HolLoopProg 64 :=
.mark loopBody604_130

def loopBody604_132 : HolLoopProg 64 :=
.seq loopBody604_73 loopBody604_131

def loopBody604_133 : HolLoopProg 64 :=
.mark loopBody604_132

def loopBody604_134 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_133

def loopBody604_135 : HolLoopProg 64 :=
.mark loopBody604_134

def loopBody604_136 : HolLoopProg 64 :=
.seq loopBody604_71 loopBody604_135

def loopBody604_137 : HolLoopProg 64 :=
.mark loopBody604_136

def loopBody604_138 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_137

def loopBody604_139 : HolLoopProg 64 :=
.mark loopBody604_138

def loopBody604_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody604_141 : HolLoopProg 64 :=
.mark loopBody604_140

def loopBody604_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 17)

def loopBody604_143 : HolLoopProg 64 :=
.mark loopBody604_142

def loopBody604_144 : HolLoopProg 64 :=
.seq loopBody604_143 loopBody604_1

def loopBody604_145 : HolLoopProg 64 :=
.mark loopBody604_144

def loopBody604_146 : HolLoopProg 64 :=
.seq loopBody604_145 loopBody604_1

def loopBody604_147 : HolLoopProg 64 :=
.mark loopBody604_146

def loopBody604_148 : HolLoopProg 64 :=
.seq loopBody604_141 loopBody604_147

def loopBody604_149 : HolLoopProg 64 :=
.mark loopBody604_148

def loopBody604_150 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_149

def loopBody604_151 : HolLoopProg 64 :=
.mark loopBody604_150

def loopBody604_152 : HolLoopProg 64 :=
.seq loopBody604_139 loopBody604_151

def loopBody604_153 : HolLoopProg 64 :=
.mark loopBody604_152

def loopBody604_154 : HolLoopProg 64 :=
.seq loopBody604_69 loopBody604_153

def loopBody604_155 : HolLoopProg 64 :=
.mark loopBody604_154

def loopBody604_156 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_155

def loopBody604_157 : HolLoopProg 64 :=
.mark loopBody604_156

def loopBody604_158 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_157

def loopBody604_159 : HolLoopProg 64 :=
.mark loopBody604_158

def loopBody604_160 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_159

def loopBody604_161 : HolLoopProg 64 :=
.mark loopBody604_160

def loopBody604_162 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_161

def loopBody604_163 : HolLoopProg 64 :=
.mark loopBody604_162

def loopBody604_164 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_163

def loopBody604_165 : HolLoopProg 64 :=
.mark loopBody604_164

def loopBody604_166 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_165

def loopBody604_167 : HolLoopProg 64 :=
.mark loopBody604_166

def loopBody604_168 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_167

def loopBody604_169 : HolLoopProg 64 :=
.mark loopBody604_168

def loopBody604_170 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_169

def loopBody604_171 : HolLoopProg 64 :=
.mark loopBody604_170

def loopBody604_172 : HolLoopProg 64 :=
.seq loopBody604_31 loopBody604_171

def loopBody604_173 : HolLoopProg 64 :=
.mark loopBody604_172

def loopBody604_174 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_173

def loopBody604_175 : HolLoopProg 64 :=
.mark loopBody604_174

def loopBody604_176 : HolLoopProg 64 :=
.seq loopBody604_29 loopBody604_175

def loopBody604_177 : HolLoopProg 64 :=
.mark loopBody604_176

def loopBody604_178 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_177

def loopBody604_179 : HolLoopProg 64 :=
.mark loopBody604_178

def loopBody604_180 : HolLoopProg 64 :=
.seq loopBody604_27 loopBody604_179

def loopBody604_181 : HolLoopProg 64 :=
.mark loopBody604_180

def loopBody604_182 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_181

def loopBody604_183 : HolLoopProg 64 :=
.mark loopBody604_182

def loopBody604_184 : HolLoopProg 64 :=
.seq loopBody604_25 loopBody604_183

def loopBody604_185 : HolLoopProg 64 :=
.mark loopBody604_184

def loopBody604_186 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_185

def loopBody604_187 : HolLoopProg 64 :=
.mark loopBody604_186

def loopBody604_188 : HolLoopProg 64 :=
.seq loopBody604_23 loopBody604_187

def loopBody604_189 : HolLoopProg 64 :=
.mark loopBody604_188

def loopBody604_190 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_189

def loopBody604_191 : HolLoopProg 64 :=
.mark loopBody604_190

def loopBody604_192 : HolLoopProg 64 :=
.seq loopBody604_21 loopBody604_191

def loopBody604_193 : HolLoopProg 64 :=
.mark loopBody604_192

def loopBody604_194 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_193

def loopBody604_195 : HolLoopProg 64 :=
.mark loopBody604_194

def loopBody604_196 : HolLoopProg 64 :=
.seq loopBody604_19 loopBody604_195

def loopBody604_197 : HolLoopProg 64 :=
.mark loopBody604_196

def loopBody604_198 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_197

def loopBody604_199 : HolLoopProg 64 :=
.mark loopBody604_198

def loopBody604_200 : HolLoopProg 64 :=
.seq loopBody604_17 loopBody604_199

def loopBody604_201 : HolLoopProg 64 :=
.mark loopBody604_200

def loopBody604_202 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_201

def loopBody604_203 : HolLoopProg 64 :=
.mark loopBody604_202

def loopBody604_204 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody604_205 : HolLoopProg 64 :=
.mark loopBody604_204

def loopBody604_206 : HolLoopProg 64 :=
.seq loopBody604_203 loopBody604_205

def loopBody604_207 : HolLoopProg 64 :=
.mark loopBody604_206

def loopBody604_208 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody604_209 : HolLoopProg 64 :=
.mark loopBody604_208

def loopBody604_210 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody604_207 loopBody604_209 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody604_211 : HolLoopProg 64 :=
.mark loopBody604_210

def loopBody604_212 : HolLoopProg 64 :=
.seq loopBody604_211 loopBody604_1

def loopBody604_213 : HolLoopProg 64 :=
.mark loopBody604_212

def loopBody604_214 : HolLoopProg 64 :=
.seq loopBody604_15 loopBody604_213

def loopBody604_215 : HolLoopProg 64 :=
.mark loopBody604_214

def loopBody604_216 : HolLoopProg 64 :=
.seq loopBody604_13 loopBody604_215

def loopBody604_217 : HolLoopProg 64 :=
.mark loopBody604_216

def loopBody604_218 : HolLoopProg 64 :=
.seq loopBody604_7 loopBody604_217

def loopBody604_219 : HolLoopProg 64 :=
.mark loopBody604_218

def loopBody604_220 : HolLoopProg 64 :=
.seq loopBody604_5 loopBody604_219

def loopBody604_221 : HolLoopProg 64 :=
.mark loopBody604_220

def loopBody604_222 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody604_221 (Flapjack.Spt.ln)

def loopBody604_223 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody604_224 : HolLoopProg 64 :=
.mark loopBody604_223

def loopBody604_225 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody604_226 : HolLoopProg 64 :=
.mark loopBody604_225

def loopBody604_227 : HolLoopProg 64 :=
.seq loopBody604_226 loopBody604_1

def loopBody604_228 : HolLoopProg 64 :=
.mark loopBody604_227

def loopBody604_229 : HolLoopProg 64 :=
.seq loopBody604_224 loopBody604_228

def loopBody604_230 : HolLoopProg 64 :=
.mark loopBody604_229

def loopBody604_231 : HolLoopProg 64 :=
.seq loopBody604_222 loopBody604_230

def loopBody604_232 : HolLoopProg 64 :=
.seq loopBody604_3 loopBody604_231

def loopBody604_233 : HolLoopProg 64 :=
.seq loopBody604_1 loopBody604_232

def output604 : Nat × List Nat × HolLoopProg 64 :=
  (668, [0, 1, 2, 3], loopBody604_233)
end InitECandidate.Proofs.FrontendStages.Loop
