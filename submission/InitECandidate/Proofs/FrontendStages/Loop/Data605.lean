import InitECandidate.Proofs.FrontendStages.Loop.Translate589
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody605_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody605_1 : HolLoopProg 64 :=
.mark loopBody605_0

def loopBody605_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody605_3 : HolLoopProg 64 :=
.mark loopBody605_2

def loopBody605_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody605_5 : HolLoopProg 64 :=
.mark loopBody605_4

def loopBody605_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody605_7 : HolLoopProg 64 :=
.mark loopBody605_6

def loopBody605_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody605_9 : HolLoopProg 64 :=
.mark loopBody605_8

def loopBody605_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody605_11 : HolLoopProg 64 :=
.mark loopBody605_10

def loopBody605_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.RegImm.reg 7) loopBody605_9 loopBody605_11 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody605_13 : HolLoopProg 64 :=
.mark loopBody605_12

def loopBody605_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody605_15 : HolLoopProg 64 :=
.mark loopBody605_14

def loopBody605_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 2,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)]))

def loopBody605_17 : HolLoopProg 64 :=
.mark loopBody605_16

def loopBody605_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 2,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody605_19 : HolLoopProg 64 :=
.mark loopBody605_18

def loopBody605_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 2,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody605_21 : HolLoopProg 64 :=
.mark loopBody605_20

def loopBody605_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 2,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody605_23 : HolLoopProg 64 :=
.mark loopBody605_22

def loopBody605_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 3,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)]))

def loopBody605_25 : HolLoopProg 64 :=
.mark loopBody605_24

def loopBody605_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 3,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody605_27 : HolLoopProg 64 :=
.mark loopBody605_26

def loopBody605_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 3,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody605_29 : HolLoopProg 64 :=
.mark loopBody605_28

def loopBody605_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.var 3,
            Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody605_31 : HolLoopProg 64 :=
.mark loopBody605_30

def loopBody605_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody605_33 : HolLoopProg 64 :=
.mark loopBody605_32

def loopBody605_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 6)

def loopBody605_35 : HolLoopProg 64 :=
.mark loopBody605_34

def loopBody605_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 7)

def loopBody605_37 : HolLoopProg 64 :=
.mark loopBody605_36

def loopBody605_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 8)

def loopBody605_39 : HolLoopProg 64 :=
.mark loopBody605_38

def loopBody605_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 9)

def loopBody605_41 : HolLoopProg 64 :=
.mark loopBody605_40

def loopBody605_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 10)

def loopBody605_43 : HolLoopProg 64 :=
.mark loopBody605_42

def loopBody605_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 23 (Flapjack.HolLoopExp.var 11)

def loopBody605_45 : HolLoopProg 64 :=
.mark loopBody605_44

def loopBody605_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 24 (Flapjack.HolLoopExp.var 12)

def loopBody605_47 : HolLoopProg 64 :=
.mark loopBody605_46

def loopBody605_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 17

def loopBody605_49 : HolLoopProg 64 :=
.mark loopBody605_48

def loopBody605_50 : HolLoopProg 64 :=
.call (some
  ([13, 14, 15, 16],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 655) ([17, 18, 19, 20, 21, 22, 23, 24]) (some (17, loopBody605_49, loopBody605_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))

def loopBody605_51 : HolLoopProg 64 :=
.mark loopBody605_50

def loopBody605_52 : HolLoopProg 64 :=
.seq loopBody605_51 loopBody605_1

def loopBody605_53 : HolLoopProg 64 :=
.mark loopBody605_52

def loopBody605_54 : HolLoopProg 64 :=
.seq loopBody605_47 loopBody605_53

def loopBody605_55 : HolLoopProg 64 :=
.mark loopBody605_54

def loopBody605_56 : HolLoopProg 64 :=
.seq loopBody605_45 loopBody605_55

def loopBody605_57 : HolLoopProg 64 :=
.mark loopBody605_56

def loopBody605_58 : HolLoopProg 64 :=
.seq loopBody605_43 loopBody605_57

def loopBody605_59 : HolLoopProg 64 :=
.mark loopBody605_58

def loopBody605_60 : HolLoopProg 64 :=
.seq loopBody605_41 loopBody605_59

def loopBody605_61 : HolLoopProg 64 :=
.mark loopBody605_60

def loopBody605_62 : HolLoopProg 64 :=
.seq loopBody605_39 loopBody605_61

def loopBody605_63 : HolLoopProg 64 :=
.mark loopBody605_62

def loopBody605_64 : HolLoopProg 64 :=
.seq loopBody605_37 loopBody605_63

def loopBody605_65 : HolLoopProg 64 :=
.mark loopBody605_64

def loopBody605_66 : HolLoopProg 64 :=
.seq loopBody605_35 loopBody605_65

def loopBody605_67 : HolLoopProg 64 :=
.mark loopBody605_66

def loopBody605_68 : HolLoopProg 64 :=
.seq loopBody605_33 loopBody605_67

def loopBody605_69 : HolLoopProg 64 :=
.mark loopBody605_68

def loopBody605_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 1,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 5#64)])

def loopBody605_71 : HolLoopProg 64 :=
.mark loopBody605_70

def loopBody605_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 13)

def loopBody605_73 : HolLoopProg 64 :=
.mark loopBody605_72

def loopBody605_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 14)

def loopBody605_75 : HolLoopProg 64 :=
.mark loopBody605_74

def loopBody605_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 15)

def loopBody605_77 : HolLoopProg 64 :=
.mark loopBody605_76

def loopBody605_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 21 (Flapjack.HolLoopExp.var 16)

def loopBody605_79 : HolLoopProg 64 :=
.mark loopBody605_78

def loopBody605_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 18)

def loopBody605_81 : HolLoopProg 64 :=
.mark loopBody605_80

def loopBody605_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 17) 22

def loopBody605_83 : HolLoopProg 64 :=
.mark loopBody605_82

def loopBody605_84 : HolLoopProg 64 :=
.seq loopBody605_83 loopBody605_1

def loopBody605_85 : HolLoopProg 64 :=
.mark loopBody605_84

def loopBody605_86 : HolLoopProg 64 :=
.seq loopBody605_81 loopBody605_85

def loopBody605_87 : HolLoopProg 64 :=
.mark loopBody605_86

def loopBody605_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 19)

def loopBody605_89 : HolLoopProg 64 :=
.mark loopBody605_88

def loopBody605_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 17, Flapjack.HolLoopExp.const 8#64]) 22

def loopBody605_91 : HolLoopProg 64 :=
.mark loopBody605_90

def loopBody605_92 : HolLoopProg 64 :=
.seq loopBody605_91 loopBody605_1

def loopBody605_93 : HolLoopProg 64 :=
.mark loopBody605_92

def loopBody605_94 : HolLoopProg 64 :=
.seq loopBody605_89 loopBody605_93

def loopBody605_95 : HolLoopProg 64 :=
.mark loopBody605_94

def loopBody605_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 20)

def loopBody605_97 : HolLoopProg 64 :=
.mark loopBody605_96

def loopBody605_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 17, Flapjack.HolLoopExp.const 16#64]) 22

def loopBody605_99 : HolLoopProg 64 :=
.mark loopBody605_98

def loopBody605_100 : HolLoopProg 64 :=
.seq loopBody605_99 loopBody605_1

def loopBody605_101 : HolLoopProg 64 :=
.mark loopBody605_100

def loopBody605_102 : HolLoopProg 64 :=
.seq loopBody605_97 loopBody605_101

def loopBody605_103 : HolLoopProg 64 :=
.mark loopBody605_102

def loopBody605_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22 (Flapjack.HolLoopExp.var 21)

def loopBody605_105 : HolLoopProg 64 :=
.mark loopBody605_104

def loopBody605_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 17, Flapjack.HolLoopExp.const 24#64]) 22

def loopBody605_107 : HolLoopProg 64 :=
.mark loopBody605_106

def loopBody605_108 : HolLoopProg 64 :=
.seq loopBody605_107 loopBody605_1

def loopBody605_109 : HolLoopProg 64 :=
.mark loopBody605_108

def loopBody605_110 : HolLoopProg 64 :=
.seq loopBody605_105 loopBody605_109

def loopBody605_111 : HolLoopProg 64 :=
.mark loopBody605_110

def loopBody605_112 : HolLoopProg 64 :=
.seq loopBody605_111 loopBody605_1

def loopBody605_113 : HolLoopProg 64 :=
.mark loopBody605_112

def loopBody605_114 : HolLoopProg 64 :=
.seq loopBody605_103 loopBody605_113

def loopBody605_115 : HolLoopProg 64 :=
.mark loopBody605_114

def loopBody605_116 : HolLoopProg 64 :=
.seq loopBody605_95 loopBody605_115

def loopBody605_117 : HolLoopProg 64 :=
.mark loopBody605_116

def loopBody605_118 : HolLoopProg 64 :=
.seq loopBody605_87 loopBody605_117

def loopBody605_119 : HolLoopProg 64 :=
.mark loopBody605_118

def loopBody605_120 : HolLoopProg 64 :=
.seq loopBody605_79 loopBody605_119

def loopBody605_121 : HolLoopProg 64 :=
.mark loopBody605_120

def loopBody605_122 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_121

def loopBody605_123 : HolLoopProg 64 :=
.mark loopBody605_122

def loopBody605_124 : HolLoopProg 64 :=
.seq loopBody605_77 loopBody605_123

def loopBody605_125 : HolLoopProg 64 :=
.mark loopBody605_124

def loopBody605_126 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_125

def loopBody605_127 : HolLoopProg 64 :=
.mark loopBody605_126

def loopBody605_128 : HolLoopProg 64 :=
.seq loopBody605_75 loopBody605_127

def loopBody605_129 : HolLoopProg 64 :=
.mark loopBody605_128

def loopBody605_130 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_129

def loopBody605_131 : HolLoopProg 64 :=
.mark loopBody605_130

def loopBody605_132 : HolLoopProg 64 :=
.seq loopBody605_73 loopBody605_131

def loopBody605_133 : HolLoopProg 64 :=
.mark loopBody605_132

def loopBody605_134 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_133

def loopBody605_135 : HolLoopProg 64 :=
.mark loopBody605_134

def loopBody605_136 : HolLoopProg 64 :=
.seq loopBody605_71 loopBody605_135

def loopBody605_137 : HolLoopProg 64 :=
.mark loopBody605_136

def loopBody605_138 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_137

def loopBody605_139 : HolLoopProg 64 :=
.mark loopBody605_138

def loopBody605_140 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody605_141 : HolLoopProg 64 :=
.mark loopBody605_140

def loopBody605_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 17)

def loopBody605_143 : HolLoopProg 64 :=
.mark loopBody605_142

def loopBody605_144 : HolLoopProg 64 :=
.seq loopBody605_143 loopBody605_1

def loopBody605_145 : HolLoopProg 64 :=
.mark loopBody605_144

def loopBody605_146 : HolLoopProg 64 :=
.seq loopBody605_145 loopBody605_1

def loopBody605_147 : HolLoopProg 64 :=
.mark loopBody605_146

def loopBody605_148 : HolLoopProg 64 :=
.seq loopBody605_141 loopBody605_147

def loopBody605_149 : HolLoopProg 64 :=
.mark loopBody605_148

def loopBody605_150 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_149

def loopBody605_151 : HolLoopProg 64 :=
.mark loopBody605_150

def loopBody605_152 : HolLoopProg 64 :=
.seq loopBody605_139 loopBody605_151

def loopBody605_153 : HolLoopProg 64 :=
.mark loopBody605_152

def loopBody605_154 : HolLoopProg 64 :=
.seq loopBody605_69 loopBody605_153

def loopBody605_155 : HolLoopProg 64 :=
.mark loopBody605_154

def loopBody605_156 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_155

def loopBody605_157 : HolLoopProg 64 :=
.mark loopBody605_156

def loopBody605_158 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_157

def loopBody605_159 : HolLoopProg 64 :=
.mark loopBody605_158

def loopBody605_160 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_159

def loopBody605_161 : HolLoopProg 64 :=
.mark loopBody605_160

def loopBody605_162 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_161

def loopBody605_163 : HolLoopProg 64 :=
.mark loopBody605_162

def loopBody605_164 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_163

def loopBody605_165 : HolLoopProg 64 :=
.mark loopBody605_164

def loopBody605_166 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_165

def loopBody605_167 : HolLoopProg 64 :=
.mark loopBody605_166

def loopBody605_168 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_167

def loopBody605_169 : HolLoopProg 64 :=
.mark loopBody605_168

def loopBody605_170 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_169

def loopBody605_171 : HolLoopProg 64 :=
.mark loopBody605_170

def loopBody605_172 : HolLoopProg 64 :=
.seq loopBody605_31 loopBody605_171

def loopBody605_173 : HolLoopProg 64 :=
.mark loopBody605_172

def loopBody605_174 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_173

def loopBody605_175 : HolLoopProg 64 :=
.mark loopBody605_174

def loopBody605_176 : HolLoopProg 64 :=
.seq loopBody605_29 loopBody605_175

def loopBody605_177 : HolLoopProg 64 :=
.mark loopBody605_176

def loopBody605_178 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_177

def loopBody605_179 : HolLoopProg 64 :=
.mark loopBody605_178

def loopBody605_180 : HolLoopProg 64 :=
.seq loopBody605_27 loopBody605_179

def loopBody605_181 : HolLoopProg 64 :=
.mark loopBody605_180

def loopBody605_182 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_181

def loopBody605_183 : HolLoopProg 64 :=
.mark loopBody605_182

def loopBody605_184 : HolLoopProg 64 :=
.seq loopBody605_25 loopBody605_183

def loopBody605_185 : HolLoopProg 64 :=
.mark loopBody605_184

def loopBody605_186 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_185

def loopBody605_187 : HolLoopProg 64 :=
.mark loopBody605_186

def loopBody605_188 : HolLoopProg 64 :=
.seq loopBody605_23 loopBody605_187

def loopBody605_189 : HolLoopProg 64 :=
.mark loopBody605_188

def loopBody605_190 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_189

def loopBody605_191 : HolLoopProg 64 :=
.mark loopBody605_190

def loopBody605_192 : HolLoopProg 64 :=
.seq loopBody605_21 loopBody605_191

def loopBody605_193 : HolLoopProg 64 :=
.mark loopBody605_192

def loopBody605_194 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_193

def loopBody605_195 : HolLoopProg 64 :=
.mark loopBody605_194

def loopBody605_196 : HolLoopProg 64 :=
.seq loopBody605_19 loopBody605_195

def loopBody605_197 : HolLoopProg 64 :=
.mark loopBody605_196

def loopBody605_198 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_197

def loopBody605_199 : HolLoopProg 64 :=
.mark loopBody605_198

def loopBody605_200 : HolLoopProg 64 :=
.seq loopBody605_17 loopBody605_199

def loopBody605_201 : HolLoopProg 64 :=
.mark loopBody605_200

def loopBody605_202 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_201

def loopBody605_203 : HolLoopProg 64 :=
.mark loopBody605_202

def loopBody605_204 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody605_205 : HolLoopProg 64 :=
.mark loopBody605_204

def loopBody605_206 : HolLoopProg 64 :=
.seq loopBody605_203 loopBody605_205

def loopBody605_207 : HolLoopProg 64 :=
.mark loopBody605_206

def loopBody605_208 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody605_209 : HolLoopProg 64 :=
.mark loopBody605_208

def loopBody605_210 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody605_207 loopBody605_209 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody605_211 : HolLoopProg 64 :=
.mark loopBody605_210

def loopBody605_212 : HolLoopProg 64 :=
.seq loopBody605_211 loopBody605_1

def loopBody605_213 : HolLoopProg 64 :=
.mark loopBody605_212

def loopBody605_214 : HolLoopProg 64 :=
.seq loopBody605_15 loopBody605_213

def loopBody605_215 : HolLoopProg 64 :=
.mark loopBody605_214

def loopBody605_216 : HolLoopProg 64 :=
.seq loopBody605_13 loopBody605_215

def loopBody605_217 : HolLoopProg 64 :=
.mark loopBody605_216

def loopBody605_218 : HolLoopProg 64 :=
.seq loopBody605_7 loopBody605_217

def loopBody605_219 : HolLoopProg 64 :=
.mark loopBody605_218

def loopBody605_220 : HolLoopProg 64 :=
.seq loopBody605_5 loopBody605_219

def loopBody605_221 : HolLoopProg 64 :=
.mark loopBody605_220

def loopBody605_222 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody605_221 (Flapjack.Spt.ln)

def loopBody605_223 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody605_224 : HolLoopProg 64 :=
.mark loopBody605_223

def loopBody605_225 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody605_226 : HolLoopProg 64 :=
.mark loopBody605_225

def loopBody605_227 : HolLoopProg 64 :=
.seq loopBody605_226 loopBody605_1

def loopBody605_228 : HolLoopProg 64 :=
.mark loopBody605_227

def loopBody605_229 : HolLoopProg 64 :=
.seq loopBody605_224 loopBody605_228

def loopBody605_230 : HolLoopProg 64 :=
.mark loopBody605_229

def loopBody605_231 : HolLoopProg 64 :=
.seq loopBody605_222 loopBody605_230

def loopBody605_232 : HolLoopProg 64 :=
.seq loopBody605_3 loopBody605_231

def loopBody605_233 : HolLoopProg 64 :=
.seq loopBody605_1 loopBody605_232

def output605 : Nat × List Nat × HolLoopProg 64 :=
  (669, [0, 1, 2, 3], loopBody605_233)
end InitECandidate.Proofs.FrontendStages.Loop
