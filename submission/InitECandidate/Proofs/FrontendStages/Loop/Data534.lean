import InitECandidate.Proofs.FrontendStages.Loop.Translate518
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody534_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody534_1 : HolLoopProg 64 :=
.mark loopBody534_0

def loopBody534_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1#64)

def loopBody534_3 : HolLoopProg 64 :=
.mark loopBody534_2

def loopBody534_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody534_5 : HolLoopProg 64 :=
.mark loopBody534_4

def loopBody534_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody534_7 : HolLoopProg 64 :=
.mark loopBody534_6

def loopBody534_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody534_9 : HolLoopProg 64 :=
.mark loopBody534_8

def loopBody534_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody534_11 : HolLoopProg 64 :=
.mark loopBody534_10

def loopBody534_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody534_9 loopBody534_11 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody534_13 : HolLoopProg 64 :=
.mark loopBody534_12

def loopBody534_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody534_15 : HolLoopProg 64 :=
.mark loopBody534_14

def loopBody534_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody534_17 : HolLoopProg 64 :=
.mark loopBody534_16

def loopBody534_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 288#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody534_19 : HolLoopProg 64 :=
.mark loopBody534_18

def loopBody534_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody534_21 : HolLoopProg 64 :=
.mark loopBody534_20

def loopBody534_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody534_23 : HolLoopProg 64 :=
.mark loopBody534_22

def loopBody534_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody534_23 loopBody534_7 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody534_25 : HolLoopProg 64 :=
.mark loopBody534_24

def loopBody534_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody534_27 : HolLoopProg 64 :=
.mark loopBody534_26

def loopBody534_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody534_29 : HolLoopProg 64 :=
.mark loopBody534_28

def loopBody534_30 : HolLoopProg 64 :=
.seq loopBody534_29 loopBody534_1

def loopBody534_31 : HolLoopProg 64 :=
.mark loopBody534_30

def loopBody534_32 : HolLoopProg 64 :=
.seq loopBody534_31 loopBody534_1

def loopBody534_33 : HolLoopProg 64 :=
.mark loopBody534_32

def loopBody534_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 104#64]))

def loopBody534_35 : HolLoopProg 64 :=
.mark loopBody534_34

def loopBody534_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody534_23 loopBody534_7 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody534_37 : HolLoopProg 64 :=
.mark loopBody534_36

def loopBody534_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 0#64]))

def loopBody534_39 : HolLoopProg 64 :=
.mark loopBody534_38

def loopBody534_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 56#64]))

def loopBody534_41 : HolLoopProg 64 :=
.mark loopBody534_40

def loopBody534_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody534_43 : HolLoopProg 64 :=
.mark loopBody534_42

def loopBody534_44 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 5 (Flapjack.RegImm.reg 6) loopBody534_43 loopBody534_21 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody534_45 : HolLoopProg 64 :=
.mark loopBody534_44

def loopBody534_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody534_47 : HolLoopProg 64 :=
.mark loopBody534_46

def loopBody534_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 48#64]),
      Flapjack.HolLoopExp.var 3])

def loopBody534_49 : HolLoopProg 64 :=
.mark loopBody534_48

def loopBody534_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.loadByte 6 6

def loopBody534_51 : HolLoopProg 64 :=
.mark loopBody534_50

def loopBody534_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody534_53 : HolLoopProg 64 :=
.mark loopBody534_52

def loopBody534_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody534_55 : HolLoopProg 64 :=
.mark loopBody534_54

def loopBody534_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody534_57 : HolLoopProg 64 :=
.mark loopBody534_56

def loopBody534_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody534_59 : HolLoopProg 64 :=
.mark loopBody534_58

def loopBody534_60 : HolLoopProg 64 :=
.seq loopBody534_59 loopBody534_1

def loopBody534_61 : HolLoopProg 64 :=
.mark loopBody534_60

def loopBody534_62 : HolLoopProg 64 :=
.seq loopBody534_61 loopBody534_1

def loopBody534_63 : HolLoopProg 64 :=
.mark loopBody534_62

def loopBody534_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody534_65 : HolLoopProg 64 :=
.mark loopBody534_64

def loopBody534_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody534_67 : HolLoopProg 64 :=
.mark loopBody534_66

def loopBody534_68 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 593) ([7]) (some (7, loopBody534_67, loopBody534_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody534_69 : HolLoopProg 64 :=
.mark loopBody534_68

def loopBody534_70 : HolLoopProg 64 :=
.seq loopBody534_69 loopBody534_1

def loopBody534_71 : HolLoopProg 64 :=
.mark loopBody534_70

def loopBody534_72 : HolLoopProg 64 :=
.seq loopBody534_65 loopBody534_71

def loopBody534_73 : HolLoopProg 64 :=
.mark loopBody534_72

def loopBody534_74 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_73

def loopBody534_75 : HolLoopProg 64 :=
.mark loopBody534_74

def loopBody534_76 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_75

def loopBody534_77 : HolLoopProg 64 :=
.mark loopBody534_76

def loopBody534_78 : HolLoopProg 64 :=
.seq loopBody534_63 loopBody534_77

def loopBody534_79 : HolLoopProg 64 :=
.mark loopBody534_78

def loopBody534_80 : HolLoopProg 64 :=
.seq loopBody534_57 loopBody534_79

def loopBody534_81 : HolLoopProg 64 :=
.mark loopBody534_80

def loopBody534_82 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 8#64) loopBody534_55 loopBody534_81 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody534_83 : HolLoopProg 64 :=
.mark loopBody534_82

def loopBody534_84 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 591) ([7]) (some (6, loopBody534_83, loopBody534_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody534_85 : HolLoopProg 64 :=
.mark loopBody534_84

def loopBody534_86 : HolLoopProg 64 :=
.seq loopBody534_85 loopBody534_1

def loopBody534_87 : HolLoopProg 64 :=
.mark loopBody534_86

def loopBody534_88 : HolLoopProg 64 :=
.seq loopBody534_53 loopBody534_87

def loopBody534_89 : HolLoopProg 64 :=
.mark loopBody534_88

def loopBody534_90 : HolLoopProg 64 :=
.seq loopBody534_51 loopBody534_89

def loopBody534_91 : HolLoopProg 64 :=
.mark loopBody534_90

def loopBody534_92 : HolLoopProg 64 :=
.seq loopBody534_49 loopBody534_91

def loopBody534_93 : HolLoopProg 64 :=
.mark loopBody534_92

def loopBody534_94 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_93

def loopBody534_95 : HolLoopProg 64 :=
.mark loopBody534_94

def loopBody534_96 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_95

def loopBody534_97 : HolLoopProg 64 :=
.mark loopBody534_96

def loopBody534_98 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_97

def loopBody534_99 : HolLoopProg 64 :=
.mark loopBody534_98

def loopBody534_100 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_99

def loopBody534_101 : HolLoopProg 64 :=
.mark loopBody534_100

def loopBody534_102 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody534_33 loopBody534_101 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody534_103 : HolLoopProg 64 :=
.mark loopBody534_102

def loopBody534_104 : HolLoopProg 64 :=
.seq loopBody534_103 loopBody534_1

def loopBody534_105 : HolLoopProg 64 :=
.mark loopBody534_104

def loopBody534_106 : HolLoopProg 64 :=
.seq loopBody534_47 loopBody534_105

def loopBody534_107 : HolLoopProg 64 :=
.mark loopBody534_106

def loopBody534_108 : HolLoopProg 64 :=
.seq loopBody534_45 loopBody534_107

def loopBody534_109 : HolLoopProg 64 :=
.mark loopBody534_108

def loopBody534_110 : HolLoopProg 64 :=
.seq loopBody534_41 loopBody534_109

def loopBody534_111 : HolLoopProg 64 :=
.mark loopBody534_110

def loopBody534_112 : HolLoopProg 64 :=
.seq loopBody534_15 loopBody534_111

def loopBody534_113 : HolLoopProg 64 :=
.mark loopBody534_112

def loopBody534_114 : HolLoopProg 64 :=
.seq loopBody534_39 loopBody534_113

def loopBody534_115 : HolLoopProg 64 :=
.mark loopBody534_114

def loopBody534_116 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_115

def loopBody534_117 : HolLoopProg 64 :=
.mark loopBody534_116

def loopBody534_118 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody534_33 loopBody534_117 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody534_119 : HolLoopProg 64 :=
.mark loopBody534_118

def loopBody534_120 : HolLoopProg 64 :=
.seq loopBody534_119 loopBody534_1

def loopBody534_121 : HolLoopProg 64 :=
.mark loopBody534_120

def loopBody534_122 : HolLoopProg 64 :=
.seq loopBody534_27 loopBody534_121

def loopBody534_123 : HolLoopProg 64 :=
.mark loopBody534_122

def loopBody534_124 : HolLoopProg 64 :=
.seq loopBody534_37 loopBody534_123

def loopBody534_125 : HolLoopProg 64 :=
.mark loopBody534_124

def loopBody534_126 : HolLoopProg 64 :=
.seq loopBody534_21 loopBody534_125

def loopBody534_127 : HolLoopProg 64 :=
.mark loopBody534_126

def loopBody534_128 : HolLoopProg 64 :=
.seq loopBody534_35 loopBody534_127

def loopBody534_129 : HolLoopProg 64 :=
.mark loopBody534_128

def loopBody534_130 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody534_33 loopBody534_129 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))

def loopBody534_131 : HolLoopProg 64 :=
.mark loopBody534_130

def loopBody534_132 : HolLoopProg 64 :=
.seq loopBody534_131 loopBody534_1

def loopBody534_133 : HolLoopProg 64 :=
.mark loopBody534_132

def loopBody534_134 : HolLoopProg 64 :=
.seq loopBody534_27 loopBody534_133

def loopBody534_135 : HolLoopProg 64 :=
.mark loopBody534_134

def loopBody534_136 : HolLoopProg 64 :=
.seq loopBody534_25 loopBody534_135

def loopBody534_137 : HolLoopProg 64 :=
.mark loopBody534_136

def loopBody534_138 : HolLoopProg 64 :=
.seq loopBody534_21 loopBody534_137

def loopBody534_139 : HolLoopProg 64 :=
.mark loopBody534_138

def loopBody534_140 : HolLoopProg 64 :=
.seq loopBody534_19 loopBody534_139

def loopBody534_141 : HolLoopProg 64 :=
.mark loopBody534_140

def loopBody534_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody534_143 : HolLoopProg 64 :=
.mark loopBody534_142

def loopBody534_144 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody534_23 loopBody534_7 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody534_145 : HolLoopProg 64 :=
.mark loopBody534_144

def loopBody534_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody534_147 : HolLoopProg 64 :=
.mark loopBody534_146

def loopBody534_148 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 596) ([]) (some (4, loopBody534_147, loopBody534_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody534_149 : HolLoopProg 64 :=
.mark loopBody534_148

def loopBody534_150 : HolLoopProg 64 :=
.seq loopBody534_149 loopBody534_1

def loopBody534_151 : HolLoopProg 64 :=
.mark loopBody534_150

def loopBody534_152 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_151

def loopBody534_153 : HolLoopProg 64 :=
.mark loopBody534_152

def loopBody534_154 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_153

def loopBody534_155 : HolLoopProg 64 :=
.mark loopBody534_154

def loopBody534_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 288#64]),
        Flapjack.HolLoopExp.const 16#64]))

def loopBody534_157 : HolLoopProg 64 :=
.mark loopBody534_156

def loopBody534_158 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.RegImm.reg 5) loopBody534_23 loopBody534_7 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))

def loopBody534_159 : HolLoopProg 64 :=
.mark loopBody534_158

def loopBody534_160 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64])

def loopBody534_161 : HolLoopProg 64 :=
.mark loopBody534_160

def loopBody534_162 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 288#64]),
        Flapjack.HolLoopExp.const 0#64]))

def loopBody534_163 : HolLoopProg 64 :=
.mark loopBody534_162

def loopBody534_164 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody534_165 : HolLoopProg 64 :=
.mark loopBody534_164

def loopBody534_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 3) 5

def loopBody534_167 : HolLoopProg 64 :=
.mark loopBody534_166

def loopBody534_168 : HolLoopProg 64 :=
.seq loopBody534_167 loopBody534_1

def loopBody534_169 : HolLoopProg 64 :=
.mark loopBody534_168

def loopBody534_170 : HolLoopProg 64 :=
.seq loopBody534_165 loopBody534_169

def loopBody534_171 : HolLoopProg 64 :=
.mark loopBody534_170

def loopBody534_172 : HolLoopProg 64 :=
.seq loopBody534_171 loopBody534_1

def loopBody534_173 : HolLoopProg 64 :=
.mark loopBody534_172

def loopBody534_174 : HolLoopProg 64 :=
.seq loopBody534_163 loopBody534_173

def loopBody534_175 : HolLoopProg 64 :=
.mark loopBody534_174

def loopBody534_176 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_175

def loopBody534_177 : HolLoopProg 64 :=
.mark loopBody534_176

def loopBody534_178 : HolLoopProg 64 :=
.seq loopBody534_161 loopBody534_177

def loopBody534_179 : HolLoopProg 64 :=
.mark loopBody534_178

def loopBody534_180 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_179

def loopBody534_181 : HolLoopProg 64 :=
.mark loopBody534_180

def loopBody534_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 288#64])

def loopBody534_183 : HolLoopProg 64 :=
.mark loopBody534_182

def loopBody534_184 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 288#64]),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody534_185 : HolLoopProg 64 :=
.mark loopBody534_184

def loopBody534_186 : HolLoopProg 64 :=
.seq loopBody534_185 loopBody534_173

def loopBody534_187 : HolLoopProg 64 :=
.mark loopBody534_186

def loopBody534_188 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_187

def loopBody534_189 : HolLoopProg 64 :=
.mark loopBody534_188

def loopBody534_190 : HolLoopProg 64 :=
.seq loopBody534_183 loopBody534_189

def loopBody534_191 : HolLoopProg 64 :=
.mark loopBody534_190

def loopBody534_192 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_191

def loopBody534_193 : HolLoopProg 64 :=
.mark loopBody534_192

def loopBody534_194 : HolLoopProg 64 :=
.seq loopBody534_181 loopBody534_193

def loopBody534_195 : HolLoopProg 64 :=
.mark loopBody534_194

def loopBody534_196 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody534_197 : HolLoopProg 64 :=
.mark loopBody534_196

def loopBody534_198 : HolLoopProg 64 :=
.seq loopBody534_197 loopBody534_1

def loopBody534_199 : HolLoopProg 64 :=
.mark loopBody534_198

def loopBody534_200 : HolLoopProg 64 :=
.seq loopBody534_199 loopBody534_1

def loopBody534_201 : HolLoopProg 64 :=
.mark loopBody534_200

def loopBody534_202 : HolLoopProg 64 :=
.seq loopBody534_195 loopBody534_201

def loopBody534_203 : HolLoopProg 64 :=
.mark loopBody534_202

def loopBody534_204 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody534_205 : HolLoopProg 64 :=
.mark loopBody534_204

def loopBody534_206 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody534_207 : HolLoopProg 64 :=
.mark loopBody534_206

def loopBody534_208 : HolLoopProg 64 :=
.seq loopBody534_207 loopBody534_1

def loopBody534_209 : HolLoopProg 64 :=
.mark loopBody534_208

def loopBody534_210 : HolLoopProg 64 :=
.seq loopBody534_209 loopBody534_1

def loopBody534_211 : HolLoopProg 64 :=
.mark loopBody534_210

def loopBody534_212 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody534_213 : HolLoopProg 64 :=
.mark loopBody534_212

def loopBody534_214 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 593) ([6]) (some (6, loopBody534_55, loopBody534_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody534_215 : HolLoopProg 64 :=
.mark loopBody534_214

def loopBody534_216 : HolLoopProg 64 :=
.seq loopBody534_215 loopBody534_1

def loopBody534_217 : HolLoopProg 64 :=
.mark loopBody534_216

def loopBody534_218 : HolLoopProg 64 :=
.seq loopBody534_213 loopBody534_217

def loopBody534_219 : HolLoopProg 64 :=
.mark loopBody534_218

def loopBody534_220 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_219

def loopBody534_221 : HolLoopProg 64 :=
.mark loopBody534_220

def loopBody534_222 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_221

def loopBody534_223 : HolLoopProg 64 :=
.mark loopBody534_222

def loopBody534_224 : HolLoopProg 64 :=
.seq loopBody534_211 loopBody534_223

def loopBody534_225 : HolLoopProg 64 :=
.mark loopBody534_224

def loopBody534_226 : HolLoopProg 64 :=
.seq loopBody534_57 loopBody534_225

def loopBody534_227 : HolLoopProg 64 :=
.mark loopBody534_226

def loopBody534_228 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 8#64) loopBody534_205 loopBody534_227 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody534_229 : HolLoopProg 64 :=
.mark loopBody534_228

def loopBody534_230 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 597) ([]) (some (5, loopBody534_229, loopBody534_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody534_231 : HolLoopProg 64 :=
.mark loopBody534_230

def loopBody534_232 : HolLoopProg 64 :=
.seq loopBody534_231 loopBody534_1

def loopBody534_233 : HolLoopProg 64 :=
.mark loopBody534_232

def loopBody534_234 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_233

def loopBody534_235 : HolLoopProg 64 :=
.mark loopBody534_234

def loopBody534_236 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_235

def loopBody534_237 : HolLoopProg 64 :=
.mark loopBody534_236

def loopBody534_238 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_237

def loopBody534_239 : HolLoopProg 64 :=
.mark loopBody534_238

def loopBody534_240 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_239

def loopBody534_241 : HolLoopProg 64 :=
.mark loopBody534_240

def loopBody534_242 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody534_203 loopBody534_241 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody534_243 : HolLoopProg 64 :=
.mark loopBody534_242

def loopBody534_244 : HolLoopProg 64 :=
.seq loopBody534_243 loopBody534_1

def loopBody534_245 : HolLoopProg 64 :=
.mark loopBody534_244

def loopBody534_246 : HolLoopProg 64 :=
.seq loopBody534_27 loopBody534_245

def loopBody534_247 : HolLoopProg 64 :=
.mark loopBody534_246

def loopBody534_248 : HolLoopProg 64 :=
.seq loopBody534_159 loopBody534_247

def loopBody534_249 : HolLoopProg 64 :=
.mark loopBody534_248

def loopBody534_250 : HolLoopProg 64 :=
.seq loopBody534_21 loopBody534_249

def loopBody534_251 : HolLoopProg 64 :=
.mark loopBody534_250

def loopBody534_252 : HolLoopProg 64 :=
.seq loopBody534_157 loopBody534_251

def loopBody534_253 : HolLoopProg 64 :=
.mark loopBody534_252

def loopBody534_254 : HolLoopProg 64 :=
.seq loopBody534_155 loopBody534_253

def loopBody534_255 : HolLoopProg 64 :=
.mark loopBody534_254

def loopBody534_256 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody534_255 loopBody534_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody534_257 : HolLoopProg 64 :=
.mark loopBody534_256

def loopBody534_258 : HolLoopProg 64 :=
.seq loopBody534_257 loopBody534_1

def loopBody534_259 : HolLoopProg 64 :=
.mark loopBody534_258

def loopBody534_260 : HolLoopProg 64 :=
.seq loopBody534_27 loopBody534_259

def loopBody534_261 : HolLoopProg 64 :=
.mark loopBody534_260

def loopBody534_262 : HolLoopProg 64 :=
.seq loopBody534_145 loopBody534_261

def loopBody534_263 : HolLoopProg 64 :=
.mark loopBody534_262

def loopBody534_264 : HolLoopProg 64 :=
.seq loopBody534_21 loopBody534_263

def loopBody534_265 : HolLoopProg 64 :=
.mark loopBody534_264

def loopBody534_266 : HolLoopProg 64 :=
.seq loopBody534_143 loopBody534_265

def loopBody534_267 : HolLoopProg 64 :=
.mark loopBody534_266

def loopBody534_268 : HolLoopProg 64 :=
.seq loopBody534_141 loopBody534_267

def loopBody534_269 : HolLoopProg 64 :=
.mark loopBody534_268

def loopBody534_270 : HolLoopProg 64 :=
.seq loopBody534_17 loopBody534_269

def loopBody534_271 : HolLoopProg 64 :=
.mark loopBody534_270

def loopBody534_272 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_271

def loopBody534_273 : HolLoopProg 64 :=
.mark loopBody534_272

def loopBody534_274 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody534_275 : HolLoopProg 64 :=
.mark loopBody534_274

def loopBody534_276 : HolLoopProg 64 :=
.seq loopBody534_273 loopBody534_275

def loopBody534_277 : HolLoopProg 64 :=
.mark loopBody534_276

def loopBody534_278 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody534_279 : HolLoopProg 64 :=
.mark loopBody534_278

def loopBody534_280 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody534_277 loopBody534_279 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody534_281 : HolLoopProg 64 :=
.mark loopBody534_280

def loopBody534_282 : HolLoopProg 64 :=
.seq loopBody534_281 loopBody534_1

def loopBody534_283 : HolLoopProg 64 :=
.mark loopBody534_282

def loopBody534_284 : HolLoopProg 64 :=
.seq loopBody534_15 loopBody534_283

def loopBody534_285 : HolLoopProg 64 :=
.mark loopBody534_284

def loopBody534_286 : HolLoopProg 64 :=
.seq loopBody534_13 loopBody534_285

def loopBody534_287 : HolLoopProg 64 :=
.mark loopBody534_286

def loopBody534_288 : HolLoopProg 64 :=
.seq loopBody534_7 loopBody534_287

def loopBody534_289 : HolLoopProg 64 :=
.mark loopBody534_288

def loopBody534_290 : HolLoopProg 64 :=
.seq loopBody534_5 loopBody534_289

def loopBody534_291 : HolLoopProg 64 :=
.mark loopBody534_290

def loopBody534_292 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) loopBody534_291 (Flapjack.Spt.ln)

def loopBody534_293 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody534_294 : HolLoopProg 64 :=
.mark loopBody534_293

def loopBody534_295 : HolLoopProg 64 :=
.seq loopBody534_294 loopBody534_1

def loopBody534_296 : HolLoopProg 64 :=
.mark loopBody534_295

def loopBody534_297 : HolLoopProg 64 :=
.seq loopBody534_17 loopBody534_296

def loopBody534_298 : HolLoopProg 64 :=
.mark loopBody534_297

def loopBody534_299 : HolLoopProg 64 :=
.seq loopBody534_292 loopBody534_298

def loopBody534_300 : HolLoopProg 64 :=
.seq loopBody534_3 loopBody534_299

def loopBody534_301 : HolLoopProg 64 :=
.seq loopBody534_1 loopBody534_300

def output534 : Nat × List Nat × HolLoopProg 64 :=
  (598, [], loopBody534_301)
end InitECandidate.Proofs.FrontendStages.Loop
