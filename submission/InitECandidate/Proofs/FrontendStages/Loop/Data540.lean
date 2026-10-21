import InitECandidate.Proofs.FrontendStages.Loop.Translate524
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody540_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody540_1 : HolLoopProg 64 :=
.mark loopBody540_0

def loopBody540_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody540_3 : HolLoopProg 64 :=
.mark loopBody540_2

def loopBody540_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 386) ([]) (some (2, loopBody540_3, loopBody540_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody540_5 : HolLoopProg 64 :=
.mark loopBody540_4

def loopBody540_6 : HolLoopProg 64 :=
.seq loopBody540_5 loopBody540_1

def loopBody540_7 : HolLoopProg 64 :=
.mark loopBody540_6

def loopBody540_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 32#64]))

def loopBody540_9 : HolLoopProg 64 :=
.mark loopBody540_8

def loopBody540_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody540_11 : HolLoopProg 64 :=
.mark loopBody540_10

def loopBody540_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody540_13 : HolLoopProg 64 :=
.mark loopBody540_12

def loopBody540_14 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 417) ([4]) (some (4, loopBody540_13, loopBody540_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody540_15 : HolLoopProg 64 :=
.mark loopBody540_14

def loopBody540_16 : HolLoopProg 64 :=
.seq loopBody540_15 loopBody540_1

def loopBody540_17 : HolLoopProg 64 :=
.mark loopBody540_16

def loopBody540_18 : HolLoopProg 64 :=
.seq loopBody540_11 loopBody540_17

def loopBody540_19 : HolLoopProg 64 :=
.mark loopBody540_18

def loopBody540_20 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_19

def loopBody540_21 : HolLoopProg 64 :=
.mark loopBody540_20

def loopBody540_22 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_21

def loopBody540_23 : HolLoopProg 64 :=
.mark loopBody540_22

def loopBody540_24 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 421) ([4]) (some (4, loopBody540_13, loopBody540_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody540_25 : HolLoopProg 64 :=
.mark loopBody540_24

def loopBody540_26 : HolLoopProg 64 :=
.seq loopBody540_25 loopBody540_1

def loopBody540_27 : HolLoopProg 64 :=
.mark loopBody540_26

def loopBody540_28 : HolLoopProg 64 :=
.seq loopBody540_11 loopBody540_27

def loopBody540_29 : HolLoopProg 64 :=
.mark loopBody540_28

def loopBody540_30 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_29

def loopBody540_31 : HolLoopProg 64 :=
.mark loopBody540_30

def loopBody540_32 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_31

def loopBody540_33 : HolLoopProg 64 :=
.mark loopBody540_32

def loopBody540_34 : HolLoopProg 64 :=
.seq loopBody540_23 loopBody540_33

def loopBody540_35 : HolLoopProg 64 :=
.mark loopBody540_34

def loopBody540_36 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 426) ([4]) (some (4, loopBody540_13, loopBody540_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody540_37 : HolLoopProg 64 :=
.mark loopBody540_36

def loopBody540_38 : HolLoopProg 64 :=
.seq loopBody540_37 loopBody540_1

def loopBody540_39 : HolLoopProg 64 :=
.mark loopBody540_38

def loopBody540_40 : HolLoopProg 64 :=
.seq loopBody540_11 loopBody540_39

def loopBody540_41 : HolLoopProg 64 :=
.mark loopBody540_40

def loopBody540_42 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_41

def loopBody540_43 : HolLoopProg 64 :=
.mark loopBody540_42

def loopBody540_44 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_43

def loopBody540_45 : HolLoopProg 64 :=
.mark loopBody540_44

def loopBody540_46 : HolLoopProg 64 :=
.seq loopBody540_35 loopBody540_45

def loopBody540_47 : HolLoopProg 64 :=
.mark loopBody540_46

def loopBody540_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody540_49 : HolLoopProg 64 :=
.mark loopBody540_48

def loopBody540_50 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 602) ([4]) (some (4, loopBody540_13, loopBody540_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody540_51 : HolLoopProg 64 :=
.mark loopBody540_50

def loopBody540_52 : HolLoopProg 64 :=
.seq loopBody540_51 loopBody540_1

def loopBody540_53 : HolLoopProg 64 :=
.mark loopBody540_52

def loopBody540_54 : HolLoopProg 64 :=
.seq loopBody540_49 loopBody540_53

def loopBody540_55 : HolLoopProg 64 :=
.mark loopBody540_54

def loopBody540_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 160#64]))

def loopBody540_57 : HolLoopProg 64 :=
.mark loopBody540_56

def loopBody540_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody540_59 : HolLoopProg 64 :=
.mark loopBody540_58

def loopBody540_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody540_61 : HolLoopProg 64 :=
.mark loopBody540_60

def loopBody540_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody540_63 : HolLoopProg 64 :=
.mark loopBody540_62

def loopBody540_64 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody540_61 loopBody540_63 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody540_65 : HolLoopProg 64 :=
.mark loopBody540_64

def loopBody540_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody540_67 : HolLoopProg 64 :=
.mark loopBody540_66

def loopBody540_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]))

def loopBody540_69 : HolLoopProg 64 :=
.mark loopBody540_68

def loopBody540_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64])

def loopBody540_71 : HolLoopProg 64 :=
.mark loopBody540_70

def loopBody540_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody540_73 : HolLoopProg 64 :=
.mark loopBody540_72

def loopBody540_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody540_75 : HolLoopProg 64 :=
.mark loopBody540_74

def loopBody540_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody540_77 : HolLoopProg 64 :=
.mark loopBody540_76

def loopBody540_78 : HolLoopProg 64 :=
.seq loopBody540_77 loopBody540_1

def loopBody540_79 : HolLoopProg 64 :=
.mark loopBody540_78

def loopBody540_80 : HolLoopProg 64 :=
.seq loopBody540_75 loopBody540_79

def loopBody540_81 : HolLoopProg 64 :=
.mark loopBody540_80

def loopBody540_82 : HolLoopProg 64 :=
.seq loopBody540_81 loopBody540_1

def loopBody540_83 : HolLoopProg 64 :=
.mark loopBody540_82

def loopBody540_84 : HolLoopProg 64 :=
.seq loopBody540_73 loopBody540_83

def loopBody540_85 : HolLoopProg 64 :=
.mark loopBody540_84

def loopBody540_86 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_85

def loopBody540_87 : HolLoopProg 64 :=
.mark loopBody540_86

def loopBody540_88 : HolLoopProg 64 :=
.seq loopBody540_71 loopBody540_87

def loopBody540_89 : HolLoopProg 64 :=
.mark loopBody540_88

def loopBody540_90 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_89

def loopBody540_91 : HolLoopProg 64 :=
.mark loopBody540_90

def loopBody540_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody540_93 : HolLoopProg 64 :=
.mark loopBody540_92

def loopBody540_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody540_95 : HolLoopProg 64 :=
.mark loopBody540_94

def loopBody540_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody540_97 : HolLoopProg 64 :=
.mark loopBody540_96

def loopBody540_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody540_99 : HolLoopProg 64 :=
.mark loopBody540_98

def loopBody540_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody540_101 : HolLoopProg 64 :=
.mark loopBody540_100

def loopBody540_102 : HolLoopProg 64 :=
.seq loopBody540_101 loopBody540_1

def loopBody540_103 : HolLoopProg 64 :=
.mark loopBody540_102

def loopBody540_104 : HolLoopProg 64 :=
.seq loopBody540_103 loopBody540_1

def loopBody540_105 : HolLoopProg 64 :=
.mark loopBody540_104

def loopBody540_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody540_107 : HolLoopProg 64 :=
.mark loopBody540_106

def loopBody540_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody540_109 : HolLoopProg 64 :=
.mark loopBody540_108

def loopBody540_110 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))) (some 387) ([8]) (some (8, loopBody540_109, loopBody540_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody540_111 : HolLoopProg 64 :=
.mark loopBody540_110

def loopBody540_112 : HolLoopProg 64 :=
.seq loopBody540_111 loopBody540_1

def loopBody540_113 : HolLoopProg 64 :=
.mark loopBody540_112

def loopBody540_114 : HolLoopProg 64 :=
.seq loopBody540_107 loopBody540_113

def loopBody540_115 : HolLoopProg 64 :=
.mark loopBody540_114

def loopBody540_116 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_115

def loopBody540_117 : HolLoopProg 64 :=
.mark loopBody540_116

def loopBody540_118 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_117

def loopBody540_119 : HolLoopProg 64 :=
.mark loopBody540_118

def loopBody540_120 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))) (some 470) ([]) (some (8, loopBody540_109, loopBody540_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody540_121 : HolLoopProg 64 :=
.mark loopBody540_120

def loopBody540_122 : HolLoopProg 64 :=
.seq loopBody540_121 loopBody540_1

def loopBody540_123 : HolLoopProg 64 :=
.mark loopBody540_122

def loopBody540_124 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_123

def loopBody540_125 : HolLoopProg 64 :=
.mark loopBody540_124

def loopBody540_126 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_125

def loopBody540_127 : HolLoopProg 64 :=
.mark loopBody540_126

def loopBody540_128 : HolLoopProg 64 :=
.seq loopBody540_119 loopBody540_127

def loopBody540_129 : HolLoopProg 64 :=
.mark loopBody540_128

def loopBody540_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody540_131 : HolLoopProg 64 :=
.mark loopBody540_130

def loopBody540_132 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 600) ([8]) (some (8, loopBody540_109, loopBody540_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody540_133 : HolLoopProg 64 :=
.mark loopBody540_132

def loopBody540_134 : HolLoopProg 64 :=
.seq loopBody540_133 loopBody540_1

def loopBody540_135 : HolLoopProg 64 :=
.mark loopBody540_134

def loopBody540_136 : HolLoopProg 64 :=
.seq loopBody540_131 loopBody540_135

def loopBody540_137 : HolLoopProg 64 :=
.mark loopBody540_136

def loopBody540_138 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_137

def loopBody540_139 : HolLoopProg 64 :=
.mark loopBody540_138

def loopBody540_140 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_139

def loopBody540_141 : HolLoopProg 64 :=
.mark loopBody540_140

def loopBody540_142 : HolLoopProg 64 :=
.seq loopBody540_129 loopBody540_141

def loopBody540_143 : HolLoopProg 64 :=
.mark loopBody540_142

def loopBody540_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody540_145 : HolLoopProg 64 :=
.mark loopBody540_144

def loopBody540_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 264#64]))

def loopBody540_147 : HolLoopProg 64 :=
.mark loopBody540_146

def loopBody540_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 8)

def loopBody540_149 : HolLoopProg 64 :=
.mark loopBody540_148

def loopBody540_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 7) 9

def loopBody540_151 : HolLoopProg 64 :=
.mark loopBody540_150

def loopBody540_152 : HolLoopProg 64 :=
.seq loopBody540_151 loopBody540_1

def loopBody540_153 : HolLoopProg 64 :=
.mark loopBody540_152

def loopBody540_154 : HolLoopProg 64 :=
.seq loopBody540_149 loopBody540_153

def loopBody540_155 : HolLoopProg 64 :=
.mark loopBody540_154

def loopBody540_156 : HolLoopProg 64 :=
.seq loopBody540_155 loopBody540_1

def loopBody540_157 : HolLoopProg 64 :=
.mark loopBody540_156

def loopBody540_158 : HolLoopProg 64 :=
.seq loopBody540_147 loopBody540_157

def loopBody540_159 : HolLoopProg 64 :=
.mark loopBody540_158

def loopBody540_160 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_159

def loopBody540_161 : HolLoopProg 64 :=
.mark loopBody540_160

def loopBody540_162 : HolLoopProg 64 :=
.seq loopBody540_145 loopBody540_161

def loopBody540_163 : HolLoopProg 64 :=
.mark loopBody540_162

def loopBody540_164 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_163

def loopBody540_165 : HolLoopProg 64 :=
.mark loopBody540_164

def loopBody540_166 : HolLoopProg 64 :=
.seq loopBody540_143 loopBody540_165

def loopBody540_167 : HolLoopProg 64 :=
.mark loopBody540_166

def loopBody540_168 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody540_169 : HolLoopProg 64 :=
.mark loopBody540_168

def loopBody540_170 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody540_171 : HolLoopProg 64 :=
.mark loopBody540_170

def loopBody540_172 : HolLoopProg 64 :=
.seq loopBody540_171 loopBody540_157

def loopBody540_173 : HolLoopProg 64 :=
.mark loopBody540_172

def loopBody540_174 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_173

def loopBody540_175 : HolLoopProg 64 :=
.mark loopBody540_174

def loopBody540_176 : HolLoopProg 64 :=
.seq loopBody540_169 loopBody540_175

def loopBody540_177 : HolLoopProg 64 :=
.mark loopBody540_176

def loopBody540_178 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_177

def loopBody540_179 : HolLoopProg 64 :=
.mark loopBody540_178

def loopBody540_180 : HolLoopProg 64 :=
.seq loopBody540_167 loopBody540_179

def loopBody540_181 : HolLoopProg 64 :=
.mark loopBody540_180

def loopBody540_182 : HolLoopProg 64 :=
.seq loopBody540_105 loopBody540_181

def loopBody540_183 : HolLoopProg 64 :=
.mark loopBody540_182

def loopBody540_184 : HolLoopProg 64 :=
.seq loopBody540_99 loopBody540_183

def loopBody540_185 : HolLoopProg 64 :=
.mark loopBody540_184

def loopBody540_186 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 8#64) loopBody540_97 loopBody540_185 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody540_187 : HolLoopProg 64 :=
.mark loopBody540_186

def loopBody540_188 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 603) ([7, 8]) (some (7, loopBody540_187, loopBody540_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody540_189 : HolLoopProg 64 :=
.mark loopBody540_188

def loopBody540_190 : HolLoopProg 64 :=
.seq loopBody540_189 loopBody540_1

def loopBody540_191 : HolLoopProg 64 :=
.mark loopBody540_190

def loopBody540_192 : HolLoopProg 64 :=
.seq loopBody540_95 loopBody540_191

def loopBody540_193 : HolLoopProg 64 :=
.mark loopBody540_192

def loopBody540_194 : HolLoopProg 64 :=
.seq loopBody540_93 loopBody540_193

def loopBody540_195 : HolLoopProg 64 :=
.mark loopBody540_194

def loopBody540_196 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_195

def loopBody540_197 : HolLoopProg 64 :=
.mark loopBody540_196

def loopBody540_198 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_197

def loopBody540_199 : HolLoopProg 64 :=
.mark loopBody540_198

def loopBody540_200 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64])

def loopBody540_201 : HolLoopProg 64 :=
.mark loopBody540_200

def loopBody540_202 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody540_203 : HolLoopProg 64 :=
.mark loopBody540_202

def loopBody540_204 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody540_205 : HolLoopProg 64 :=
.mark loopBody540_204

def loopBody540_206 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 6) 8

def loopBody540_207 : HolLoopProg 64 :=
.mark loopBody540_206

def loopBody540_208 : HolLoopProg 64 :=
.seq loopBody540_207 loopBody540_1

def loopBody540_209 : HolLoopProg 64 :=
.mark loopBody540_208

def loopBody540_210 : HolLoopProg 64 :=
.seq loopBody540_205 loopBody540_209

def loopBody540_211 : HolLoopProg 64 :=
.mark loopBody540_210

def loopBody540_212 : HolLoopProg 64 :=
.seq loopBody540_211 loopBody540_1

def loopBody540_213 : HolLoopProg 64 :=
.mark loopBody540_212

def loopBody540_214 : HolLoopProg 64 :=
.seq loopBody540_203 loopBody540_213

def loopBody540_215 : HolLoopProg 64 :=
.mark loopBody540_214

def loopBody540_216 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_215

def loopBody540_217 : HolLoopProg 64 :=
.mark loopBody540_216

def loopBody540_218 : HolLoopProg 64 :=
.seq loopBody540_201 loopBody540_217

def loopBody540_219 : HolLoopProg 64 :=
.mark loopBody540_218

def loopBody540_220 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_219

def loopBody540_221 : HolLoopProg 64 :=
.mark loopBody540_220

def loopBody540_222 : HolLoopProg 64 :=
.seq loopBody540_199 loopBody540_221

def loopBody540_223 : HolLoopProg 64 :=
.mark loopBody540_222

def loopBody540_224 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody540_225 : HolLoopProg 64 :=
.mark loopBody540_224

def loopBody540_226 : HolLoopProg 64 :=
.seq loopBody540_225 loopBody540_1

def loopBody540_227 : HolLoopProg 64 :=
.mark loopBody540_226

def loopBody540_228 : HolLoopProg 64 :=
.seq loopBody540_73 loopBody540_227

def loopBody540_229 : HolLoopProg 64 :=
.mark loopBody540_228

def loopBody540_230 : HolLoopProg 64 :=
.seq loopBody540_223 loopBody540_229

def loopBody540_231 : HolLoopProg 64 :=
.mark loopBody540_230

def loopBody540_232 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_231

def loopBody540_233 : HolLoopProg 64 :=
.mark loopBody540_232

def loopBody540_234 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_233

def loopBody540_235 : HolLoopProg 64 :=
.mark loopBody540_234

def loopBody540_236 : HolLoopProg 64 :=
.seq loopBody540_91 loopBody540_235

def loopBody540_237 : HolLoopProg 64 :=
.mark loopBody540_236

def loopBody540_238 : HolLoopProg 64 :=
.seq loopBody540_69 loopBody540_237

def loopBody540_239 : HolLoopProg 64 :=
.mark loopBody540_238

def loopBody540_240 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_239

def loopBody540_241 : HolLoopProg 64 :=
.mark loopBody540_240

def loopBody540_242 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody540_241 loopBody540_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody540_243 : HolLoopProg 64 :=
.mark loopBody540_242

def loopBody540_244 : HolLoopProg 64 :=
.seq loopBody540_243 loopBody540_1

def loopBody540_245 : HolLoopProg 64 :=
.mark loopBody540_244

def loopBody540_246 : HolLoopProg 64 :=
.seq loopBody540_67 loopBody540_245

def loopBody540_247 : HolLoopProg 64 :=
.mark loopBody540_246

def loopBody540_248 : HolLoopProg 64 :=
.seq loopBody540_65 loopBody540_247

def loopBody540_249 : HolLoopProg 64 :=
.mark loopBody540_248

def loopBody540_250 : HolLoopProg 64 :=
.seq loopBody540_59 loopBody540_249

def loopBody540_251 : HolLoopProg 64 :=
.mark loopBody540_250

def loopBody540_252 : HolLoopProg 64 :=
.seq loopBody540_57 loopBody540_251

def loopBody540_253 : HolLoopProg 64 :=
.mark loopBody540_252

def loopBody540_254 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody540_255 : HolLoopProg 64 :=
.mark loopBody540_254

def loopBody540_256 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody540_257 : HolLoopProg 64 :=
.mark loopBody540_256

def loopBody540_258 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 387) ([5]) (some (5, loopBody540_257, loopBody540_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody540_259 : HolLoopProg 64 :=
.mark loopBody540_258

def loopBody540_260 : HolLoopProg 64 :=
.seq loopBody540_259 loopBody540_1

def loopBody540_261 : HolLoopProg 64 :=
.mark loopBody540_260

def loopBody540_262 : HolLoopProg 64 :=
.seq loopBody540_255 loopBody540_261

def loopBody540_263 : HolLoopProg 64 :=
.mark loopBody540_262

def loopBody540_264 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_263

def loopBody540_265 : HolLoopProg 64 :=
.mark loopBody540_264

def loopBody540_266 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_265

def loopBody540_267 : HolLoopProg 64 :=
.mark loopBody540_266

def loopBody540_268 : HolLoopProg 64 :=
.seq loopBody540_253 loopBody540_267

def loopBody540_269 : HolLoopProg 64 :=
.mark loopBody540_268

def loopBody540_270 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody540_271 : HolLoopProg 64 :=
.mark loopBody540_270

def loopBody540_272 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody540_273 : HolLoopProg 64 :=
.mark loopBody540_272

def loopBody540_274 : HolLoopProg 64 :=
.seq loopBody540_273 loopBody540_1

def loopBody540_275 : HolLoopProg 64 :=
.mark loopBody540_274

def loopBody540_276 : HolLoopProg 64 :=
.seq loopBody540_271 loopBody540_275

def loopBody540_277 : HolLoopProg 64 :=
.mark loopBody540_276

def loopBody540_278 : HolLoopProg 64 :=
.seq loopBody540_269 loopBody540_277

def loopBody540_279 : HolLoopProg 64 :=
.mark loopBody540_278

def loopBody540_280 : HolLoopProg 64 :=
.seq loopBody540_55 loopBody540_279

def loopBody540_281 : HolLoopProg 64 :=
.mark loopBody540_280

def loopBody540_282 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_281

def loopBody540_283 : HolLoopProg 64 :=
.mark loopBody540_282

def loopBody540_284 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_283

def loopBody540_285 : HolLoopProg 64 :=
.mark loopBody540_284

def loopBody540_286 : HolLoopProg 64 :=
.seq loopBody540_47 loopBody540_285

def loopBody540_287 : HolLoopProg 64 :=
.mark loopBody540_286

def loopBody540_288 : HolLoopProg 64 :=
.seq loopBody540_9 loopBody540_287

def loopBody540_289 : HolLoopProg 64 :=
.mark loopBody540_288

def loopBody540_290 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_289

def loopBody540_291 : HolLoopProg 64 :=
.mark loopBody540_290

def loopBody540_292 : HolLoopProg 64 :=
.seq loopBody540_7 loopBody540_291

def loopBody540_293 : HolLoopProg 64 :=
.mark loopBody540_292

def loopBody540_294 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_293

def loopBody540_295 : HolLoopProg 64 :=
.mark loopBody540_294

def loopBody540_296 : HolLoopProg 64 :=
.seq loopBody540_1 loopBody540_295

def loopBody540_297 : HolLoopProg 64 :=
.mark loopBody540_296

def output540 : Nat × List Nat × HolLoopProg 64 :=
  (604, [0], loopBody540_297)
end InitECandidate.Proofs.FrontendStages.Loop
