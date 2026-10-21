import InitECandidate.Proofs.FrontendStages.Loop.Translate749
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody765_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody765_1 : HolLoopProg 64 :=
.mark loopBody765_0

def loopBody765_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody765_3 : HolLoopProg 64 :=
.mark loopBody765_2

def loopBody765_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64]))

def loopBody765_5 : HolLoopProg 64 :=
.mark loopBody765_4

def loopBody765_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody765_7 : HolLoopProg 64 :=
.mark loopBody765_6

def loopBody765_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody765_9 : HolLoopProg 64 :=
.mark loopBody765_8

def loopBody765_10 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 461) ([4]) (some (4, loopBody765_9, loopBody765_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody765_11 : HolLoopProg 64 :=
.mark loopBody765_10

def loopBody765_12 : HolLoopProg 64 :=
.seq loopBody765_11 loopBody765_1

def loopBody765_13 : HolLoopProg 64 :=
.mark loopBody765_12

def loopBody765_14 : HolLoopProg 64 :=
.seq loopBody765_7 loopBody765_13

def loopBody765_15 : HolLoopProg 64 :=
.mark loopBody765_14

def loopBody765_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody765_17 : HolLoopProg 64 :=
.mark loopBody765_16

def loopBody765_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 120#64)

def loopBody765_19 : HolLoopProg 64 :=
.mark loopBody765_18

def loopBody765_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 7 7 5 6)

def loopBody765_21 : HolLoopProg 64 :=
.mark loopBody765_20

def loopBody765_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 600#64, Flapjack.HolLoopExp.var 7])

def loopBody765_23 : HolLoopProg 64 :=
.mark loopBody765_22

def loopBody765_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody765_25 : HolLoopProg 64 :=
.mark loopBody765_24

def loopBody765_26 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 466) ([8]) (some (5, loopBody765_25, loopBody765_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody765_27 : HolLoopProg 64 :=
.mark loopBody765_26

def loopBody765_28 : HolLoopProg 64 :=
.seq loopBody765_27 loopBody765_1

def loopBody765_29 : HolLoopProg 64 :=
.mark loopBody765_28

def loopBody765_30 : HolLoopProg 64 :=
.seq loopBody765_23 loopBody765_29

def loopBody765_31 : HolLoopProg 64 :=
.mark loopBody765_30

def loopBody765_32 : HolLoopProg 64 :=
.seq loopBody765_21 loopBody765_31

def loopBody765_33 : HolLoopProg 64 :=
.mark loopBody765_32

def loopBody765_34 : HolLoopProg 64 :=
.seq loopBody765_19 loopBody765_33

def loopBody765_35 : HolLoopProg 64 :=
.mark loopBody765_34

def loopBody765_36 : HolLoopProg 64 :=
.seq loopBody765_17 loopBody765_35

def loopBody765_37 : HolLoopProg 64 :=
.mark loopBody765_36

def loopBody765_38 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_37

def loopBody765_39 : HolLoopProg 64 :=
.mark loopBody765_38

def loopBody765_40 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_39

def loopBody765_41 : HolLoopProg 64 :=
.mark loopBody765_40

def loopBody765_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody765_43 : HolLoopProg 64 :=
.mark loopBody765_42

def loopBody765_44 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 68) ([5]) (some (5, loopBody765_25, loopBody765_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))

def loopBody765_45 : HolLoopProg 64 :=
.mark loopBody765_44

def loopBody765_46 : HolLoopProg 64 :=
.seq loopBody765_45 loopBody765_1

def loopBody765_47 : HolLoopProg 64 :=
.mark loopBody765_46

def loopBody765_48 : HolLoopProg 64 :=
.seq loopBody765_43 loopBody765_47

def loopBody765_49 : HolLoopProg 64 :=
.mark loopBody765_48

def loopBody765_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody765_51 : HolLoopProg 64 :=
.mark loopBody765_50

def loopBody765_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 12#64)

def loopBody765_53 : HolLoopProg 64 :=
.mark loopBody765_52

def loopBody765_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody765_55 : HolLoopProg 64 :=
.mark loopBody765_54

def loopBody765_56 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.ls PUnit.unit))) (some 78) ([6, 7]) (some (6, loopBody765_55, loopBody765_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))

def loopBody765_57 : HolLoopProg 64 :=
.mark loopBody765_56

def loopBody765_58 : HolLoopProg 64 :=
.seq loopBody765_57 loopBody765_1

def loopBody765_59 : HolLoopProg 64 :=
.mark loopBody765_58

def loopBody765_60 : HolLoopProg 64 :=
.seq loopBody765_53 loopBody765_59

def loopBody765_61 : HolLoopProg 64 :=
.mark loopBody765_60

def loopBody765_62 : HolLoopProg 64 :=
.seq loopBody765_51 loopBody765_61

def loopBody765_63 : HolLoopProg 64 :=
.mark loopBody765_62

def loopBody765_64 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_63

def loopBody765_65 : HolLoopProg 64 :=
.mark loopBody765_64

def loopBody765_66 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_65

def loopBody765_67 : HolLoopProg 64 :=
.mark loopBody765_66

def loopBody765_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 88#64]))

def loopBody765_69 : HolLoopProg 64 :=
.mark loopBody765_68

def loopBody765_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody765_71 : HolLoopProg 64 :=
.mark loopBody765_70

def loopBody765_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 12#64])

def loopBody765_73 : HolLoopProg 64 :=
.mark loopBody765_72

def loopBody765_74 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 627) ([6, 7, 8]) (some (6, loopBody765_55, loopBody765_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody765_75 : HolLoopProg 64 :=
.mark loopBody765_74

def loopBody765_76 : HolLoopProg 64 :=
.seq loopBody765_75 loopBody765_1

def loopBody765_77 : HolLoopProg 64 :=
.mark loopBody765_76

def loopBody765_78 : HolLoopProg 64 :=
.seq loopBody765_73 loopBody765_77

def loopBody765_79 : HolLoopProg 64 :=
.mark loopBody765_78

def loopBody765_80 : HolLoopProg 64 :=
.seq loopBody765_71 loopBody765_79

def loopBody765_81 : HolLoopProg 64 :=
.mark loopBody765_80

def loopBody765_82 : HolLoopProg 64 :=
.seq loopBody765_69 loopBody765_81

def loopBody765_83 : HolLoopProg 64 :=
.mark loopBody765_82

def loopBody765_84 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_83

def loopBody765_85 : HolLoopProg 64 :=
.mark loopBody765_84

def loopBody765_86 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_85

def loopBody765_87 : HolLoopProg 64 :=
.mark loopBody765_86

def loopBody765_88 : HolLoopProg 64 :=
.seq loopBody765_67 loopBody765_87

def loopBody765_89 : HolLoopProg 64 :=
.mark loopBody765_88

def loopBody765_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody765_91 : HolLoopProg 64 :=
.mark loopBody765_90

def loopBody765_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody765_93 : HolLoopProg 64 :=
.mark loopBody765_92

def loopBody765_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody765_95 : HolLoopProg 64 :=
.mark loopBody765_94

def loopBody765_96 : HolLoopProg 64 :=
.seq loopBody765_95 loopBody765_1

def loopBody765_97 : HolLoopProg 64 :=
.mark loopBody765_96

def loopBody765_98 : HolLoopProg 64 :=
.seq loopBody765_93 loopBody765_97

def loopBody765_99 : HolLoopProg 64 :=
.mark loopBody765_98

def loopBody765_100 : HolLoopProg 64 :=
.seq loopBody765_99 loopBody765_1

def loopBody765_101 : HolLoopProg 64 :=
.mark loopBody765_100

def loopBody765_102 : HolLoopProg 64 :=
.seq loopBody765_51 loopBody765_101

def loopBody765_103 : HolLoopProg 64 :=
.mark loopBody765_102

def loopBody765_104 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_103

def loopBody765_105 : HolLoopProg 64 :=
.mark loopBody765_104

def loopBody765_106 : HolLoopProg 64 :=
.seq loopBody765_91 loopBody765_105

def loopBody765_107 : HolLoopProg 64 :=
.mark loopBody765_106

def loopBody765_108 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_107

def loopBody765_109 : HolLoopProg 64 :=
.mark loopBody765_108

def loopBody765_110 : HolLoopProg 64 :=
.seq loopBody765_89 loopBody765_109

def loopBody765_111 : HolLoopProg 64 :=
.mark loopBody765_110

def loopBody765_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody765_113 : HolLoopProg 64 :=
.mark loopBody765_112

def loopBody765_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 32#64)

def loopBody765_115 : HolLoopProg 64 :=
.mark loopBody765_114

def loopBody765_116 : HolLoopProg 64 :=
.seq loopBody765_115 loopBody765_101

def loopBody765_117 : HolLoopProg 64 :=
.mark loopBody765_116

def loopBody765_118 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_117

def loopBody765_119 : HolLoopProg 64 :=
.mark loopBody765_118

def loopBody765_120 : HolLoopProg 64 :=
.seq loopBody765_113 loopBody765_119

def loopBody765_121 : HolLoopProg 64 :=
.mark loopBody765_120

def loopBody765_122 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_121

def loopBody765_123 : HolLoopProg 64 :=
.mark loopBody765_122

def loopBody765_124 : HolLoopProg 64 :=
.seq loopBody765_111 loopBody765_123

def loopBody765_125 : HolLoopProg 64 :=
.mark loopBody765_124

def loopBody765_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody765_127 : HolLoopProg 64 :=
.mark loopBody765_126

def loopBody765_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody765_129 : HolLoopProg 64 :=
.mark loopBody765_128

def loopBody765_130 : HolLoopProg 64 :=
.seq loopBody765_129 loopBody765_1

def loopBody765_131 : HolLoopProg 64 :=
.mark loopBody765_130

def loopBody765_132 : HolLoopProg 64 :=
.seq loopBody765_127 loopBody765_131

def loopBody765_133 : HolLoopProg 64 :=
.mark loopBody765_132

def loopBody765_134 : HolLoopProg 64 :=
.seq loopBody765_125 loopBody765_133

def loopBody765_135 : HolLoopProg 64 :=
.mark loopBody765_134

def loopBody765_136 : HolLoopProg 64 :=
.seq loopBody765_49 loopBody765_135

def loopBody765_137 : HolLoopProg 64 :=
.mark loopBody765_136

def loopBody765_138 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_137

def loopBody765_139 : HolLoopProg 64 :=
.mark loopBody765_138

def loopBody765_140 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_139

def loopBody765_141 : HolLoopProg 64 :=
.mark loopBody765_140

def loopBody765_142 : HolLoopProg 64 :=
.seq loopBody765_41 loopBody765_141

def loopBody765_143 : HolLoopProg 64 :=
.mark loopBody765_142

def loopBody765_144 : HolLoopProg 64 :=
.seq loopBody765_15 loopBody765_143

def loopBody765_145 : HolLoopProg 64 :=
.mark loopBody765_144

def loopBody765_146 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_145

def loopBody765_147 : HolLoopProg 64 :=
.mark loopBody765_146

def loopBody765_148 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_147

def loopBody765_149 : HolLoopProg 64 :=
.mark loopBody765_148

def loopBody765_150 : HolLoopProg 64 :=
.seq loopBody765_5 loopBody765_149

def loopBody765_151 : HolLoopProg 64 :=
.mark loopBody765_150

def loopBody765_152 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_151

def loopBody765_153 : HolLoopProg 64 :=
.mark loopBody765_152

def loopBody765_154 : HolLoopProg 64 :=
.seq loopBody765_3 loopBody765_153

def loopBody765_155 : HolLoopProg 64 :=
.mark loopBody765_154

def loopBody765_156 : HolLoopProg 64 :=
.seq loopBody765_1 loopBody765_155

def loopBody765_157 : HolLoopProg 64 :=
.mark loopBody765_156

def output765 : Nat × List Nat × HolLoopProg 64 :=
  (829, [], loopBody765_157)
end InitECandidate.Proofs.FrontendStages.Loop
