import InitECandidate.Proofs.FrontendStages.Loop.Translate173
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody189_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody189_1 : HolLoopProg 64 :=
.mark loopBody189_0

def loopBody189_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody189_3 : HolLoopProg 64 :=
.mark loopBody189_2

def loopBody189_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody189_3, loopBody189_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody189_5 : HolLoopProg 64 :=
.mark loopBody189_4

def loopBody189_6 : HolLoopProg 64 :=
.seq loopBody189_5 loopBody189_1

def loopBody189_7 : HolLoopProg 64 :=
.mark loopBody189_6

def loopBody189_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 128#64)

def loopBody189_9 : HolLoopProg 64 :=
.mark loopBody189_8

def loopBody189_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody189_11 : HolLoopProg 64 :=
.mark loopBody189_10

def loopBody189_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody189_11, loopBody189_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody189_13 : HolLoopProg 64 :=
.mark loopBody189_12

def loopBody189_14 : HolLoopProg 64 :=
.seq loopBody189_13 loopBody189_1

def loopBody189_15 : HolLoopProg 64 :=
.mark loopBody189_14

def loopBody189_16 : HolLoopProg 64 :=
.seq loopBody189_9 loopBody189_15

def loopBody189_17 : HolLoopProg 64 :=
.mark loopBody189_16

def loopBody189_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody189_19 : HolLoopProg 64 :=
.mark loopBody189_18

def loopBody189_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody189_21 : HolLoopProg 64 :=
.mark loopBody189_20

def loopBody189_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody189_23 : HolLoopProg 64 :=
.mark loopBody189_22

def loopBody189_24 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 244) ([5, 6]) (some (5, loopBody189_23, loopBody189_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody189_25 : HolLoopProg 64 :=
.mark loopBody189_24

def loopBody189_26 : HolLoopProg 64 :=
.seq loopBody189_25 loopBody189_1

def loopBody189_27 : HolLoopProg 64 :=
.mark loopBody189_26

def loopBody189_28 : HolLoopProg 64 :=
.seq loopBody189_21 loopBody189_27

def loopBody189_29 : HolLoopProg 64 :=
.mark loopBody189_28

def loopBody189_30 : HolLoopProg 64 :=
.seq loopBody189_19 loopBody189_29

def loopBody189_31 : HolLoopProg 64 :=
.mark loopBody189_30

def loopBody189_32 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_31

def loopBody189_33 : HolLoopProg 64 :=
.mark loopBody189_32

def loopBody189_34 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_33

def loopBody189_35 : HolLoopProg 64 :=
.mark loopBody189_34

def loopBody189_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64])

def loopBody189_37 : HolLoopProg 64 :=
.mark loopBody189_36

def loopBody189_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 32#64])

def loopBody189_39 : HolLoopProg 64 :=
.mark loopBody189_38

def loopBody189_40 : HolLoopProg 64 :=
.seq loopBody189_39 loopBody189_27

def loopBody189_41 : HolLoopProg 64 :=
.mark loopBody189_40

def loopBody189_42 : HolLoopProg 64 :=
.seq loopBody189_37 loopBody189_41

def loopBody189_43 : HolLoopProg 64 :=
.mark loopBody189_42

def loopBody189_44 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_43

def loopBody189_45 : HolLoopProg 64 :=
.mark loopBody189_44

def loopBody189_46 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_45

def loopBody189_47 : HolLoopProg 64 :=
.mark loopBody189_46

def loopBody189_48 : HolLoopProg 64 :=
.seq loopBody189_35 loopBody189_47

def loopBody189_49 : HolLoopProg 64 :=
.mark loopBody189_48

def loopBody189_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64])

def loopBody189_51 : HolLoopProg 64 :=
.mark loopBody189_50

def loopBody189_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 20#64)

def loopBody189_53 : HolLoopProg 64 :=
.mark loopBody189_52

def loopBody189_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 64#64])

def loopBody189_55 : HolLoopProg 64 :=
.mark loopBody189_54

def loopBody189_56 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 242) ([5, 6, 7]) (some (5, loopBody189_23, loopBody189_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody189_57 : HolLoopProg 64 :=
.mark loopBody189_56

def loopBody189_58 : HolLoopProg 64 :=
.seq loopBody189_57 loopBody189_1

def loopBody189_59 : HolLoopProg 64 :=
.mark loopBody189_58

def loopBody189_60 : HolLoopProg 64 :=
.seq loopBody189_55 loopBody189_59

def loopBody189_61 : HolLoopProg 64 :=
.mark loopBody189_60

def loopBody189_62 : HolLoopProg 64 :=
.seq loopBody189_53 loopBody189_61

def loopBody189_63 : HolLoopProg 64 :=
.mark loopBody189_62

def loopBody189_64 : HolLoopProg 64 :=
.seq loopBody189_51 loopBody189_63

def loopBody189_65 : HolLoopProg 64 :=
.mark loopBody189_64

def loopBody189_66 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_65

def loopBody189_67 : HolLoopProg 64 :=
.mark loopBody189_66

def loopBody189_68 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_67

def loopBody189_69 : HolLoopProg 64 :=
.mark loopBody189_68

def loopBody189_70 : HolLoopProg 64 :=
.seq loopBody189_49 loopBody189_69

def loopBody189_71 : HolLoopProg 64 :=
.mark loopBody189_70

def loopBody189_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 36#64])

def loopBody189_73 : HolLoopProg 64 :=
.mark loopBody189_72

def loopBody189_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 96#64])

def loopBody189_75 : HolLoopProg 64 :=
.mark loopBody189_74

def loopBody189_76 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 244) ([5, 6]) (some (5, loopBody189_23, loopBody189_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody189_77 : HolLoopProg 64 :=
.mark loopBody189_76

def loopBody189_78 : HolLoopProg 64 :=
.seq loopBody189_77 loopBody189_1

def loopBody189_79 : HolLoopProg 64 :=
.mark loopBody189_78

def loopBody189_80 : HolLoopProg 64 :=
.seq loopBody189_75 loopBody189_79

def loopBody189_81 : HolLoopProg 64 :=
.mark loopBody189_80

def loopBody189_82 : HolLoopProg 64 :=
.seq loopBody189_73 loopBody189_81

def loopBody189_83 : HolLoopProg 64 :=
.mark loopBody189_82

def loopBody189_84 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_83

def loopBody189_85 : HolLoopProg 64 :=
.mark loopBody189_84

def loopBody189_86 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_85

def loopBody189_87 : HolLoopProg 64 :=
.mark loopBody189_86

def loopBody189_88 : HolLoopProg 64 :=
.seq loopBody189_71 loopBody189_87

def loopBody189_89 : HolLoopProg 64 :=
.mark loopBody189_88

def loopBody189_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody189_91 : HolLoopProg 64 :=
.mark loopBody189_90

def loopBody189_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 4#64)

def loopBody189_93 : HolLoopProg 64 :=
.mark loopBody189_92

def loopBody189_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 4#64)

def loopBody189_95 : HolLoopProg 64 :=
.mark loopBody189_94

def loopBody189_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody189_97 : HolLoopProg 64 :=
.mark loopBody189_96

def loopBody189_98 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 235) ([5, 6, 7, 8]) (some (5, loopBody189_23, loopBody189_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody189_99 : HolLoopProg 64 :=
.mark loopBody189_98

def loopBody189_100 : HolLoopProg 64 :=
.seq loopBody189_99 loopBody189_1

def loopBody189_101 : HolLoopProg 64 :=
.mark loopBody189_100

def loopBody189_102 : HolLoopProg 64 :=
.seq loopBody189_97 loopBody189_101

def loopBody189_103 : HolLoopProg 64 :=
.mark loopBody189_102

def loopBody189_104 : HolLoopProg 64 :=
.seq loopBody189_95 loopBody189_103

def loopBody189_105 : HolLoopProg 64 :=
.mark loopBody189_104

def loopBody189_106 : HolLoopProg 64 :=
.seq loopBody189_93 loopBody189_105

def loopBody189_107 : HolLoopProg 64 :=
.mark loopBody189_106

def loopBody189_108 : HolLoopProg 64 :=
.seq loopBody189_91 loopBody189_107

def loopBody189_109 : HolLoopProg 64 :=
.mark loopBody189_108

def loopBody189_110 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_109

def loopBody189_111 : HolLoopProg 64 :=
.mark loopBody189_110

def loopBody189_112 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_111

def loopBody189_113 : HolLoopProg 64 :=
.mark loopBody189_112

def loopBody189_114 : HolLoopProg 64 :=
.seq loopBody189_89 loopBody189_113

def loopBody189_115 : HolLoopProg 64 :=
.mark loopBody189_114

def loopBody189_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody189_117 : HolLoopProg 64 :=
.mark loopBody189_116

def loopBody189_118 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody189_23, loopBody189_1, (Flapjack.Spt.ln)))

def loopBody189_119 : HolLoopProg 64 :=
.mark loopBody189_118

def loopBody189_120 : HolLoopProg 64 :=
.seq loopBody189_119 loopBody189_1

def loopBody189_121 : HolLoopProg 64 :=
.mark loopBody189_120

def loopBody189_122 : HolLoopProg 64 :=
.seq loopBody189_117 loopBody189_121

def loopBody189_123 : HolLoopProg 64 :=
.mark loopBody189_122

def loopBody189_124 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_123

def loopBody189_125 : HolLoopProg 64 :=
.mark loopBody189_124

def loopBody189_126 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_125

def loopBody189_127 : HolLoopProg 64 :=
.mark loopBody189_126

def loopBody189_128 : HolLoopProg 64 :=
.seq loopBody189_115 loopBody189_127

def loopBody189_129 : HolLoopProg 64 :=
.mark loopBody189_128

def loopBody189_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody189_131 : HolLoopProg 64 :=
.mark loopBody189_130

def loopBody189_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody189_133 : HolLoopProg 64 :=
.mark loopBody189_132

def loopBody189_134 : HolLoopProg 64 :=
.seq loopBody189_133 loopBody189_1

def loopBody189_135 : HolLoopProg 64 :=
.mark loopBody189_134

def loopBody189_136 : HolLoopProg 64 :=
.seq loopBody189_131 loopBody189_135

def loopBody189_137 : HolLoopProg 64 :=
.mark loopBody189_136

def loopBody189_138 : HolLoopProg 64 :=
.seq loopBody189_129 loopBody189_137

def loopBody189_139 : HolLoopProg 64 :=
.mark loopBody189_138

def loopBody189_140 : HolLoopProg 64 :=
.seq loopBody189_17 loopBody189_139

def loopBody189_141 : HolLoopProg 64 :=
.mark loopBody189_140

def loopBody189_142 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_141

def loopBody189_143 : HolLoopProg 64 :=
.mark loopBody189_142

def loopBody189_144 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_143

def loopBody189_145 : HolLoopProg 64 :=
.mark loopBody189_144

def loopBody189_146 : HolLoopProg 64 :=
.seq loopBody189_7 loopBody189_145

def loopBody189_147 : HolLoopProg 64 :=
.mark loopBody189_146

def loopBody189_148 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_147

def loopBody189_149 : HolLoopProg 64 :=
.mark loopBody189_148

def loopBody189_150 : HolLoopProg 64 :=
.seq loopBody189_1 loopBody189_149

def loopBody189_151 : HolLoopProg 64 :=
.mark loopBody189_150

def output189 : Nat × List Nat × HolLoopProg 64 :=
  (253, [0, 1], loopBody189_151)
end InitECandidate.Proofs.FrontendStages.Loop
