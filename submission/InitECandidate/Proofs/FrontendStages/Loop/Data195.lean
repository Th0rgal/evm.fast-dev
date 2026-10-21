import InitECandidate.Proofs.FrontendStages.Loop.Translate179
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody195_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody195_1 : HolLoopProg 64 :=
.mark loopBody195_0

def loopBody195_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody195_3 : HolLoopProg 64 :=
.mark loopBody195_2

def loopBody195_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody195_3, loopBody195_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody195_5 : HolLoopProg 64 :=
.mark loopBody195_4

def loopBody195_6 : HolLoopProg 64 :=
.seq loopBody195_5 loopBody195_1

def loopBody195_7 : HolLoopProg 64 :=
.mark loopBody195_6

def loopBody195_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 128#64)

def loopBody195_9 : HolLoopProg 64 :=
.mark loopBody195_8

def loopBody195_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody195_11 : HolLoopProg 64 :=
.mark loopBody195_10

def loopBody195_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody195_11, loopBody195_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody195_13 : HolLoopProg 64 :=
.mark loopBody195_12

def loopBody195_14 : HolLoopProg 64 :=
.seq loopBody195_13 loopBody195_1

def loopBody195_15 : HolLoopProg 64 :=
.mark loopBody195_14

def loopBody195_16 : HolLoopProg 64 :=
.seq loopBody195_9 loopBody195_15

def loopBody195_17 : HolLoopProg 64 :=
.mark loopBody195_16

def loopBody195_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody195_19 : HolLoopProg 64 :=
.mark loopBody195_18

def loopBody195_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 48#64)

def loopBody195_21 : HolLoopProg 64 :=
.mark loopBody195_20

def loopBody195_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody195_23 : HolLoopProg 64 :=
.mark loopBody195_22

def loopBody195_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody195_25 : HolLoopProg 64 :=
.mark loopBody195_24

def loopBody195_26 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 242) ([5, 6, 7]) (some (5, loopBody195_25, loopBody195_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody195_27 : HolLoopProg 64 :=
.mark loopBody195_26

def loopBody195_28 : HolLoopProg 64 :=
.seq loopBody195_27 loopBody195_1

def loopBody195_29 : HolLoopProg 64 :=
.mark loopBody195_28

def loopBody195_30 : HolLoopProg 64 :=
.seq loopBody195_23 loopBody195_29

def loopBody195_31 : HolLoopProg 64 :=
.mark loopBody195_30

def loopBody195_32 : HolLoopProg 64 :=
.seq loopBody195_21 loopBody195_31

def loopBody195_33 : HolLoopProg 64 :=
.mark loopBody195_32

def loopBody195_34 : HolLoopProg 64 :=
.seq loopBody195_19 loopBody195_33

def loopBody195_35 : HolLoopProg 64 :=
.mark loopBody195_34

def loopBody195_36 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_35

def loopBody195_37 : HolLoopProg 64 :=
.mark loopBody195_36

def loopBody195_38 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_37

def loopBody195_39 : HolLoopProg 64 :=
.mark loopBody195_38

def loopBody195_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 32#64])

def loopBody195_41 : HolLoopProg 64 :=
.mark loopBody195_40

def loopBody195_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64])

def loopBody195_43 : HolLoopProg 64 :=
.mark loopBody195_42

def loopBody195_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 32#64)

def loopBody195_45 : HolLoopProg 64 :=
.mark loopBody195_44

def loopBody195_46 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([5, 6, 7]) (some (5, loopBody195_25, loopBody195_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody195_47 : HolLoopProg 64 :=
.mark loopBody195_46

def loopBody195_48 : HolLoopProg 64 :=
.seq loopBody195_47 loopBody195_1

def loopBody195_49 : HolLoopProg 64 :=
.mark loopBody195_48

def loopBody195_50 : HolLoopProg 64 :=
.seq loopBody195_45 loopBody195_49

def loopBody195_51 : HolLoopProg 64 :=
.mark loopBody195_50

def loopBody195_52 : HolLoopProg 64 :=
.seq loopBody195_43 loopBody195_51

def loopBody195_53 : HolLoopProg 64 :=
.mark loopBody195_52

def loopBody195_54 : HolLoopProg 64 :=
.seq loopBody195_41 loopBody195_53

def loopBody195_55 : HolLoopProg 64 :=
.mark loopBody195_54

def loopBody195_56 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_55

def loopBody195_57 : HolLoopProg 64 :=
.mark loopBody195_56

def loopBody195_58 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_57

def loopBody195_59 : HolLoopProg 64 :=
.mark loopBody195_58

def loopBody195_60 : HolLoopProg 64 :=
.seq loopBody195_39 loopBody195_59

def loopBody195_61 : HolLoopProg 64 :=
.mark loopBody195_60

def loopBody195_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 80#64])

def loopBody195_63 : HolLoopProg 64 :=
.mark loopBody195_62

def loopBody195_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 64#64])

def loopBody195_65 : HolLoopProg 64 :=
.mark loopBody195_64

def loopBody195_66 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 244) ([5, 6]) (some (5, loopBody195_25, loopBody195_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody195_67 : HolLoopProg 64 :=
.mark loopBody195_66

def loopBody195_68 : HolLoopProg 64 :=
.seq loopBody195_67 loopBody195_1

def loopBody195_69 : HolLoopProg 64 :=
.mark loopBody195_68

def loopBody195_70 : HolLoopProg 64 :=
.seq loopBody195_65 loopBody195_69

def loopBody195_71 : HolLoopProg 64 :=
.mark loopBody195_70

def loopBody195_72 : HolLoopProg 64 :=
.seq loopBody195_63 loopBody195_71

def loopBody195_73 : HolLoopProg 64 :=
.mark loopBody195_72

def loopBody195_74 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_73

def loopBody195_75 : HolLoopProg 64 :=
.mark loopBody195_74

def loopBody195_76 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_75

def loopBody195_77 : HolLoopProg 64 :=
.mark loopBody195_76

def loopBody195_78 : HolLoopProg 64 :=
.seq loopBody195_61 loopBody195_77

def loopBody195_79 : HolLoopProg 64 :=
.mark loopBody195_78

def loopBody195_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 88#64])

def loopBody195_81 : HolLoopProg 64 :=
.mark loopBody195_80

def loopBody195_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 96#64)

def loopBody195_83 : HolLoopProg 64 :=
.mark loopBody195_82

def loopBody195_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 96#64])

def loopBody195_85 : HolLoopProg 64 :=
.mark loopBody195_84

def loopBody195_86 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 242) ([5, 6, 7]) (some (5, loopBody195_25, loopBody195_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody195_87 : HolLoopProg 64 :=
.mark loopBody195_86

def loopBody195_88 : HolLoopProg 64 :=
.seq loopBody195_87 loopBody195_1

def loopBody195_89 : HolLoopProg 64 :=
.mark loopBody195_88

def loopBody195_90 : HolLoopProg 64 :=
.seq loopBody195_85 loopBody195_89

def loopBody195_91 : HolLoopProg 64 :=
.mark loopBody195_90

def loopBody195_92 : HolLoopProg 64 :=
.seq loopBody195_83 loopBody195_91

def loopBody195_93 : HolLoopProg 64 :=
.mark loopBody195_92

def loopBody195_94 : HolLoopProg 64 :=
.seq loopBody195_81 loopBody195_93

def loopBody195_95 : HolLoopProg 64 :=
.mark loopBody195_94

def loopBody195_96 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_95

def loopBody195_97 : HolLoopProg 64 :=
.mark loopBody195_96

def loopBody195_98 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_97

def loopBody195_99 : HolLoopProg 64 :=
.mark loopBody195_98

def loopBody195_100 : HolLoopProg 64 :=
.seq loopBody195_79 loopBody195_99

def loopBody195_101 : HolLoopProg 64 :=
.mark loopBody195_100

def loopBody195_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody195_103 : HolLoopProg 64 :=
.mark loopBody195_102

def loopBody195_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 4#64)

def loopBody195_105 : HolLoopProg 64 :=
.mark loopBody195_104

def loopBody195_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 4#64)

def loopBody195_107 : HolLoopProg 64 :=
.mark loopBody195_106

def loopBody195_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody195_109 : HolLoopProg 64 :=
.mark loopBody195_108

def loopBody195_110 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 235) ([5, 6, 7, 8]) (some (5, loopBody195_25, loopBody195_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody195_111 : HolLoopProg 64 :=
.mark loopBody195_110

def loopBody195_112 : HolLoopProg 64 :=
.seq loopBody195_111 loopBody195_1

def loopBody195_113 : HolLoopProg 64 :=
.mark loopBody195_112

def loopBody195_114 : HolLoopProg 64 :=
.seq loopBody195_109 loopBody195_113

def loopBody195_115 : HolLoopProg 64 :=
.mark loopBody195_114

def loopBody195_116 : HolLoopProg 64 :=
.seq loopBody195_107 loopBody195_115

def loopBody195_117 : HolLoopProg 64 :=
.mark loopBody195_116

def loopBody195_118 : HolLoopProg 64 :=
.seq loopBody195_105 loopBody195_117

def loopBody195_119 : HolLoopProg 64 :=
.mark loopBody195_118

def loopBody195_120 : HolLoopProg 64 :=
.seq loopBody195_103 loopBody195_119

def loopBody195_121 : HolLoopProg 64 :=
.mark loopBody195_120

def loopBody195_122 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_121

def loopBody195_123 : HolLoopProg 64 :=
.mark loopBody195_122

def loopBody195_124 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_123

def loopBody195_125 : HolLoopProg 64 :=
.mark loopBody195_124

def loopBody195_126 : HolLoopProg 64 :=
.seq loopBody195_101 loopBody195_125

def loopBody195_127 : HolLoopProg 64 :=
.mark loopBody195_126

def loopBody195_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody195_129 : HolLoopProg 64 :=
.mark loopBody195_128

def loopBody195_130 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody195_25, loopBody195_1, (Flapjack.Spt.ln)))

def loopBody195_131 : HolLoopProg 64 :=
.mark loopBody195_130

def loopBody195_132 : HolLoopProg 64 :=
.seq loopBody195_131 loopBody195_1

def loopBody195_133 : HolLoopProg 64 :=
.mark loopBody195_132

def loopBody195_134 : HolLoopProg 64 :=
.seq loopBody195_129 loopBody195_133

def loopBody195_135 : HolLoopProg 64 :=
.mark loopBody195_134

def loopBody195_136 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_135

def loopBody195_137 : HolLoopProg 64 :=
.mark loopBody195_136

def loopBody195_138 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_137

def loopBody195_139 : HolLoopProg 64 :=
.mark loopBody195_138

def loopBody195_140 : HolLoopProg 64 :=
.seq loopBody195_127 loopBody195_139

def loopBody195_141 : HolLoopProg 64 :=
.mark loopBody195_140

def loopBody195_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody195_143 : HolLoopProg 64 :=
.mark loopBody195_142

def loopBody195_144 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody195_145 : HolLoopProg 64 :=
.mark loopBody195_144

def loopBody195_146 : HolLoopProg 64 :=
.seq loopBody195_145 loopBody195_1

def loopBody195_147 : HolLoopProg 64 :=
.mark loopBody195_146

def loopBody195_148 : HolLoopProg 64 :=
.seq loopBody195_143 loopBody195_147

def loopBody195_149 : HolLoopProg 64 :=
.mark loopBody195_148

def loopBody195_150 : HolLoopProg 64 :=
.seq loopBody195_141 loopBody195_149

def loopBody195_151 : HolLoopProg 64 :=
.mark loopBody195_150

def loopBody195_152 : HolLoopProg 64 :=
.seq loopBody195_17 loopBody195_151

def loopBody195_153 : HolLoopProg 64 :=
.mark loopBody195_152

def loopBody195_154 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_153

def loopBody195_155 : HolLoopProg 64 :=
.mark loopBody195_154

def loopBody195_156 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_155

def loopBody195_157 : HolLoopProg 64 :=
.mark loopBody195_156

def loopBody195_158 : HolLoopProg 64 :=
.seq loopBody195_7 loopBody195_157

def loopBody195_159 : HolLoopProg 64 :=
.mark loopBody195_158

def loopBody195_160 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_159

def loopBody195_161 : HolLoopProg 64 :=
.mark loopBody195_160

def loopBody195_162 : HolLoopProg 64 :=
.seq loopBody195_1 loopBody195_161

def loopBody195_163 : HolLoopProg 64 :=
.mark loopBody195_162

def output195 : Nat × List Nat × HolLoopProg 64 :=
  (259, [0, 1], loopBody195_163)
end InitECandidate.Proofs.FrontendStages.Loop
