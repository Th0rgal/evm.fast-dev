import InitECandidate.Proofs.FrontendStages.Loop.Translate176
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody192_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody192_1 : HolLoopProg 64 :=
.mark loopBody192_0

def loopBody192_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody192_3 : HolLoopProg 64 :=
.mark loopBody192_2

def loopBody192_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody192_3, loopBody192_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody192_5 : HolLoopProg 64 :=
.mark loopBody192_4

def loopBody192_6 : HolLoopProg 64 :=
.seq loopBody192_5 loopBody192_1

def loopBody192_7 : HolLoopProg 64 :=
.mark loopBody192_6

def loopBody192_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 160#64)

def loopBody192_9 : HolLoopProg 64 :=
.mark loopBody192_8

def loopBody192_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody192_11 : HolLoopProg 64 :=
.mark loopBody192_10

def loopBody192_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody192_11, loopBody192_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody192_13 : HolLoopProg 64 :=
.mark loopBody192_12

def loopBody192_14 : HolLoopProg 64 :=
.seq loopBody192_13 loopBody192_1

def loopBody192_15 : HolLoopProg 64 :=
.mark loopBody192_14

def loopBody192_16 : HolLoopProg 64 :=
.seq loopBody192_9 loopBody192_15

def loopBody192_17 : HolLoopProg 64 :=
.mark loopBody192_16

def loopBody192_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody192_19 : HolLoopProg 64 :=
.mark loopBody192_18

def loopBody192_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 48#64)

def loopBody192_21 : HolLoopProg 64 :=
.mark loopBody192_20

def loopBody192_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody192_23 : HolLoopProg 64 :=
.mark loopBody192_22

def loopBody192_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody192_25 : HolLoopProg 64 :=
.mark loopBody192_24

def loopBody192_26 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 242) ([5, 6, 7]) (some (5, loopBody192_25, loopBody192_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody192_27 : HolLoopProg 64 :=
.mark loopBody192_26

def loopBody192_28 : HolLoopProg 64 :=
.seq loopBody192_27 loopBody192_1

def loopBody192_29 : HolLoopProg 64 :=
.mark loopBody192_28

def loopBody192_30 : HolLoopProg 64 :=
.seq loopBody192_23 loopBody192_29

def loopBody192_31 : HolLoopProg 64 :=
.mark loopBody192_30

def loopBody192_32 : HolLoopProg 64 :=
.seq loopBody192_21 loopBody192_31

def loopBody192_33 : HolLoopProg 64 :=
.mark loopBody192_32

def loopBody192_34 : HolLoopProg 64 :=
.seq loopBody192_19 loopBody192_33

def loopBody192_35 : HolLoopProg 64 :=
.mark loopBody192_34

def loopBody192_36 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_35

def loopBody192_37 : HolLoopProg 64 :=
.mark loopBody192_36

def loopBody192_38 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_37

def loopBody192_39 : HolLoopProg 64 :=
.mark loopBody192_38

def loopBody192_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 32#64])

def loopBody192_41 : HolLoopProg 64 :=
.mark loopBody192_40

def loopBody192_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64])

def loopBody192_43 : HolLoopProg 64 :=
.mark loopBody192_42

def loopBody192_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 32#64)

def loopBody192_45 : HolLoopProg 64 :=
.mark loopBody192_44

def loopBody192_46 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([5, 6, 7]) (some (5, loopBody192_25, loopBody192_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody192_47 : HolLoopProg 64 :=
.mark loopBody192_46

def loopBody192_48 : HolLoopProg 64 :=
.seq loopBody192_47 loopBody192_1

def loopBody192_49 : HolLoopProg 64 :=
.mark loopBody192_48

def loopBody192_50 : HolLoopProg 64 :=
.seq loopBody192_45 loopBody192_49

def loopBody192_51 : HolLoopProg 64 :=
.mark loopBody192_50

def loopBody192_52 : HolLoopProg 64 :=
.seq loopBody192_43 loopBody192_51

def loopBody192_53 : HolLoopProg 64 :=
.mark loopBody192_52

def loopBody192_54 : HolLoopProg 64 :=
.seq loopBody192_41 loopBody192_53

def loopBody192_55 : HolLoopProg 64 :=
.mark loopBody192_54

def loopBody192_56 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_55

def loopBody192_57 : HolLoopProg 64 :=
.mark loopBody192_56

def loopBody192_58 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_57

def loopBody192_59 : HolLoopProg 64 :=
.mark loopBody192_58

def loopBody192_60 : HolLoopProg 64 :=
.seq loopBody192_39 loopBody192_59

def loopBody192_61 : HolLoopProg 64 :=
.mark loopBody192_60

def loopBody192_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 80#64])

def loopBody192_63 : HolLoopProg 64 :=
.mark loopBody192_62

def loopBody192_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 64#64])

def loopBody192_65 : HolLoopProg 64 :=
.mark loopBody192_64

def loopBody192_66 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 244) ([5, 6]) (some (5, loopBody192_25, loopBody192_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody192_67 : HolLoopProg 64 :=
.mark loopBody192_66

def loopBody192_68 : HolLoopProg 64 :=
.seq loopBody192_67 loopBody192_1

def loopBody192_69 : HolLoopProg 64 :=
.mark loopBody192_68

def loopBody192_70 : HolLoopProg 64 :=
.seq loopBody192_65 loopBody192_69

def loopBody192_71 : HolLoopProg 64 :=
.mark loopBody192_70

def loopBody192_72 : HolLoopProg 64 :=
.seq loopBody192_63 loopBody192_71

def loopBody192_73 : HolLoopProg 64 :=
.mark loopBody192_72

def loopBody192_74 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_73

def loopBody192_75 : HolLoopProg 64 :=
.mark loopBody192_74

def loopBody192_76 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_75

def loopBody192_77 : HolLoopProg 64 :=
.mark loopBody192_76

def loopBody192_78 : HolLoopProg 64 :=
.seq loopBody192_61 loopBody192_77

def loopBody192_79 : HolLoopProg 64 :=
.mark loopBody192_78

def loopBody192_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 88#64])

def loopBody192_81 : HolLoopProg 64 :=
.mark loopBody192_80

def loopBody192_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 96#64)

def loopBody192_83 : HolLoopProg 64 :=
.mark loopBody192_82

def loopBody192_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 96#64])

def loopBody192_85 : HolLoopProg 64 :=
.mark loopBody192_84

def loopBody192_86 : HolLoopProg 64 :=
.seq loopBody192_85 loopBody192_29

def loopBody192_87 : HolLoopProg 64 :=
.mark loopBody192_86

def loopBody192_88 : HolLoopProg 64 :=
.seq loopBody192_83 loopBody192_87

def loopBody192_89 : HolLoopProg 64 :=
.mark loopBody192_88

def loopBody192_90 : HolLoopProg 64 :=
.seq loopBody192_81 loopBody192_89

def loopBody192_91 : HolLoopProg 64 :=
.mark loopBody192_90

def loopBody192_92 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_91

def loopBody192_93 : HolLoopProg 64 :=
.mark loopBody192_92

def loopBody192_94 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_93

def loopBody192_95 : HolLoopProg 64 :=
.mark loopBody192_94

def loopBody192_96 : HolLoopProg 64 :=
.seq loopBody192_79 loopBody192_95

def loopBody192_97 : HolLoopProg 64 :=
.mark loopBody192_96

def loopBody192_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 184#64])

def loopBody192_99 : HolLoopProg 64 :=
.mark loopBody192_98

def loopBody192_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 128#64])

def loopBody192_101 : HolLoopProg 64 :=
.mark loopBody192_100

def loopBody192_102 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 244) ([5, 6]) (some (5, loopBody192_25, loopBody192_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody192_103 : HolLoopProg 64 :=
.mark loopBody192_102

def loopBody192_104 : HolLoopProg 64 :=
.seq loopBody192_103 loopBody192_1

def loopBody192_105 : HolLoopProg 64 :=
.mark loopBody192_104

def loopBody192_106 : HolLoopProg 64 :=
.seq loopBody192_101 loopBody192_105

def loopBody192_107 : HolLoopProg 64 :=
.mark loopBody192_106

def loopBody192_108 : HolLoopProg 64 :=
.seq loopBody192_99 loopBody192_107

def loopBody192_109 : HolLoopProg 64 :=
.mark loopBody192_108

def loopBody192_110 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_109

def loopBody192_111 : HolLoopProg 64 :=
.mark loopBody192_110

def loopBody192_112 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_111

def loopBody192_113 : HolLoopProg 64 :=
.mark loopBody192_112

def loopBody192_114 : HolLoopProg 64 :=
.seq loopBody192_97 loopBody192_113

def loopBody192_115 : HolLoopProg 64 :=
.mark loopBody192_114

def loopBody192_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody192_117 : HolLoopProg 64 :=
.mark loopBody192_116

def loopBody192_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 5#64)

def loopBody192_119 : HolLoopProg 64 :=
.mark loopBody192_118

def loopBody192_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 5#64)

def loopBody192_121 : HolLoopProg 64 :=
.mark loopBody192_120

def loopBody192_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody192_123 : HolLoopProg 64 :=
.mark loopBody192_122

def loopBody192_124 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 235) ([5, 6, 7, 8]) (some (5, loopBody192_25, loopBody192_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody192_125 : HolLoopProg 64 :=
.mark loopBody192_124

def loopBody192_126 : HolLoopProg 64 :=
.seq loopBody192_125 loopBody192_1

def loopBody192_127 : HolLoopProg 64 :=
.mark loopBody192_126

def loopBody192_128 : HolLoopProg 64 :=
.seq loopBody192_123 loopBody192_127

def loopBody192_129 : HolLoopProg 64 :=
.mark loopBody192_128

def loopBody192_130 : HolLoopProg 64 :=
.seq loopBody192_121 loopBody192_129

def loopBody192_131 : HolLoopProg 64 :=
.mark loopBody192_130

def loopBody192_132 : HolLoopProg 64 :=
.seq loopBody192_119 loopBody192_131

def loopBody192_133 : HolLoopProg 64 :=
.mark loopBody192_132

def loopBody192_134 : HolLoopProg 64 :=
.seq loopBody192_117 loopBody192_133

def loopBody192_135 : HolLoopProg 64 :=
.mark loopBody192_134

def loopBody192_136 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_135

def loopBody192_137 : HolLoopProg 64 :=
.mark loopBody192_136

def loopBody192_138 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_137

def loopBody192_139 : HolLoopProg 64 :=
.mark loopBody192_138

def loopBody192_140 : HolLoopProg 64 :=
.seq loopBody192_115 loopBody192_139

def loopBody192_141 : HolLoopProg 64 :=
.mark loopBody192_140

def loopBody192_142 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody192_143 : HolLoopProg 64 :=
.mark loopBody192_142

def loopBody192_144 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody192_25, loopBody192_1, (Flapjack.Spt.ln)))

def loopBody192_145 : HolLoopProg 64 :=
.mark loopBody192_144

def loopBody192_146 : HolLoopProg 64 :=
.seq loopBody192_145 loopBody192_1

def loopBody192_147 : HolLoopProg 64 :=
.mark loopBody192_146

def loopBody192_148 : HolLoopProg 64 :=
.seq loopBody192_143 loopBody192_147

def loopBody192_149 : HolLoopProg 64 :=
.mark loopBody192_148

def loopBody192_150 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_149

def loopBody192_151 : HolLoopProg 64 :=
.mark loopBody192_150

def loopBody192_152 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_151

def loopBody192_153 : HolLoopProg 64 :=
.mark loopBody192_152

def loopBody192_154 : HolLoopProg 64 :=
.seq loopBody192_141 loopBody192_153

def loopBody192_155 : HolLoopProg 64 :=
.mark loopBody192_154

def loopBody192_156 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody192_157 : HolLoopProg 64 :=
.mark loopBody192_156

def loopBody192_158 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody192_159 : HolLoopProg 64 :=
.mark loopBody192_158

def loopBody192_160 : HolLoopProg 64 :=
.seq loopBody192_159 loopBody192_1

def loopBody192_161 : HolLoopProg 64 :=
.mark loopBody192_160

def loopBody192_162 : HolLoopProg 64 :=
.seq loopBody192_157 loopBody192_161

def loopBody192_163 : HolLoopProg 64 :=
.mark loopBody192_162

def loopBody192_164 : HolLoopProg 64 :=
.seq loopBody192_155 loopBody192_163

def loopBody192_165 : HolLoopProg 64 :=
.mark loopBody192_164

def loopBody192_166 : HolLoopProg 64 :=
.seq loopBody192_17 loopBody192_165

def loopBody192_167 : HolLoopProg 64 :=
.mark loopBody192_166

def loopBody192_168 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_167

def loopBody192_169 : HolLoopProg 64 :=
.mark loopBody192_168

def loopBody192_170 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_169

def loopBody192_171 : HolLoopProg 64 :=
.mark loopBody192_170

def loopBody192_172 : HolLoopProg 64 :=
.seq loopBody192_7 loopBody192_171

def loopBody192_173 : HolLoopProg 64 :=
.mark loopBody192_172

def loopBody192_174 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_173

def loopBody192_175 : HolLoopProg 64 :=
.mark loopBody192_174

def loopBody192_176 : HolLoopProg 64 :=
.seq loopBody192_1 loopBody192_175

def loopBody192_177 : HolLoopProg 64 :=
.mark loopBody192_176

def output192 : Nat × List Nat × HolLoopProg 64 :=
  (256, [0, 1], loopBody192_177)
end InitECandidate.Proofs.FrontendStages.Loop
