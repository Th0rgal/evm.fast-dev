import InitECandidate.Proofs.FrontendStages.Loop.Translate344
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody360_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody360_1 : HolLoopProg 64 :=
.mark loopBody360_0

def loopBody360_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody360_3 : HolLoopProg 64 :=
.mark loopBody360_2

def loopBody360_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody360_5 : HolLoopProg 64 :=
.mark loopBody360_4

def loopBody360_6 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 403) ([6]) (some (6, loopBody360_5, loopBody360_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody360_7 : HolLoopProg 64 :=
.mark loopBody360_6

def loopBody360_8 : HolLoopProg 64 :=
.seq loopBody360_7 loopBody360_1

def loopBody360_9 : HolLoopProg 64 :=
.mark loopBody360_8

def loopBody360_10 : HolLoopProg 64 :=
.seq loopBody360_3 loopBody360_9

def loopBody360_11 : HolLoopProg 64 :=
.mark loopBody360_10

def loopBody360_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody360_13 : HolLoopProg 64 :=
.mark loopBody360_12

def loopBody360_14 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 391) ([6]) (some (6, loopBody360_5, loopBody360_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody360_15 : HolLoopProg 64 :=
.mark loopBody360_14

def loopBody360_16 : HolLoopProg 64 :=
.seq loopBody360_15 loopBody360_1

def loopBody360_17 : HolLoopProg 64 :=
.mark loopBody360_16

def loopBody360_18 : HolLoopProg 64 :=
.seq loopBody360_13 loopBody360_17

def loopBody360_19 : HolLoopProg 64 :=
.mark loopBody360_18

def loopBody360_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 8#64]))

def loopBody360_21 : HolLoopProg 64 :=
.mark loopBody360_20

def loopBody360_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody360_23 : HolLoopProg 64 :=
.mark loopBody360_22

def loopBody360_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody360_25 : HolLoopProg 64 :=
.mark loopBody360_24

def loopBody360_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody360_27 : HolLoopProg 64 :=
.mark loopBody360_26

def loopBody360_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 1)

def loopBody360_29 : HolLoopProg 64 :=
.mark loopBody360_28

def loopBody360_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 2)

def loopBody360_31 : HolLoopProg 64 :=
.mark loopBody360_30

def loopBody360_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 3)

def loopBody360_33 : HolLoopProg 64 :=
.mark loopBody360_32

def loopBody360_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 4)

def loopBody360_35 : HolLoopProg 64 :=
.mark loopBody360_34

def loopBody360_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody360_37 : HolLoopProg 64 :=
.mark loopBody360_36

def loopBody360_38 : HolLoopProg 64 :=
.call (some
  ([6, 7, 8, 9],
    Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 116) ([10, 11, 12, 13, 14, 15, 16, 17]) (some (10, loopBody360_37, loopBody360_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody360_39 : HolLoopProg 64 :=
.mark loopBody360_38

def loopBody360_40 : HolLoopProg 64 :=
.seq loopBody360_39 loopBody360_1

def loopBody360_41 : HolLoopProg 64 :=
.mark loopBody360_40

def loopBody360_42 : HolLoopProg 64 :=
.seq loopBody360_35 loopBody360_41

def loopBody360_43 : HolLoopProg 64 :=
.mark loopBody360_42

def loopBody360_44 : HolLoopProg 64 :=
.seq loopBody360_33 loopBody360_43

def loopBody360_45 : HolLoopProg 64 :=
.mark loopBody360_44

def loopBody360_46 : HolLoopProg 64 :=
.seq loopBody360_31 loopBody360_45

def loopBody360_47 : HolLoopProg 64 :=
.mark loopBody360_46

def loopBody360_48 : HolLoopProg 64 :=
.seq loopBody360_29 loopBody360_47

def loopBody360_49 : HolLoopProg 64 :=
.mark loopBody360_48

def loopBody360_50 : HolLoopProg 64 :=
.seq loopBody360_27 loopBody360_49

def loopBody360_51 : HolLoopProg 64 :=
.mark loopBody360_50

def loopBody360_52 : HolLoopProg 64 :=
.seq loopBody360_25 loopBody360_51

def loopBody360_53 : HolLoopProg 64 :=
.mark loopBody360_52

def loopBody360_54 : HolLoopProg 64 :=
.seq loopBody360_23 loopBody360_53

def loopBody360_55 : HolLoopProg 64 :=
.mark loopBody360_54

def loopBody360_56 : HolLoopProg 64 :=
.seq loopBody360_21 loopBody360_55

def loopBody360_57 : HolLoopProg 64 :=
.mark loopBody360_56

def loopBody360_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 8#64])

def loopBody360_59 : HolLoopProg 64 :=
.mark loopBody360_58

def loopBody360_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody360_61 : HolLoopProg 64 :=
.mark loopBody360_60

def loopBody360_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 7)

def loopBody360_63 : HolLoopProg 64 :=
.mark loopBody360_62

def loopBody360_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 8)

def loopBody360_65 : HolLoopProg 64 :=
.mark loopBody360_64

def loopBody360_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody360_67 : HolLoopProg 64 :=
.mark loopBody360_66

def loopBody360_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 11)

def loopBody360_69 : HolLoopProg 64 :=
.mark loopBody360_68

def loopBody360_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 10) 15

def loopBody360_71 : HolLoopProg 64 :=
.mark loopBody360_70

def loopBody360_72 : HolLoopProg 64 :=
.seq loopBody360_71 loopBody360_1

def loopBody360_73 : HolLoopProg 64 :=
.mark loopBody360_72

def loopBody360_74 : HolLoopProg 64 :=
.seq loopBody360_69 loopBody360_73

def loopBody360_75 : HolLoopProg 64 :=
.mark loopBody360_74

def loopBody360_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 12)

def loopBody360_77 : HolLoopProg 64 :=
.mark loopBody360_76

def loopBody360_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.const 8#64]) 15

def loopBody360_79 : HolLoopProg 64 :=
.mark loopBody360_78

def loopBody360_80 : HolLoopProg 64 :=
.seq loopBody360_79 loopBody360_1

def loopBody360_81 : HolLoopProg 64 :=
.mark loopBody360_80

def loopBody360_82 : HolLoopProg 64 :=
.seq loopBody360_77 loopBody360_81

def loopBody360_83 : HolLoopProg 64 :=
.mark loopBody360_82

def loopBody360_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 13)

def loopBody360_85 : HolLoopProg 64 :=
.mark loopBody360_84

def loopBody360_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.const 16#64]) 15

def loopBody360_87 : HolLoopProg 64 :=
.mark loopBody360_86

def loopBody360_88 : HolLoopProg 64 :=
.seq loopBody360_87 loopBody360_1

def loopBody360_89 : HolLoopProg 64 :=
.mark loopBody360_88

def loopBody360_90 : HolLoopProg 64 :=
.seq loopBody360_85 loopBody360_89

def loopBody360_91 : HolLoopProg 64 :=
.mark loopBody360_90

def loopBody360_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 14)

def loopBody360_93 : HolLoopProg 64 :=
.mark loopBody360_92

def loopBody360_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.const 24#64]) 15

def loopBody360_95 : HolLoopProg 64 :=
.mark loopBody360_94

def loopBody360_96 : HolLoopProg 64 :=
.seq loopBody360_95 loopBody360_1

def loopBody360_97 : HolLoopProg 64 :=
.mark loopBody360_96

def loopBody360_98 : HolLoopProg 64 :=
.seq loopBody360_93 loopBody360_97

def loopBody360_99 : HolLoopProg 64 :=
.mark loopBody360_98

def loopBody360_100 : HolLoopProg 64 :=
.seq loopBody360_99 loopBody360_1

def loopBody360_101 : HolLoopProg 64 :=
.mark loopBody360_100

def loopBody360_102 : HolLoopProg 64 :=
.seq loopBody360_91 loopBody360_101

def loopBody360_103 : HolLoopProg 64 :=
.mark loopBody360_102

def loopBody360_104 : HolLoopProg 64 :=
.seq loopBody360_83 loopBody360_103

def loopBody360_105 : HolLoopProg 64 :=
.mark loopBody360_104

def loopBody360_106 : HolLoopProg 64 :=
.seq loopBody360_75 loopBody360_105

def loopBody360_107 : HolLoopProg 64 :=
.mark loopBody360_106

def loopBody360_108 : HolLoopProg 64 :=
.seq loopBody360_67 loopBody360_107

def loopBody360_109 : HolLoopProg 64 :=
.mark loopBody360_108

def loopBody360_110 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_109

def loopBody360_111 : HolLoopProg 64 :=
.mark loopBody360_110

def loopBody360_112 : HolLoopProg 64 :=
.seq loopBody360_65 loopBody360_111

def loopBody360_113 : HolLoopProg 64 :=
.mark loopBody360_112

def loopBody360_114 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_113

def loopBody360_115 : HolLoopProg 64 :=
.mark loopBody360_114

def loopBody360_116 : HolLoopProg 64 :=
.seq loopBody360_63 loopBody360_115

def loopBody360_117 : HolLoopProg 64 :=
.mark loopBody360_116

def loopBody360_118 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_117

def loopBody360_119 : HolLoopProg 64 :=
.mark loopBody360_118

def loopBody360_120 : HolLoopProg 64 :=
.seq loopBody360_61 loopBody360_119

def loopBody360_121 : HolLoopProg 64 :=
.mark loopBody360_120

def loopBody360_122 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_121

def loopBody360_123 : HolLoopProg 64 :=
.mark loopBody360_122

def loopBody360_124 : HolLoopProg 64 :=
.seq loopBody360_59 loopBody360_123

def loopBody360_125 : HolLoopProg 64 :=
.mark loopBody360_124

def loopBody360_126 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_125

def loopBody360_127 : HolLoopProg 64 :=
.mark loopBody360_126

def loopBody360_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 0)

def loopBody360_129 : HolLoopProg 64 :=
.mark loopBody360_128

def loopBody360_130 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 5)

def loopBody360_131 : HolLoopProg 64 :=
.mark loopBody360_130

def loopBody360_132 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody360_133 : HolLoopProg 64 :=
.mark loopBody360_132

def loopBody360_134 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 419) ([11, 12]) (some (11, loopBody360_133, loopBody360_1, (Flapjack.Spt.ln)))

def loopBody360_135 : HolLoopProg 64 :=
.mark loopBody360_134

def loopBody360_136 : HolLoopProg 64 :=
.seq loopBody360_135 loopBody360_1

def loopBody360_137 : HolLoopProg 64 :=
.mark loopBody360_136

def loopBody360_138 : HolLoopProg 64 :=
.seq loopBody360_131 loopBody360_137

def loopBody360_139 : HolLoopProg 64 :=
.mark loopBody360_138

def loopBody360_140 : HolLoopProg 64 :=
.seq loopBody360_129 loopBody360_139

def loopBody360_141 : HolLoopProg 64 :=
.mark loopBody360_140

def loopBody360_142 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_141

def loopBody360_143 : HolLoopProg 64 :=
.mark loopBody360_142

def loopBody360_144 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_143

def loopBody360_145 : HolLoopProg 64 :=
.mark loopBody360_144

def loopBody360_146 : HolLoopProg 64 :=
.seq loopBody360_127 loopBody360_145

def loopBody360_147 : HolLoopProg 64 :=
.mark loopBody360_146

def loopBody360_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody360_149 : HolLoopProg 64 :=
.mark loopBody360_148

def loopBody360_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [10]

def loopBody360_151 : HolLoopProg 64 :=
.mark loopBody360_150

def loopBody360_152 : HolLoopProg 64 :=
.seq loopBody360_151 loopBody360_1

def loopBody360_153 : HolLoopProg 64 :=
.mark loopBody360_152

def loopBody360_154 : HolLoopProg 64 :=
.seq loopBody360_149 loopBody360_153

def loopBody360_155 : HolLoopProg 64 :=
.mark loopBody360_154

def loopBody360_156 : HolLoopProg 64 :=
.seq loopBody360_147 loopBody360_155

def loopBody360_157 : HolLoopProg 64 :=
.mark loopBody360_156

def loopBody360_158 : HolLoopProg 64 :=
.seq loopBody360_57 loopBody360_157

def loopBody360_159 : HolLoopProg 64 :=
.mark loopBody360_158

def loopBody360_160 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_159

def loopBody360_161 : HolLoopProg 64 :=
.mark loopBody360_160

def loopBody360_162 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_161

def loopBody360_163 : HolLoopProg 64 :=
.mark loopBody360_162

def loopBody360_164 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_163

def loopBody360_165 : HolLoopProg 64 :=
.mark loopBody360_164

def loopBody360_166 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_165

def loopBody360_167 : HolLoopProg 64 :=
.mark loopBody360_166

def loopBody360_168 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_167

def loopBody360_169 : HolLoopProg 64 :=
.mark loopBody360_168

def loopBody360_170 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_169

def loopBody360_171 : HolLoopProg 64 :=
.mark loopBody360_170

def loopBody360_172 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_171

def loopBody360_173 : HolLoopProg 64 :=
.mark loopBody360_172

def loopBody360_174 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_173

def loopBody360_175 : HolLoopProg 64 :=
.mark loopBody360_174

def loopBody360_176 : HolLoopProg 64 :=
.seq loopBody360_19 loopBody360_175

def loopBody360_177 : HolLoopProg 64 :=
.mark loopBody360_176

def loopBody360_178 : HolLoopProg 64 :=
.seq loopBody360_11 loopBody360_177

def loopBody360_179 : HolLoopProg 64 :=
.mark loopBody360_178

def loopBody360_180 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_179

def loopBody360_181 : HolLoopProg 64 :=
.mark loopBody360_180

def loopBody360_182 : HolLoopProg 64 :=
.seq loopBody360_1 loopBody360_181

def loopBody360_183 : HolLoopProg 64 :=
.mark loopBody360_182

def output360 : Nat × List Nat × HolLoopProg 64 :=
  (424, [0, 1, 2, 3, 4], loopBody360_183)
end InitECandidate.Proofs.FrontendStages.Loop
