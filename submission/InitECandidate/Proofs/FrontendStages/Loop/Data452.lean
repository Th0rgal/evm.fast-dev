import InitECandidate.Proofs.FrontendStages.Loop.Translate436
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody452_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody452_1 : HolLoopProg 64 :=
.mark loopBody452_0

def loopBody452_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody452_3 : HolLoopProg 64 :=
.mark loopBody452_2

def loopBody452_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody452_3, loopBody452_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody452_5 : HolLoopProg 64 :=
.mark loopBody452_4

def loopBody452_6 : HolLoopProg 64 :=
.seq loopBody452_5 loopBody452_1

def loopBody452_7 : HolLoopProg 64 :=
.mark loopBody452_6

def loopBody452_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody452_9 : HolLoopProg 64 :=
.mark loopBody452_8

def loopBody452_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody452_9, loopBody452_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody452_11 : HolLoopProg 64 :=
.mark loopBody452_10

def loopBody452_12 : HolLoopProg 64 :=
.seq loopBody452_11 loopBody452_1

def loopBody452_13 : HolLoopProg 64 :=
.mark loopBody452_12

def loopBody452_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody452_15 : HolLoopProg 64 :=
.mark loopBody452_14

def loopBody452_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody452_17 : HolLoopProg 64 :=
.mark loopBody452_16

def loopBody452_18 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 466) ([10]) (some (10, loopBody452_17, loopBody452_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody452_19 : HolLoopProg 64 :=
.mark loopBody452_18

def loopBody452_20 : HolLoopProg 64 :=
.seq loopBody452_19 loopBody452_1

def loopBody452_21 : HolLoopProg 64 :=
.mark loopBody452_20

def loopBody452_22 : HolLoopProg 64 :=
.seq loopBody452_15 loopBody452_21

def loopBody452_23 : HolLoopProg 64 :=
.mark loopBody452_22

def loopBody452_24 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_23

def loopBody452_25 : HolLoopProg 64 :=
.mark loopBody452_24

def loopBody452_26 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_25

def loopBody452_27 : HolLoopProg 64 :=
.mark loopBody452_26

def loopBody452_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody452_29 : HolLoopProg 64 :=
.mark loopBody452_28

def loopBody452_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody452_31 : HolLoopProg 64 :=
.mark loopBody452_30

def loopBody452_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody452_33 : HolLoopProg 64 :=
.mark loopBody452_32

def loopBody452_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody452_35 : HolLoopProg 64 :=
.mark loopBody452_34

def loopBody452_36 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 458) ([10, 11, 12, 13]) (some (10, loopBody452_17, loopBody452_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody452_37 : HolLoopProg 64 :=
.mark loopBody452_36

def loopBody452_38 : HolLoopProg 64 :=
.seq loopBody452_37 loopBody452_1

def loopBody452_39 : HolLoopProg 64 :=
.mark loopBody452_38

def loopBody452_40 : HolLoopProg 64 :=
.seq loopBody452_35 loopBody452_39

def loopBody452_41 : HolLoopProg 64 :=
.mark loopBody452_40

def loopBody452_42 : HolLoopProg 64 :=
.seq loopBody452_33 loopBody452_41

def loopBody452_43 : HolLoopProg 64 :=
.mark loopBody452_42

def loopBody452_44 : HolLoopProg 64 :=
.seq loopBody452_31 loopBody452_43

def loopBody452_45 : HolLoopProg 64 :=
.mark loopBody452_44

def loopBody452_46 : HolLoopProg 64 :=
.seq loopBody452_29 loopBody452_45

def loopBody452_47 : HolLoopProg 64 :=
.mark loopBody452_46

def loopBody452_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 5)

def loopBody452_49 : HolLoopProg 64 :=
.mark loopBody452_48

def loopBody452_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 6)

def loopBody452_51 : HolLoopProg 64 :=
.mark loopBody452_50

def loopBody452_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 7)

def loopBody452_53 : HolLoopProg 64 :=
.mark loopBody452_52

def loopBody452_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 8)

def loopBody452_55 : HolLoopProg 64 :=
.mark loopBody452_54

def loopBody452_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 9)

def loopBody452_57 : HolLoopProg 64 :=
.mark loopBody452_56

def loopBody452_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 14

def loopBody452_59 : HolLoopProg 64 :=
.mark loopBody452_58

def loopBody452_60 : HolLoopProg 64 :=
.call (some ([10, 11, 12, 13], Flapjack.Spt.ln)) (some 142) ([14, 15, 16, 17, 18]) (some (14, loopBody452_59, loopBody452_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody452_61 : HolLoopProg 64 :=
.mark loopBody452_60

def loopBody452_62 : HolLoopProg 64 :=
.seq loopBody452_61 loopBody452_1

def loopBody452_63 : HolLoopProg 64 :=
.mark loopBody452_62

def loopBody452_64 : HolLoopProg 64 :=
.seq loopBody452_57 loopBody452_63

def loopBody452_65 : HolLoopProg 64 :=
.mark loopBody452_64

def loopBody452_66 : HolLoopProg 64 :=
.seq loopBody452_55 loopBody452_65

def loopBody452_67 : HolLoopProg 64 :=
.mark loopBody452_66

def loopBody452_68 : HolLoopProg 64 :=
.seq loopBody452_53 loopBody452_67

def loopBody452_69 : HolLoopProg 64 :=
.mark loopBody452_68

def loopBody452_70 : HolLoopProg 64 :=
.seq loopBody452_51 loopBody452_69

def loopBody452_71 : HolLoopProg 64 :=
.mark loopBody452_70

def loopBody452_72 : HolLoopProg 64 :=
.seq loopBody452_49 loopBody452_71

def loopBody452_73 : HolLoopProg 64 :=
.mark loopBody452_72

def loopBody452_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 10)

def loopBody452_75 : HolLoopProg 64 :=
.mark loopBody452_74

def loopBody452_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 11)

def loopBody452_77 : HolLoopProg 64 :=
.mark loopBody452_76

def loopBody452_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 12)

def loopBody452_79 : HolLoopProg 64 :=
.mark loopBody452_78

def loopBody452_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 13)

def loopBody452_81 : HolLoopProg 64 :=
.mark loopBody452_80

def loopBody452_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 15

def loopBody452_83 : HolLoopProg 64 :=
.mark loopBody452_82

def loopBody452_84 : HolLoopProg 64 :=
.call (some ([14], Flapjack.Spt.ln)) (some 472) ([15, 16, 17, 18]) (some (15, loopBody452_83, loopBody452_1, (Flapjack.Spt.ln)))

def loopBody452_85 : HolLoopProg 64 :=
.mark loopBody452_84

def loopBody452_86 : HolLoopProg 64 :=
.seq loopBody452_85 loopBody452_1

def loopBody452_87 : HolLoopProg 64 :=
.mark loopBody452_86

def loopBody452_88 : HolLoopProg 64 :=
.seq loopBody452_81 loopBody452_87

def loopBody452_89 : HolLoopProg 64 :=
.mark loopBody452_88

def loopBody452_90 : HolLoopProg 64 :=
.seq loopBody452_79 loopBody452_89

def loopBody452_91 : HolLoopProg 64 :=
.mark loopBody452_90

def loopBody452_92 : HolLoopProg 64 :=
.seq loopBody452_77 loopBody452_91

def loopBody452_93 : HolLoopProg 64 :=
.mark loopBody452_92

def loopBody452_94 : HolLoopProg 64 :=
.seq loopBody452_75 loopBody452_93

def loopBody452_95 : HolLoopProg 64 :=
.mark loopBody452_94

def loopBody452_96 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_95

def loopBody452_97 : HolLoopProg 64 :=
.mark loopBody452_96

def loopBody452_98 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_97

def loopBody452_99 : HolLoopProg 64 :=
.mark loopBody452_98

def loopBody452_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 1#64)

def loopBody452_101 : HolLoopProg 64 :=
.mark loopBody452_100

def loopBody452_102 : HolLoopProg 64 :=
.call (some ([14], Flapjack.Spt.ln)) (some 486) ([15]) (some (15, loopBody452_83, loopBody452_1, (Flapjack.Spt.ln)))

def loopBody452_103 : HolLoopProg 64 :=
.mark loopBody452_102

def loopBody452_104 : HolLoopProg 64 :=
.seq loopBody452_103 loopBody452_1

def loopBody452_105 : HolLoopProg 64 :=
.mark loopBody452_104

def loopBody452_106 : HolLoopProg 64 :=
.seq loopBody452_101 loopBody452_105

def loopBody452_107 : HolLoopProg 64 :=
.mark loopBody452_106

def loopBody452_108 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_107

def loopBody452_109 : HolLoopProg 64 :=
.mark loopBody452_108

def loopBody452_110 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_109

def loopBody452_111 : HolLoopProg 64 :=
.mark loopBody452_110

def loopBody452_112 : HolLoopProg 64 :=
.seq loopBody452_99 loopBody452_111

def loopBody452_113 : HolLoopProg 64 :=
.mark loopBody452_112

def loopBody452_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody452_115 : HolLoopProg 64 :=
.mark loopBody452_114

def loopBody452_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [14]

def loopBody452_117 : HolLoopProg 64 :=
.mark loopBody452_116

def loopBody452_118 : HolLoopProg 64 :=
.seq loopBody452_117 loopBody452_1

def loopBody452_119 : HolLoopProg 64 :=
.mark loopBody452_118

def loopBody452_120 : HolLoopProg 64 :=
.seq loopBody452_115 loopBody452_119

def loopBody452_121 : HolLoopProg 64 :=
.mark loopBody452_120

def loopBody452_122 : HolLoopProg 64 :=
.seq loopBody452_113 loopBody452_121

def loopBody452_123 : HolLoopProg 64 :=
.mark loopBody452_122

def loopBody452_124 : HolLoopProg 64 :=
.seq loopBody452_73 loopBody452_123

def loopBody452_125 : HolLoopProg 64 :=
.mark loopBody452_124

def loopBody452_126 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_125

def loopBody452_127 : HolLoopProg 64 :=
.mark loopBody452_126

def loopBody452_128 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_127

def loopBody452_129 : HolLoopProg 64 :=
.mark loopBody452_128

def loopBody452_130 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_129

def loopBody452_131 : HolLoopProg 64 :=
.mark loopBody452_130

def loopBody452_132 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_131

def loopBody452_133 : HolLoopProg 64 :=
.mark loopBody452_132

def loopBody452_134 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_133

def loopBody452_135 : HolLoopProg 64 :=
.mark loopBody452_134

def loopBody452_136 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_135

def loopBody452_137 : HolLoopProg 64 :=
.mark loopBody452_136

def loopBody452_138 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_137

def loopBody452_139 : HolLoopProg 64 :=
.mark loopBody452_138

def loopBody452_140 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_139

def loopBody452_141 : HolLoopProg 64 :=
.mark loopBody452_140

def loopBody452_142 : HolLoopProg 64 :=
.seq loopBody452_47 loopBody452_141

def loopBody452_143 : HolLoopProg 64 :=
.mark loopBody452_142

def loopBody452_144 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_143

def loopBody452_145 : HolLoopProg 64 :=
.mark loopBody452_144

def loopBody452_146 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_145

def loopBody452_147 : HolLoopProg 64 :=
.mark loopBody452_146

def loopBody452_148 : HolLoopProg 64 :=
.seq loopBody452_27 loopBody452_147

def loopBody452_149 : HolLoopProg 64 :=
.mark loopBody452_148

def loopBody452_150 : HolLoopProg 64 :=
.seq loopBody452_13 loopBody452_149

def loopBody452_151 : HolLoopProg 64 :=
.mark loopBody452_150

def loopBody452_152 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_151

def loopBody452_153 : HolLoopProg 64 :=
.mark loopBody452_152

def loopBody452_154 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_153

def loopBody452_155 : HolLoopProg 64 :=
.mark loopBody452_154

def loopBody452_156 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_155

def loopBody452_157 : HolLoopProg 64 :=
.mark loopBody452_156

def loopBody452_158 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_157

def loopBody452_159 : HolLoopProg 64 :=
.mark loopBody452_158

def loopBody452_160 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_159

def loopBody452_161 : HolLoopProg 64 :=
.mark loopBody452_160

def loopBody452_162 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_161

def loopBody452_163 : HolLoopProg 64 :=
.mark loopBody452_162

def loopBody452_164 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_163

def loopBody452_165 : HolLoopProg 64 :=
.mark loopBody452_164

def loopBody452_166 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_165

def loopBody452_167 : HolLoopProg 64 :=
.mark loopBody452_166

def loopBody452_168 : HolLoopProg 64 :=
.seq loopBody452_7 loopBody452_167

def loopBody452_169 : HolLoopProg 64 :=
.mark loopBody452_168

def loopBody452_170 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_169

def loopBody452_171 : HolLoopProg 64 :=
.mark loopBody452_170

def loopBody452_172 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_171

def loopBody452_173 : HolLoopProg 64 :=
.mark loopBody452_172

def loopBody452_174 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_173

def loopBody452_175 : HolLoopProg 64 :=
.mark loopBody452_174

def loopBody452_176 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_175

def loopBody452_177 : HolLoopProg 64 :=
.mark loopBody452_176

def loopBody452_178 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_177

def loopBody452_179 : HolLoopProg 64 :=
.mark loopBody452_178

def loopBody452_180 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_179

def loopBody452_181 : HolLoopProg 64 :=
.mark loopBody452_180

def loopBody452_182 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_181

def loopBody452_183 : HolLoopProg 64 :=
.mark loopBody452_182

def loopBody452_184 : HolLoopProg 64 :=
.seq loopBody452_1 loopBody452_183

def loopBody452_185 : HolLoopProg 64 :=
.mark loopBody452_184

def output452 : Nat × List Nat × HolLoopProg 64 :=
  (516, [], loopBody452_185)
end InitECandidate.Proofs.FrontendStages.Loop
