import InitECandidate.Proofs.FrontendStages.Loop.Translate416
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody432_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody432_1 : HolLoopProg 64 :=
.mark loopBody432_0

def loopBody432_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody432_3 : HolLoopProg 64 :=
.mark loopBody432_2

def loopBody432_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody432_3, loopBody432_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody432_5 : HolLoopProg 64 :=
.mark loopBody432_4

def loopBody432_6 : HolLoopProg 64 :=
.seq loopBody432_5 loopBody432_1

def loopBody432_7 : HolLoopProg 64 :=
.mark loopBody432_6

def loopBody432_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody432_9 : HolLoopProg 64 :=
.mark loopBody432_8

def loopBody432_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody432_9, loopBody432_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody432_11 : HolLoopProg 64 :=
.mark loopBody432_10

def loopBody432_12 : HolLoopProg 64 :=
.seq loopBody432_11 loopBody432_1

def loopBody432_13 : HolLoopProg 64 :=
.mark loopBody432_12

def loopBody432_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 5#64)

def loopBody432_15 : HolLoopProg 64 :=
.mark loopBody432_14

def loopBody432_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody432_17 : HolLoopProg 64 :=
.mark loopBody432_16

def loopBody432_18 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 466) ([10]) (some (10, loopBody432_17, loopBody432_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody432_19 : HolLoopProg 64 :=
.mark loopBody432_18

def loopBody432_20 : HolLoopProg 64 :=
.seq loopBody432_19 loopBody432_1

def loopBody432_21 : HolLoopProg 64 :=
.mark loopBody432_20

def loopBody432_22 : HolLoopProg 64 :=
.seq loopBody432_15 loopBody432_21

def loopBody432_23 : HolLoopProg 64 :=
.mark loopBody432_22

def loopBody432_24 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_23

def loopBody432_25 : HolLoopProg 64 :=
.mark loopBody432_24

def loopBody432_26 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_25

def loopBody432_27 : HolLoopProg 64 :=
.mark loopBody432_26

def loopBody432_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody432_29 : HolLoopProg 64 :=
.mark loopBody432_28

def loopBody432_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody432_31 : HolLoopProg 64 :=
.mark loopBody432_30

def loopBody432_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody432_33 : HolLoopProg 64 :=
.mark loopBody432_32

def loopBody432_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody432_35 : HolLoopProg 64 :=
.mark loopBody432_34

def loopBody432_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody432_37 : HolLoopProg 64 :=
.mark loopBody432_36

def loopBody432_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 6)

def loopBody432_39 : HolLoopProg 64 :=
.mark loopBody432_38

def loopBody432_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 7)

def loopBody432_41 : HolLoopProg 64 :=
.mark loopBody432_40

def loopBody432_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 8)

def loopBody432_43 : HolLoopProg 64 :=
.mark loopBody432_42

def loopBody432_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody432_45 : HolLoopProg 64 :=
.mark loopBody432_44

def loopBody432_46 : HolLoopProg 64 :=
.call (some ([9, 10, 11, 12], Flapjack.Spt.ln)) (some 130) ([13, 14, 15, 16, 17, 18, 19, 20]) (some (13, loopBody432_45, loopBody432_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody432_47 : HolLoopProg 64 :=
.mark loopBody432_46

def loopBody432_48 : HolLoopProg 64 :=
.seq loopBody432_47 loopBody432_1

def loopBody432_49 : HolLoopProg 64 :=
.mark loopBody432_48

def loopBody432_50 : HolLoopProg 64 :=
.seq loopBody432_43 loopBody432_49

def loopBody432_51 : HolLoopProg 64 :=
.mark loopBody432_50

def loopBody432_52 : HolLoopProg 64 :=
.seq loopBody432_41 loopBody432_51

def loopBody432_53 : HolLoopProg 64 :=
.mark loopBody432_52

def loopBody432_54 : HolLoopProg 64 :=
.seq loopBody432_39 loopBody432_53

def loopBody432_55 : HolLoopProg 64 :=
.mark loopBody432_54

def loopBody432_56 : HolLoopProg 64 :=
.seq loopBody432_37 loopBody432_55

def loopBody432_57 : HolLoopProg 64 :=
.mark loopBody432_56

def loopBody432_58 : HolLoopProg 64 :=
.seq loopBody432_35 loopBody432_57

def loopBody432_59 : HolLoopProg 64 :=
.mark loopBody432_58

def loopBody432_60 : HolLoopProg 64 :=
.seq loopBody432_33 loopBody432_59

def loopBody432_61 : HolLoopProg 64 :=
.mark loopBody432_60

def loopBody432_62 : HolLoopProg 64 :=
.seq loopBody432_31 loopBody432_61

def loopBody432_63 : HolLoopProg 64 :=
.mark loopBody432_62

def loopBody432_64 : HolLoopProg 64 :=
.seq loopBody432_29 loopBody432_63

def loopBody432_65 : HolLoopProg 64 :=
.mark loopBody432_64

def loopBody432_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody432_67 : HolLoopProg 64 :=
.mark loopBody432_66

def loopBody432_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 10)

def loopBody432_69 : HolLoopProg 64 :=
.mark loopBody432_68

def loopBody432_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 11)

def loopBody432_71 : HolLoopProg 64 :=
.mark loopBody432_70

def loopBody432_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 12)

def loopBody432_73 : HolLoopProg 64 :=
.mark loopBody432_72

def loopBody432_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 14

def loopBody432_75 : HolLoopProg 64 :=
.mark loopBody432_74

def loopBody432_76 : HolLoopProg 64 :=
.call (some ([13], Flapjack.Spt.ln)) (some 472) ([14, 15, 16, 17]) (some (14, loopBody432_75, loopBody432_1, (Flapjack.Spt.ln)))

def loopBody432_77 : HolLoopProg 64 :=
.mark loopBody432_76

def loopBody432_78 : HolLoopProg 64 :=
.seq loopBody432_77 loopBody432_1

def loopBody432_79 : HolLoopProg 64 :=
.mark loopBody432_78

def loopBody432_80 : HolLoopProg 64 :=
.seq loopBody432_73 loopBody432_79

def loopBody432_81 : HolLoopProg 64 :=
.mark loopBody432_80

def loopBody432_82 : HolLoopProg 64 :=
.seq loopBody432_71 loopBody432_81

def loopBody432_83 : HolLoopProg 64 :=
.mark loopBody432_82

def loopBody432_84 : HolLoopProg 64 :=
.seq loopBody432_69 loopBody432_83

def loopBody432_85 : HolLoopProg 64 :=
.mark loopBody432_84

def loopBody432_86 : HolLoopProg 64 :=
.seq loopBody432_67 loopBody432_85

def loopBody432_87 : HolLoopProg 64 :=
.mark loopBody432_86

def loopBody432_88 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_87

def loopBody432_89 : HolLoopProg 64 :=
.mark loopBody432_88

def loopBody432_90 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_89

def loopBody432_91 : HolLoopProg 64 :=
.mark loopBody432_90

def loopBody432_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody432_93 : HolLoopProg 64 :=
.mark loopBody432_92

def loopBody432_94 : HolLoopProg 64 :=
.call (some ([13], Flapjack.Spt.ln)) (some 486) ([14]) (some (14, loopBody432_75, loopBody432_1, (Flapjack.Spt.ln)))

def loopBody432_95 : HolLoopProg 64 :=
.mark loopBody432_94

def loopBody432_96 : HolLoopProg 64 :=
.seq loopBody432_95 loopBody432_1

def loopBody432_97 : HolLoopProg 64 :=
.mark loopBody432_96

def loopBody432_98 : HolLoopProg 64 :=
.seq loopBody432_93 loopBody432_97

def loopBody432_99 : HolLoopProg 64 :=
.mark loopBody432_98

def loopBody432_100 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_99

def loopBody432_101 : HolLoopProg 64 :=
.mark loopBody432_100

def loopBody432_102 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_101

def loopBody432_103 : HolLoopProg 64 :=
.mark loopBody432_102

def loopBody432_104 : HolLoopProg 64 :=
.seq loopBody432_91 loopBody432_103

def loopBody432_105 : HolLoopProg 64 :=
.mark loopBody432_104

def loopBody432_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody432_107 : HolLoopProg 64 :=
.mark loopBody432_106

def loopBody432_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [13]

def loopBody432_109 : HolLoopProg 64 :=
.mark loopBody432_108

def loopBody432_110 : HolLoopProg 64 :=
.seq loopBody432_109 loopBody432_1

def loopBody432_111 : HolLoopProg 64 :=
.mark loopBody432_110

def loopBody432_112 : HolLoopProg 64 :=
.seq loopBody432_107 loopBody432_111

def loopBody432_113 : HolLoopProg 64 :=
.mark loopBody432_112

def loopBody432_114 : HolLoopProg 64 :=
.seq loopBody432_105 loopBody432_113

def loopBody432_115 : HolLoopProg 64 :=
.mark loopBody432_114

def loopBody432_116 : HolLoopProg 64 :=
.seq loopBody432_65 loopBody432_115

def loopBody432_117 : HolLoopProg 64 :=
.mark loopBody432_116

def loopBody432_118 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_117

def loopBody432_119 : HolLoopProg 64 :=
.mark loopBody432_118

def loopBody432_120 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_119

def loopBody432_121 : HolLoopProg 64 :=
.mark loopBody432_120

def loopBody432_122 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_121

def loopBody432_123 : HolLoopProg 64 :=
.mark loopBody432_122

def loopBody432_124 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_123

def loopBody432_125 : HolLoopProg 64 :=
.mark loopBody432_124

def loopBody432_126 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_125

def loopBody432_127 : HolLoopProg 64 :=
.mark loopBody432_126

def loopBody432_128 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_127

def loopBody432_129 : HolLoopProg 64 :=
.mark loopBody432_128

def loopBody432_130 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_129

def loopBody432_131 : HolLoopProg 64 :=
.mark loopBody432_130

def loopBody432_132 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_131

def loopBody432_133 : HolLoopProg 64 :=
.mark loopBody432_132

def loopBody432_134 : HolLoopProg 64 :=
.seq loopBody432_27 loopBody432_133

def loopBody432_135 : HolLoopProg 64 :=
.mark loopBody432_134

def loopBody432_136 : HolLoopProg 64 :=
.seq loopBody432_13 loopBody432_135

def loopBody432_137 : HolLoopProg 64 :=
.mark loopBody432_136

def loopBody432_138 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_137

def loopBody432_139 : HolLoopProg 64 :=
.mark loopBody432_138

def loopBody432_140 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_139

def loopBody432_141 : HolLoopProg 64 :=
.mark loopBody432_140

def loopBody432_142 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_141

def loopBody432_143 : HolLoopProg 64 :=
.mark loopBody432_142

def loopBody432_144 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_143

def loopBody432_145 : HolLoopProg 64 :=
.mark loopBody432_144

def loopBody432_146 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_145

def loopBody432_147 : HolLoopProg 64 :=
.mark loopBody432_146

def loopBody432_148 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_147

def loopBody432_149 : HolLoopProg 64 :=
.mark loopBody432_148

def loopBody432_150 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_149

def loopBody432_151 : HolLoopProg 64 :=
.mark loopBody432_150

def loopBody432_152 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_151

def loopBody432_153 : HolLoopProg 64 :=
.mark loopBody432_152

def loopBody432_154 : HolLoopProg 64 :=
.seq loopBody432_7 loopBody432_153

def loopBody432_155 : HolLoopProg 64 :=
.mark loopBody432_154

def loopBody432_156 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_155

def loopBody432_157 : HolLoopProg 64 :=
.mark loopBody432_156

def loopBody432_158 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_157

def loopBody432_159 : HolLoopProg 64 :=
.mark loopBody432_158

def loopBody432_160 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_159

def loopBody432_161 : HolLoopProg 64 :=
.mark loopBody432_160

def loopBody432_162 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_161

def loopBody432_163 : HolLoopProg 64 :=
.mark loopBody432_162

def loopBody432_164 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_163

def loopBody432_165 : HolLoopProg 64 :=
.mark loopBody432_164

def loopBody432_166 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_165

def loopBody432_167 : HolLoopProg 64 :=
.mark loopBody432_166

def loopBody432_168 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_167

def loopBody432_169 : HolLoopProg 64 :=
.mark loopBody432_168

def loopBody432_170 : HolLoopProg 64 :=
.seq loopBody432_1 loopBody432_169

def loopBody432_171 : HolLoopProg 64 :=
.mark loopBody432_170

def output432 : Nat × List Nat × HolLoopProg 64 :=
  (496, [], loopBody432_171)
end InitECandidate.Proofs.FrontendStages.Loop
