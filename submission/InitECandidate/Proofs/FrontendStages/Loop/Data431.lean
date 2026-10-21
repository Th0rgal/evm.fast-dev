import InitECandidate.Proofs.FrontendStages.Loop.Translate415
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody431_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody431_1 : HolLoopProg 64 :=
.mark loopBody431_0

def loopBody431_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody431_3 : HolLoopProg 64 :=
.mark loopBody431_2

def loopBody431_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody431_3, loopBody431_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody431_5 : HolLoopProg 64 :=
.mark loopBody431_4

def loopBody431_6 : HolLoopProg 64 :=
.seq loopBody431_5 loopBody431_1

def loopBody431_7 : HolLoopProg 64 :=
.mark loopBody431_6

def loopBody431_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody431_9 : HolLoopProg 64 :=
.mark loopBody431_8

def loopBody431_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody431_9, loopBody431_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody431_11 : HolLoopProg 64 :=
.mark loopBody431_10

def loopBody431_12 : HolLoopProg 64 :=
.seq loopBody431_11 loopBody431_1

def loopBody431_13 : HolLoopProg 64 :=
.mark loopBody431_12

def loopBody431_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody431_15 : HolLoopProg 64 :=
.mark loopBody431_14

def loopBody431_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody431_17 : HolLoopProg 64 :=
.mark loopBody431_16

def loopBody431_18 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 466) ([10]) (some (10, loopBody431_17, loopBody431_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody431_19 : HolLoopProg 64 :=
.mark loopBody431_18

def loopBody431_20 : HolLoopProg 64 :=
.seq loopBody431_19 loopBody431_1

def loopBody431_21 : HolLoopProg 64 :=
.mark loopBody431_20

def loopBody431_22 : HolLoopProg 64 :=
.seq loopBody431_15 loopBody431_21

def loopBody431_23 : HolLoopProg 64 :=
.mark loopBody431_22

def loopBody431_24 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_23

def loopBody431_25 : HolLoopProg 64 :=
.mark loopBody431_24

def loopBody431_26 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_25

def loopBody431_27 : HolLoopProg 64 :=
.mark loopBody431_26

def loopBody431_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 1)

def loopBody431_29 : HolLoopProg 64 :=
.mark loopBody431_28

def loopBody431_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 2)

def loopBody431_31 : HolLoopProg 64 :=
.mark loopBody431_30

def loopBody431_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 3)

def loopBody431_33 : HolLoopProg 64 :=
.mark loopBody431_32

def loopBody431_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 4)

def loopBody431_35 : HolLoopProg 64 :=
.mark loopBody431_34

def loopBody431_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 5)

def loopBody431_37 : HolLoopProg 64 :=
.mark loopBody431_36

def loopBody431_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 6)

def loopBody431_39 : HolLoopProg 64 :=
.mark loopBody431_38

def loopBody431_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 7)

def loopBody431_41 : HolLoopProg 64 :=
.mark loopBody431_40

def loopBody431_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 8)

def loopBody431_43 : HolLoopProg 64 :=
.mark loopBody431_42

def loopBody431_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody431_45 : HolLoopProg 64 :=
.mark loopBody431_44

def loopBody431_46 : HolLoopProg 64 :=
.call (some ([9, 10, 11, 12], Flapjack.Spt.ln)) (some 117) ([13, 14, 15, 16, 17, 18, 19, 20]) (some (13, loopBody431_45, loopBody431_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))

def loopBody431_47 : HolLoopProg 64 :=
.mark loopBody431_46

def loopBody431_48 : HolLoopProg 64 :=
.seq loopBody431_47 loopBody431_1

def loopBody431_49 : HolLoopProg 64 :=
.mark loopBody431_48

def loopBody431_50 : HolLoopProg 64 :=
.seq loopBody431_43 loopBody431_49

def loopBody431_51 : HolLoopProg 64 :=
.mark loopBody431_50

def loopBody431_52 : HolLoopProg 64 :=
.seq loopBody431_41 loopBody431_51

def loopBody431_53 : HolLoopProg 64 :=
.mark loopBody431_52

def loopBody431_54 : HolLoopProg 64 :=
.seq loopBody431_39 loopBody431_53

def loopBody431_55 : HolLoopProg 64 :=
.mark loopBody431_54

def loopBody431_56 : HolLoopProg 64 :=
.seq loopBody431_37 loopBody431_55

def loopBody431_57 : HolLoopProg 64 :=
.mark loopBody431_56

def loopBody431_58 : HolLoopProg 64 :=
.seq loopBody431_35 loopBody431_57

def loopBody431_59 : HolLoopProg 64 :=
.mark loopBody431_58

def loopBody431_60 : HolLoopProg 64 :=
.seq loopBody431_33 loopBody431_59

def loopBody431_61 : HolLoopProg 64 :=
.mark loopBody431_60

def loopBody431_62 : HolLoopProg 64 :=
.seq loopBody431_31 loopBody431_61

def loopBody431_63 : HolLoopProg 64 :=
.mark loopBody431_62

def loopBody431_64 : HolLoopProg 64 :=
.seq loopBody431_29 loopBody431_63

def loopBody431_65 : HolLoopProg 64 :=
.mark loopBody431_64

def loopBody431_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 9)

def loopBody431_67 : HolLoopProg 64 :=
.mark loopBody431_66

def loopBody431_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 10)

def loopBody431_69 : HolLoopProg 64 :=
.mark loopBody431_68

def loopBody431_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 11)

def loopBody431_71 : HolLoopProg 64 :=
.mark loopBody431_70

def loopBody431_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 12)

def loopBody431_73 : HolLoopProg 64 :=
.mark loopBody431_72

def loopBody431_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 14

def loopBody431_75 : HolLoopProg 64 :=
.mark loopBody431_74

def loopBody431_76 : HolLoopProg 64 :=
.call (some ([13], Flapjack.Spt.ln)) (some 472) ([14, 15, 16, 17]) (some (14, loopBody431_75, loopBody431_1, (Flapjack.Spt.ln)))

def loopBody431_77 : HolLoopProg 64 :=
.mark loopBody431_76

def loopBody431_78 : HolLoopProg 64 :=
.seq loopBody431_77 loopBody431_1

def loopBody431_79 : HolLoopProg 64 :=
.mark loopBody431_78

def loopBody431_80 : HolLoopProg 64 :=
.seq loopBody431_73 loopBody431_79

def loopBody431_81 : HolLoopProg 64 :=
.mark loopBody431_80

def loopBody431_82 : HolLoopProg 64 :=
.seq loopBody431_71 loopBody431_81

def loopBody431_83 : HolLoopProg 64 :=
.mark loopBody431_82

def loopBody431_84 : HolLoopProg 64 :=
.seq loopBody431_69 loopBody431_83

def loopBody431_85 : HolLoopProg 64 :=
.mark loopBody431_84

def loopBody431_86 : HolLoopProg 64 :=
.seq loopBody431_67 loopBody431_85

def loopBody431_87 : HolLoopProg 64 :=
.mark loopBody431_86

def loopBody431_88 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_87

def loopBody431_89 : HolLoopProg 64 :=
.mark loopBody431_88

def loopBody431_90 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_89

def loopBody431_91 : HolLoopProg 64 :=
.mark loopBody431_90

def loopBody431_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody431_93 : HolLoopProg 64 :=
.mark loopBody431_92

def loopBody431_94 : HolLoopProg 64 :=
.call (some ([13], Flapjack.Spt.ln)) (some 486) ([14]) (some (14, loopBody431_75, loopBody431_1, (Flapjack.Spt.ln)))

def loopBody431_95 : HolLoopProg 64 :=
.mark loopBody431_94

def loopBody431_96 : HolLoopProg 64 :=
.seq loopBody431_95 loopBody431_1

def loopBody431_97 : HolLoopProg 64 :=
.mark loopBody431_96

def loopBody431_98 : HolLoopProg 64 :=
.seq loopBody431_93 loopBody431_97

def loopBody431_99 : HolLoopProg 64 :=
.mark loopBody431_98

def loopBody431_100 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_99

def loopBody431_101 : HolLoopProg 64 :=
.mark loopBody431_100

def loopBody431_102 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_101

def loopBody431_103 : HolLoopProg 64 :=
.mark loopBody431_102

def loopBody431_104 : HolLoopProg 64 :=
.seq loopBody431_91 loopBody431_103

def loopBody431_105 : HolLoopProg 64 :=
.mark loopBody431_104

def loopBody431_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody431_107 : HolLoopProg 64 :=
.mark loopBody431_106

def loopBody431_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [13]

def loopBody431_109 : HolLoopProg 64 :=
.mark loopBody431_108

def loopBody431_110 : HolLoopProg 64 :=
.seq loopBody431_109 loopBody431_1

def loopBody431_111 : HolLoopProg 64 :=
.mark loopBody431_110

def loopBody431_112 : HolLoopProg 64 :=
.seq loopBody431_107 loopBody431_111

def loopBody431_113 : HolLoopProg 64 :=
.mark loopBody431_112

def loopBody431_114 : HolLoopProg 64 :=
.seq loopBody431_105 loopBody431_113

def loopBody431_115 : HolLoopProg 64 :=
.mark loopBody431_114

def loopBody431_116 : HolLoopProg 64 :=
.seq loopBody431_65 loopBody431_115

def loopBody431_117 : HolLoopProg 64 :=
.mark loopBody431_116

def loopBody431_118 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_117

def loopBody431_119 : HolLoopProg 64 :=
.mark loopBody431_118

def loopBody431_120 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_119

def loopBody431_121 : HolLoopProg 64 :=
.mark loopBody431_120

def loopBody431_122 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_121

def loopBody431_123 : HolLoopProg 64 :=
.mark loopBody431_122

def loopBody431_124 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_123

def loopBody431_125 : HolLoopProg 64 :=
.mark loopBody431_124

def loopBody431_126 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_125

def loopBody431_127 : HolLoopProg 64 :=
.mark loopBody431_126

def loopBody431_128 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_127

def loopBody431_129 : HolLoopProg 64 :=
.mark loopBody431_128

def loopBody431_130 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_129

def loopBody431_131 : HolLoopProg 64 :=
.mark loopBody431_130

def loopBody431_132 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_131

def loopBody431_133 : HolLoopProg 64 :=
.mark loopBody431_132

def loopBody431_134 : HolLoopProg 64 :=
.seq loopBody431_27 loopBody431_133

def loopBody431_135 : HolLoopProg 64 :=
.mark loopBody431_134

def loopBody431_136 : HolLoopProg 64 :=
.seq loopBody431_13 loopBody431_135

def loopBody431_137 : HolLoopProg 64 :=
.mark loopBody431_136

def loopBody431_138 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_137

def loopBody431_139 : HolLoopProg 64 :=
.mark loopBody431_138

def loopBody431_140 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_139

def loopBody431_141 : HolLoopProg 64 :=
.mark loopBody431_140

def loopBody431_142 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_141

def loopBody431_143 : HolLoopProg 64 :=
.mark loopBody431_142

def loopBody431_144 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_143

def loopBody431_145 : HolLoopProg 64 :=
.mark loopBody431_144

def loopBody431_146 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_145

def loopBody431_147 : HolLoopProg 64 :=
.mark loopBody431_146

def loopBody431_148 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_147

def loopBody431_149 : HolLoopProg 64 :=
.mark loopBody431_148

def loopBody431_150 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_149

def loopBody431_151 : HolLoopProg 64 :=
.mark loopBody431_150

def loopBody431_152 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_151

def loopBody431_153 : HolLoopProg 64 :=
.mark loopBody431_152

def loopBody431_154 : HolLoopProg 64 :=
.seq loopBody431_7 loopBody431_153

def loopBody431_155 : HolLoopProg 64 :=
.mark loopBody431_154

def loopBody431_156 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_155

def loopBody431_157 : HolLoopProg 64 :=
.mark loopBody431_156

def loopBody431_158 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_157

def loopBody431_159 : HolLoopProg 64 :=
.mark loopBody431_158

def loopBody431_160 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_159

def loopBody431_161 : HolLoopProg 64 :=
.mark loopBody431_160

def loopBody431_162 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_161

def loopBody431_163 : HolLoopProg 64 :=
.mark loopBody431_162

def loopBody431_164 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_163

def loopBody431_165 : HolLoopProg 64 :=
.mark loopBody431_164

def loopBody431_166 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_165

def loopBody431_167 : HolLoopProg 64 :=
.mark loopBody431_166

def loopBody431_168 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_167

def loopBody431_169 : HolLoopProg 64 :=
.mark loopBody431_168

def loopBody431_170 : HolLoopProg 64 :=
.seq loopBody431_1 loopBody431_169

def loopBody431_171 : HolLoopProg 64 :=
.mark loopBody431_170

def output431 : Nat × List Nat × HolLoopProg 64 :=
  (495, [], loopBody431_171)
end InitECandidate.Proofs.FrontendStages.Loop
