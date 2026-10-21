import InitECandidate.Proofs.FrontendStages.Loop.Translate482
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody498_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody498_1 : HolLoopProg 64 :=
.mark loopBody498_0

def loopBody498_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody498_3 : HolLoopProg 64 :=
.mark loopBody498_2

def loopBody498_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody498_3, loopBody498_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody498_5 : HolLoopProg 64 :=
.mark loopBody498_4

def loopBody498_6 : HolLoopProg 64 :=
.seq loopBody498_5 loopBody498_1

def loopBody498_7 : HolLoopProg 64 :=
.mark loopBody498_6

def loopBody498_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody498_9 : HolLoopProg 64 :=
.mark loopBody498_8

def loopBody498_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody498_11 : HolLoopProg 64 :=
.mark loopBody498_10

def loopBody498_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody498_13 : HolLoopProg 64 :=
.mark loopBody498_12

def loopBody498_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody498_15 : HolLoopProg 64 :=
.mark loopBody498_14

def loopBody498_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody498_17 : HolLoopProg 64 :=
.mark loopBody498_16

def loopBody498_18 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 462) ([6, 7, 8, 9]) (some (6, loopBody498_17, loopBody498_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody498_19 : HolLoopProg 64 :=
.mark loopBody498_18

def loopBody498_20 : HolLoopProg 64 :=
.seq loopBody498_19 loopBody498_1

def loopBody498_21 : HolLoopProg 64 :=
.mark loopBody498_20

def loopBody498_22 : HolLoopProg 64 :=
.seq loopBody498_15 loopBody498_21

def loopBody498_23 : HolLoopProg 64 :=
.mark loopBody498_22

def loopBody498_24 : HolLoopProg 64 :=
.seq loopBody498_13 loopBody498_23

def loopBody498_25 : HolLoopProg 64 :=
.mark loopBody498_24

def loopBody498_26 : HolLoopProg 64 :=
.seq loopBody498_11 loopBody498_25

def loopBody498_27 : HolLoopProg 64 :=
.mark loopBody498_26

def loopBody498_28 : HolLoopProg 64 :=
.seq loopBody498_9 loopBody498_27

def loopBody498_29 : HolLoopProg 64 :=
.mark loopBody498_28

def loopBody498_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody498_31 : HolLoopProg 64 :=
.mark loopBody498_30

def loopBody498_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody498_33 : HolLoopProg 64 :=
.mark loopBody498_32

def loopBody498_34 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 491) ([7]) (some (7, loopBody498_33, loopBody498_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody498_35 : HolLoopProg 64 :=
.mark loopBody498_34

def loopBody498_36 : HolLoopProg 64 :=
.seq loopBody498_35 loopBody498_1

def loopBody498_37 : HolLoopProg 64 :=
.mark loopBody498_36

def loopBody498_38 : HolLoopProg 64 :=
.seq loopBody498_31 loopBody498_37

def loopBody498_39 : HolLoopProg 64 :=
.mark loopBody498_38

def loopBody498_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 100#64])

def loopBody498_41 : HolLoopProg 64 :=
.mark loopBody498_40

def loopBody498_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody498_43 : HolLoopProg 64 :=
.mark loopBody498_42

def loopBody498_44 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 466) ([8]) (some (8, loopBody498_43, loopBody498_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody498_45 : HolLoopProg 64 :=
.mark loopBody498_44

def loopBody498_46 : HolLoopProg 64 :=
.seq loopBody498_45 loopBody498_1

def loopBody498_47 : HolLoopProg 64 :=
.mark loopBody498_46

def loopBody498_48 : HolLoopProg 64 :=
.seq loopBody498_41 loopBody498_47

def loopBody498_49 : HolLoopProg 64 :=
.mark loopBody498_48

def loopBody498_50 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_49

def loopBody498_51 : HolLoopProg 64 :=
.mark loopBody498_50

def loopBody498_52 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_51

def loopBody498_53 : HolLoopProg 64 :=
.mark loopBody498_52

def loopBody498_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody498_55 : HolLoopProg 64 :=
.mark loopBody498_54

def loopBody498_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody498_57 : HolLoopProg 64 :=
.mark loopBody498_56

def loopBody498_58 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 492) ([8, 9]) (some (8, loopBody498_43, loopBody498_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody498_59 : HolLoopProg 64 :=
.mark loopBody498_58

def loopBody498_60 : HolLoopProg 64 :=
.seq loopBody498_59 loopBody498_1

def loopBody498_61 : HolLoopProg 64 :=
.mark loopBody498_60

def loopBody498_62 : HolLoopProg 64 :=
.seq loopBody498_57 loopBody498_61

def loopBody498_63 : HolLoopProg 64 :=
.mark loopBody498_62

def loopBody498_64 : HolLoopProg 64 :=
.seq loopBody498_55 loopBody498_63

def loopBody498_65 : HolLoopProg 64 :=
.mark loopBody498_64

def loopBody498_66 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_65

def loopBody498_67 : HolLoopProg 64 :=
.mark loopBody498_66

def loopBody498_68 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_67

def loopBody498_69 : HolLoopProg 64 :=
.mark loopBody498_68

def loopBody498_70 : HolLoopProg 64 :=
.seq loopBody498_53 loopBody498_69

def loopBody498_71 : HolLoopProg 64 :=
.mark loopBody498_70

def loopBody498_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody498_73 : HolLoopProg 64 :=
.mark loopBody498_72

def loopBody498_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody498_75 : HolLoopProg 64 :=
.mark loopBody498_74

def loopBody498_76 : HolLoopProg 64 :=
.call (some ([7, 8], Flapjack.Spt.ln)) (some 561) ([9]) (some (9, loopBody498_75, loopBody498_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  Flapjack.Spt.ln)))

def loopBody498_77 : HolLoopProg 64 :=
.mark loopBody498_76

def loopBody498_78 : HolLoopProg 64 :=
.seq loopBody498_77 loopBody498_1

def loopBody498_79 : HolLoopProg 64 :=
.mark loopBody498_78

def loopBody498_80 : HolLoopProg 64 :=
.seq loopBody498_73 loopBody498_79

def loopBody498_81 : HolLoopProg 64 :=
.mark loopBody498_80

def loopBody498_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody498_83 : HolLoopProg 64 :=
.mark loopBody498_82

def loopBody498_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody498_85 : HolLoopProg 64 :=
.mark loopBody498_84

def loopBody498_86 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 473) ([10]) (some (10, loopBody498_85, loopBody498_1, (Flapjack.Spt.ln)))

def loopBody498_87 : HolLoopProg 64 :=
.mark loopBody498_86

def loopBody498_88 : HolLoopProg 64 :=
.seq loopBody498_87 loopBody498_1

def loopBody498_89 : HolLoopProg 64 :=
.mark loopBody498_88

def loopBody498_90 : HolLoopProg 64 :=
.seq loopBody498_83 loopBody498_89

def loopBody498_91 : HolLoopProg 64 :=
.mark loopBody498_90

def loopBody498_92 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_91

def loopBody498_93 : HolLoopProg 64 :=
.mark loopBody498_92

def loopBody498_94 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_93

def loopBody498_95 : HolLoopProg 64 :=
.mark loopBody498_94

def loopBody498_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody498_97 : HolLoopProg 64 :=
.mark loopBody498_96

def loopBody498_98 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 486) ([10]) (some (10, loopBody498_85, loopBody498_1, (Flapjack.Spt.ln)))

def loopBody498_99 : HolLoopProg 64 :=
.mark loopBody498_98

def loopBody498_100 : HolLoopProg 64 :=
.seq loopBody498_99 loopBody498_1

def loopBody498_101 : HolLoopProg 64 :=
.mark loopBody498_100

def loopBody498_102 : HolLoopProg 64 :=
.seq loopBody498_97 loopBody498_101

def loopBody498_103 : HolLoopProg 64 :=
.mark loopBody498_102

def loopBody498_104 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_103

def loopBody498_105 : HolLoopProg 64 :=
.mark loopBody498_104

def loopBody498_106 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_105

def loopBody498_107 : HolLoopProg 64 :=
.mark loopBody498_106

def loopBody498_108 : HolLoopProg 64 :=
.seq loopBody498_95 loopBody498_107

def loopBody498_109 : HolLoopProg 64 :=
.mark loopBody498_108

def loopBody498_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody498_111 : HolLoopProg 64 :=
.mark loopBody498_110

def loopBody498_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9]

def loopBody498_113 : HolLoopProg 64 :=
.mark loopBody498_112

def loopBody498_114 : HolLoopProg 64 :=
.seq loopBody498_113 loopBody498_1

def loopBody498_115 : HolLoopProg 64 :=
.mark loopBody498_114

def loopBody498_116 : HolLoopProg 64 :=
.seq loopBody498_111 loopBody498_115

def loopBody498_117 : HolLoopProg 64 :=
.mark loopBody498_116

def loopBody498_118 : HolLoopProg 64 :=
.seq loopBody498_109 loopBody498_117

def loopBody498_119 : HolLoopProg 64 :=
.mark loopBody498_118

def loopBody498_120 : HolLoopProg 64 :=
.seq loopBody498_81 loopBody498_119

def loopBody498_121 : HolLoopProg 64 :=
.mark loopBody498_120

def loopBody498_122 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_121

def loopBody498_123 : HolLoopProg 64 :=
.mark loopBody498_122

def loopBody498_124 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_123

def loopBody498_125 : HolLoopProg 64 :=
.mark loopBody498_124

def loopBody498_126 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_125

def loopBody498_127 : HolLoopProg 64 :=
.mark loopBody498_126

def loopBody498_128 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_127

def loopBody498_129 : HolLoopProg 64 :=
.mark loopBody498_128

def loopBody498_130 : HolLoopProg 64 :=
.seq loopBody498_71 loopBody498_129

def loopBody498_131 : HolLoopProg 64 :=
.mark loopBody498_130

def loopBody498_132 : HolLoopProg 64 :=
.seq loopBody498_39 loopBody498_131

def loopBody498_133 : HolLoopProg 64 :=
.mark loopBody498_132

def loopBody498_134 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_133

def loopBody498_135 : HolLoopProg 64 :=
.mark loopBody498_134

def loopBody498_136 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_135

def loopBody498_137 : HolLoopProg 64 :=
.mark loopBody498_136

def loopBody498_138 : HolLoopProg 64 :=
.seq loopBody498_29 loopBody498_137

def loopBody498_139 : HolLoopProg 64 :=
.mark loopBody498_138

def loopBody498_140 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_139

def loopBody498_141 : HolLoopProg 64 :=
.mark loopBody498_140

def loopBody498_142 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_141

def loopBody498_143 : HolLoopProg 64 :=
.mark loopBody498_142

def loopBody498_144 : HolLoopProg 64 :=
.seq loopBody498_7 loopBody498_143

def loopBody498_145 : HolLoopProg 64 :=
.mark loopBody498_144

def loopBody498_146 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_145

def loopBody498_147 : HolLoopProg 64 :=
.mark loopBody498_146

def loopBody498_148 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_147

def loopBody498_149 : HolLoopProg 64 :=
.mark loopBody498_148

def loopBody498_150 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_149

def loopBody498_151 : HolLoopProg 64 :=
.mark loopBody498_150

def loopBody498_152 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_151

def loopBody498_153 : HolLoopProg 64 :=
.mark loopBody498_152

def loopBody498_154 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_153

def loopBody498_155 : HolLoopProg 64 :=
.mark loopBody498_154

def loopBody498_156 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_155

def loopBody498_157 : HolLoopProg 64 :=
.mark loopBody498_156

def loopBody498_158 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_157

def loopBody498_159 : HolLoopProg 64 :=
.mark loopBody498_158

def loopBody498_160 : HolLoopProg 64 :=
.seq loopBody498_1 loopBody498_159

def loopBody498_161 : HolLoopProg 64 :=
.mark loopBody498_160

def output498 : Nat × List Nat × HolLoopProg 64 :=
  (562, [], loopBody498_161)
end InitECandidate.Proofs.FrontendStages.Loop
