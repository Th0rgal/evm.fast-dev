import InitECandidate.Proofs.FrontendStages.Loop.Translate434
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody450_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody450_1 : HolLoopProg 64 :=
.mark loopBody450_0

def loopBody450_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody450_3 : HolLoopProg 64 :=
.mark loopBody450_2

def loopBody450_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody450_3, loopBody450_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody450_5 : HolLoopProg 64 :=
.mark loopBody450_4

def loopBody450_6 : HolLoopProg 64 :=
.seq loopBody450_5 loopBody450_1

def loopBody450_7 : HolLoopProg 64 :=
.mark loopBody450_6

def loopBody450_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody450_9 : HolLoopProg 64 :=
.mark loopBody450_8

def loopBody450_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody450_9, loopBody450_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody450_11 : HolLoopProg 64 :=
.mark loopBody450_10

def loopBody450_12 : HolLoopProg 64 :=
.seq loopBody450_11 loopBody450_1

def loopBody450_13 : HolLoopProg 64 :=
.mark loopBody450_12

def loopBody450_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody450_15 : HolLoopProg 64 :=
.mark loopBody450_14

def loopBody450_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody450_17 : HolLoopProg 64 :=
.mark loopBody450_16

def loopBody450_18 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 466) ([10]) (some (10, loopBody450_17, loopBody450_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody450_19 : HolLoopProg 64 :=
.mark loopBody450_18

def loopBody450_20 : HolLoopProg 64 :=
.seq loopBody450_19 loopBody450_1

def loopBody450_21 : HolLoopProg 64 :=
.mark loopBody450_20

def loopBody450_22 : HolLoopProg 64 :=
.seq loopBody450_15 loopBody450_21

def loopBody450_23 : HolLoopProg 64 :=
.mark loopBody450_22

def loopBody450_24 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_23

def loopBody450_25 : HolLoopProg 64 :=
.mark loopBody450_24

def loopBody450_26 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_25

def loopBody450_27 : HolLoopProg 64 :=
.mark loopBody450_26

def loopBody450_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody450_29 : HolLoopProg 64 :=
.mark loopBody450_28

def loopBody450_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody450_31 : HolLoopProg 64 :=
.mark loopBody450_30

def loopBody450_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody450_33 : HolLoopProg 64 :=
.mark loopBody450_32

def loopBody450_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody450_35 : HolLoopProg 64 :=
.mark loopBody450_34

def loopBody450_36 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 458) ([10, 11, 12, 13]) (some (10, loopBody450_17, loopBody450_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody450_37 : HolLoopProg 64 :=
.mark loopBody450_36

def loopBody450_38 : HolLoopProg 64 :=
.seq loopBody450_37 loopBody450_1

def loopBody450_39 : HolLoopProg 64 :=
.mark loopBody450_38

def loopBody450_40 : HolLoopProg 64 :=
.seq loopBody450_35 loopBody450_39

def loopBody450_41 : HolLoopProg 64 :=
.mark loopBody450_40

def loopBody450_42 : HolLoopProg 64 :=
.seq loopBody450_33 loopBody450_41

def loopBody450_43 : HolLoopProg 64 :=
.mark loopBody450_42

def loopBody450_44 : HolLoopProg 64 :=
.seq loopBody450_31 loopBody450_43

def loopBody450_45 : HolLoopProg 64 :=
.mark loopBody450_44

def loopBody450_46 : HolLoopProg 64 :=
.seq loopBody450_29 loopBody450_45

def loopBody450_47 : HolLoopProg 64 :=
.mark loopBody450_46

def loopBody450_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody450_49 : HolLoopProg 64 :=
.mark loopBody450_48

def loopBody450_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 5)

def loopBody450_51 : HolLoopProg 64 :=
.mark loopBody450_50

def loopBody450_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 6)

def loopBody450_53 : HolLoopProg 64 :=
.mark loopBody450_52

def loopBody450_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 7)

def loopBody450_55 : HolLoopProg 64 :=
.mark loopBody450_54

def loopBody450_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 8)

def loopBody450_57 : HolLoopProg 64 :=
.mark loopBody450_56

def loopBody450_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody450_59 : HolLoopProg 64 :=
.mark loopBody450_58

def loopBody450_60 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 145) ([11, 12, 13, 14, 15]) (some (11, loopBody450_59, loopBody450_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
  Flapjack.Spt.ln)))

def loopBody450_61 : HolLoopProg 64 :=
.mark loopBody450_60

def loopBody450_62 : HolLoopProg 64 :=
.seq loopBody450_61 loopBody450_1

def loopBody450_63 : HolLoopProg 64 :=
.mark loopBody450_62

def loopBody450_64 : HolLoopProg 64 :=
.seq loopBody450_57 loopBody450_63

def loopBody450_65 : HolLoopProg 64 :=
.mark loopBody450_64

def loopBody450_66 : HolLoopProg 64 :=
.seq loopBody450_55 loopBody450_65

def loopBody450_67 : HolLoopProg 64 :=
.mark loopBody450_66

def loopBody450_68 : HolLoopProg 64 :=
.seq loopBody450_53 loopBody450_67

def loopBody450_69 : HolLoopProg 64 :=
.mark loopBody450_68

def loopBody450_70 : HolLoopProg 64 :=
.seq loopBody450_51 loopBody450_69

def loopBody450_71 : HolLoopProg 64 :=
.mark loopBody450_70

def loopBody450_72 : HolLoopProg 64 :=
.seq loopBody450_49 loopBody450_71

def loopBody450_73 : HolLoopProg 64 :=
.mark loopBody450_72

def loopBody450_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody450_75 : HolLoopProg 64 :=
.mark loopBody450_74

def loopBody450_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 12

def loopBody450_77 : HolLoopProg 64 :=
.mark loopBody450_76

def loopBody450_78 : HolLoopProg 64 :=
.call (some ([11], Flapjack.Spt.ln)) (some 473) ([12]) (some (12, loopBody450_77, loopBody450_1, (Flapjack.Spt.ln)))

def loopBody450_79 : HolLoopProg 64 :=
.mark loopBody450_78

def loopBody450_80 : HolLoopProg 64 :=
.seq loopBody450_79 loopBody450_1

def loopBody450_81 : HolLoopProg 64 :=
.mark loopBody450_80

def loopBody450_82 : HolLoopProg 64 :=
.seq loopBody450_75 loopBody450_81

def loopBody450_83 : HolLoopProg 64 :=
.mark loopBody450_82

def loopBody450_84 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_83

def loopBody450_85 : HolLoopProg 64 :=
.mark loopBody450_84

def loopBody450_86 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_85

def loopBody450_87 : HolLoopProg 64 :=
.mark loopBody450_86

def loopBody450_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody450_89 : HolLoopProg 64 :=
.mark loopBody450_88

def loopBody450_90 : HolLoopProg 64 :=
.call (some ([11], Flapjack.Spt.ln)) (some 486) ([12]) (some (12, loopBody450_77, loopBody450_1, (Flapjack.Spt.ln)))

def loopBody450_91 : HolLoopProg 64 :=
.mark loopBody450_90

def loopBody450_92 : HolLoopProg 64 :=
.seq loopBody450_91 loopBody450_1

def loopBody450_93 : HolLoopProg 64 :=
.mark loopBody450_92

def loopBody450_94 : HolLoopProg 64 :=
.seq loopBody450_89 loopBody450_93

def loopBody450_95 : HolLoopProg 64 :=
.mark loopBody450_94

def loopBody450_96 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_95

def loopBody450_97 : HolLoopProg 64 :=
.mark loopBody450_96

def loopBody450_98 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_97

def loopBody450_99 : HolLoopProg 64 :=
.mark loopBody450_98

def loopBody450_100 : HolLoopProg 64 :=
.seq loopBody450_87 loopBody450_99

def loopBody450_101 : HolLoopProg 64 :=
.mark loopBody450_100

def loopBody450_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody450_103 : HolLoopProg 64 :=
.mark loopBody450_102

def loopBody450_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [11]

def loopBody450_105 : HolLoopProg 64 :=
.mark loopBody450_104

def loopBody450_106 : HolLoopProg 64 :=
.seq loopBody450_105 loopBody450_1

def loopBody450_107 : HolLoopProg 64 :=
.mark loopBody450_106

def loopBody450_108 : HolLoopProg 64 :=
.seq loopBody450_103 loopBody450_107

def loopBody450_109 : HolLoopProg 64 :=
.mark loopBody450_108

def loopBody450_110 : HolLoopProg 64 :=
.seq loopBody450_101 loopBody450_109

def loopBody450_111 : HolLoopProg 64 :=
.mark loopBody450_110

def loopBody450_112 : HolLoopProg 64 :=
.seq loopBody450_73 loopBody450_111

def loopBody450_113 : HolLoopProg 64 :=
.mark loopBody450_112

def loopBody450_114 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_113

def loopBody450_115 : HolLoopProg 64 :=
.mark loopBody450_114

def loopBody450_116 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_115

def loopBody450_117 : HolLoopProg 64 :=
.mark loopBody450_116

def loopBody450_118 : HolLoopProg 64 :=
.seq loopBody450_47 loopBody450_117

def loopBody450_119 : HolLoopProg 64 :=
.mark loopBody450_118

def loopBody450_120 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_119

def loopBody450_121 : HolLoopProg 64 :=
.mark loopBody450_120

def loopBody450_122 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_121

def loopBody450_123 : HolLoopProg 64 :=
.mark loopBody450_122

def loopBody450_124 : HolLoopProg 64 :=
.seq loopBody450_27 loopBody450_123

def loopBody450_125 : HolLoopProg 64 :=
.mark loopBody450_124

def loopBody450_126 : HolLoopProg 64 :=
.seq loopBody450_13 loopBody450_125

def loopBody450_127 : HolLoopProg 64 :=
.mark loopBody450_126

def loopBody450_128 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_127

def loopBody450_129 : HolLoopProg 64 :=
.mark loopBody450_128

def loopBody450_130 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_129

def loopBody450_131 : HolLoopProg 64 :=
.mark loopBody450_130

def loopBody450_132 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_131

def loopBody450_133 : HolLoopProg 64 :=
.mark loopBody450_132

def loopBody450_134 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_133

def loopBody450_135 : HolLoopProg 64 :=
.mark loopBody450_134

def loopBody450_136 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_135

def loopBody450_137 : HolLoopProg 64 :=
.mark loopBody450_136

def loopBody450_138 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_137

def loopBody450_139 : HolLoopProg 64 :=
.mark loopBody450_138

def loopBody450_140 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_139

def loopBody450_141 : HolLoopProg 64 :=
.mark loopBody450_140

def loopBody450_142 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_141

def loopBody450_143 : HolLoopProg 64 :=
.mark loopBody450_142

def loopBody450_144 : HolLoopProg 64 :=
.seq loopBody450_7 loopBody450_143

def loopBody450_145 : HolLoopProg 64 :=
.mark loopBody450_144

def loopBody450_146 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_145

def loopBody450_147 : HolLoopProg 64 :=
.mark loopBody450_146

def loopBody450_148 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_147

def loopBody450_149 : HolLoopProg 64 :=
.mark loopBody450_148

def loopBody450_150 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_149

def loopBody450_151 : HolLoopProg 64 :=
.mark loopBody450_150

def loopBody450_152 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_151

def loopBody450_153 : HolLoopProg 64 :=
.mark loopBody450_152

def loopBody450_154 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_153

def loopBody450_155 : HolLoopProg 64 :=
.mark loopBody450_154

def loopBody450_156 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_155

def loopBody450_157 : HolLoopProg 64 :=
.mark loopBody450_156

def loopBody450_158 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_157

def loopBody450_159 : HolLoopProg 64 :=
.mark loopBody450_158

def loopBody450_160 : HolLoopProg 64 :=
.seq loopBody450_1 loopBody450_159

def loopBody450_161 : HolLoopProg 64 :=
.mark loopBody450_160

def output450 : Nat × List Nat × HolLoopProg 64 :=
  (514, [], loopBody450_161)
end InitECandidate.Proofs.FrontendStages.Loop
