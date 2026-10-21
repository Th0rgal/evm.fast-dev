import InitECandidate.Proofs.FrontendStages.Loop.Translate424
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody440_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody440_1 : HolLoopProg 64 :=
.mark loopBody440_0

def loopBody440_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody440_3 : HolLoopProg 64 :=
.mark loopBody440_2

def loopBody440_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody440_3, loopBody440_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody440_5 : HolLoopProg 64 :=
.mark loopBody440_4

def loopBody440_6 : HolLoopProg 64 :=
.seq loopBody440_5 loopBody440_1

def loopBody440_7 : HolLoopProg 64 :=
.mark loopBody440_6

def loopBody440_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody440_9 : HolLoopProg 64 :=
.mark loopBody440_8

def loopBody440_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody440_9, loopBody440_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody440_11 : HolLoopProg 64 :=
.mark loopBody440_10

def loopBody440_12 : HolLoopProg 64 :=
.seq loopBody440_11 loopBody440_1

def loopBody440_13 : HolLoopProg 64 :=
.mark loopBody440_12

def loopBody440_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody440_15 : HolLoopProg 64 :=
.mark loopBody440_14

def loopBody440_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody440_17 : HolLoopProg 64 :=
.mark loopBody440_16

def loopBody440_18 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 466) ([10]) (some (10, loopBody440_17, loopBody440_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody440_19 : HolLoopProg 64 :=
.mark loopBody440_18

def loopBody440_20 : HolLoopProg 64 :=
.seq loopBody440_19 loopBody440_1

def loopBody440_21 : HolLoopProg 64 :=
.mark loopBody440_20

def loopBody440_22 : HolLoopProg 64 :=
.seq loopBody440_15 loopBody440_21

def loopBody440_23 : HolLoopProg 64 :=
.mark loopBody440_22

def loopBody440_24 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_23

def loopBody440_25 : HolLoopProg 64 :=
.mark loopBody440_24

def loopBody440_26 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_25

def loopBody440_27 : HolLoopProg 64 :=
.mark loopBody440_26

def loopBody440_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody440_29 : HolLoopProg 64 :=
.mark loopBody440_28

def loopBody440_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody440_31 : HolLoopProg 64 :=
.mark loopBody440_30

def loopBody440_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody440_33 : HolLoopProg 64 :=
.mark loopBody440_32

def loopBody440_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody440_35 : HolLoopProg 64 :=
.mark loopBody440_34

def loopBody440_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 5)

def loopBody440_37 : HolLoopProg 64 :=
.mark loopBody440_36

def loopBody440_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 6)

def loopBody440_39 : HolLoopProg 64 :=
.mark loopBody440_38

def loopBody440_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 7)

def loopBody440_41 : HolLoopProg 64 :=
.mark loopBody440_40

def loopBody440_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 8)

def loopBody440_43 : HolLoopProg 64 :=
.mark loopBody440_42

def loopBody440_44 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 106) ([10, 11, 12, 13, 14, 15, 16, 17]) (some (10, loopBody440_17, loopBody440_1, (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))

def loopBody440_45 : HolLoopProg 64 :=
.mark loopBody440_44

def loopBody440_46 : HolLoopProg 64 :=
.seq loopBody440_45 loopBody440_1

def loopBody440_47 : HolLoopProg 64 :=
.mark loopBody440_46

def loopBody440_48 : HolLoopProg 64 :=
.seq loopBody440_43 loopBody440_47

def loopBody440_49 : HolLoopProg 64 :=
.mark loopBody440_48

def loopBody440_50 : HolLoopProg 64 :=
.seq loopBody440_41 loopBody440_49

def loopBody440_51 : HolLoopProg 64 :=
.mark loopBody440_50

def loopBody440_52 : HolLoopProg 64 :=
.seq loopBody440_39 loopBody440_51

def loopBody440_53 : HolLoopProg 64 :=
.mark loopBody440_52

def loopBody440_54 : HolLoopProg 64 :=
.seq loopBody440_37 loopBody440_53

def loopBody440_55 : HolLoopProg 64 :=
.mark loopBody440_54

def loopBody440_56 : HolLoopProg 64 :=
.seq loopBody440_35 loopBody440_55

def loopBody440_57 : HolLoopProg 64 :=
.mark loopBody440_56

def loopBody440_58 : HolLoopProg 64 :=
.seq loopBody440_33 loopBody440_57

def loopBody440_59 : HolLoopProg 64 :=
.mark loopBody440_58

def loopBody440_60 : HolLoopProg 64 :=
.seq loopBody440_31 loopBody440_59

def loopBody440_61 : HolLoopProg 64 :=
.mark loopBody440_60

def loopBody440_62 : HolLoopProg 64 :=
.seq loopBody440_29 loopBody440_61

def loopBody440_63 : HolLoopProg 64 :=
.mark loopBody440_62

def loopBody440_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody440_65 : HolLoopProg 64 :=
.mark loopBody440_64

def loopBody440_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody440_67 : HolLoopProg 64 :=
.mark loopBody440_66

def loopBody440_68 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 474) ([11]) (some (11, loopBody440_67, loopBody440_1, (Flapjack.Spt.ln)))

def loopBody440_69 : HolLoopProg 64 :=
.mark loopBody440_68

def loopBody440_70 : HolLoopProg 64 :=
.seq loopBody440_69 loopBody440_1

def loopBody440_71 : HolLoopProg 64 :=
.mark loopBody440_70

def loopBody440_72 : HolLoopProg 64 :=
.seq loopBody440_65 loopBody440_71

def loopBody440_73 : HolLoopProg 64 :=
.mark loopBody440_72

def loopBody440_74 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_73

def loopBody440_75 : HolLoopProg 64 :=
.mark loopBody440_74

def loopBody440_76 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_75

def loopBody440_77 : HolLoopProg 64 :=
.mark loopBody440_76

def loopBody440_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody440_79 : HolLoopProg 64 :=
.mark loopBody440_78

def loopBody440_80 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 486) ([11]) (some (11, loopBody440_67, loopBody440_1, (Flapjack.Spt.ln)))

def loopBody440_81 : HolLoopProg 64 :=
.mark loopBody440_80

def loopBody440_82 : HolLoopProg 64 :=
.seq loopBody440_81 loopBody440_1

def loopBody440_83 : HolLoopProg 64 :=
.mark loopBody440_82

def loopBody440_84 : HolLoopProg 64 :=
.seq loopBody440_79 loopBody440_83

def loopBody440_85 : HolLoopProg 64 :=
.mark loopBody440_84

def loopBody440_86 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_85

def loopBody440_87 : HolLoopProg 64 :=
.mark loopBody440_86

def loopBody440_88 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_87

def loopBody440_89 : HolLoopProg 64 :=
.mark loopBody440_88

def loopBody440_90 : HolLoopProg 64 :=
.seq loopBody440_77 loopBody440_89

def loopBody440_91 : HolLoopProg 64 :=
.mark loopBody440_90

def loopBody440_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody440_93 : HolLoopProg 64 :=
.mark loopBody440_92

def loopBody440_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [10]

def loopBody440_95 : HolLoopProg 64 :=
.mark loopBody440_94

def loopBody440_96 : HolLoopProg 64 :=
.seq loopBody440_95 loopBody440_1

def loopBody440_97 : HolLoopProg 64 :=
.mark loopBody440_96

def loopBody440_98 : HolLoopProg 64 :=
.seq loopBody440_93 loopBody440_97

def loopBody440_99 : HolLoopProg 64 :=
.mark loopBody440_98

def loopBody440_100 : HolLoopProg 64 :=
.seq loopBody440_91 loopBody440_99

def loopBody440_101 : HolLoopProg 64 :=
.mark loopBody440_100

def loopBody440_102 : HolLoopProg 64 :=
.seq loopBody440_63 loopBody440_101

def loopBody440_103 : HolLoopProg 64 :=
.mark loopBody440_102

def loopBody440_104 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_103

def loopBody440_105 : HolLoopProg 64 :=
.mark loopBody440_104

def loopBody440_106 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_105

def loopBody440_107 : HolLoopProg 64 :=
.mark loopBody440_106

def loopBody440_108 : HolLoopProg 64 :=
.seq loopBody440_27 loopBody440_107

def loopBody440_109 : HolLoopProg 64 :=
.mark loopBody440_108

def loopBody440_110 : HolLoopProg 64 :=
.seq loopBody440_13 loopBody440_109

def loopBody440_111 : HolLoopProg 64 :=
.mark loopBody440_110

def loopBody440_112 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_111

def loopBody440_113 : HolLoopProg 64 :=
.mark loopBody440_112

def loopBody440_114 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_113

def loopBody440_115 : HolLoopProg 64 :=
.mark loopBody440_114

def loopBody440_116 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_115

def loopBody440_117 : HolLoopProg 64 :=
.mark loopBody440_116

def loopBody440_118 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_117

def loopBody440_119 : HolLoopProg 64 :=
.mark loopBody440_118

def loopBody440_120 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_119

def loopBody440_121 : HolLoopProg 64 :=
.mark loopBody440_120

def loopBody440_122 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_121

def loopBody440_123 : HolLoopProg 64 :=
.mark loopBody440_122

def loopBody440_124 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_123

def loopBody440_125 : HolLoopProg 64 :=
.mark loopBody440_124

def loopBody440_126 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_125

def loopBody440_127 : HolLoopProg 64 :=
.mark loopBody440_126

def loopBody440_128 : HolLoopProg 64 :=
.seq loopBody440_7 loopBody440_127

def loopBody440_129 : HolLoopProg 64 :=
.mark loopBody440_128

def loopBody440_130 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_129

def loopBody440_131 : HolLoopProg 64 :=
.mark loopBody440_130

def loopBody440_132 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_131

def loopBody440_133 : HolLoopProg 64 :=
.mark loopBody440_132

def loopBody440_134 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_133

def loopBody440_135 : HolLoopProg 64 :=
.mark loopBody440_134

def loopBody440_136 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_135

def loopBody440_137 : HolLoopProg 64 :=
.mark loopBody440_136

def loopBody440_138 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_137

def loopBody440_139 : HolLoopProg 64 :=
.mark loopBody440_138

def loopBody440_140 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_139

def loopBody440_141 : HolLoopProg 64 :=
.mark loopBody440_140

def loopBody440_142 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_141

def loopBody440_143 : HolLoopProg 64 :=
.mark loopBody440_142

def loopBody440_144 : HolLoopProg 64 :=
.seq loopBody440_1 loopBody440_143

def loopBody440_145 : HolLoopProg 64 :=
.mark loopBody440_144

def output440 : Nat × List Nat × HolLoopProg 64 :=
  (504, [], loopBody440_145)
end InitECandidate.Proofs.FrontendStages.Loop
