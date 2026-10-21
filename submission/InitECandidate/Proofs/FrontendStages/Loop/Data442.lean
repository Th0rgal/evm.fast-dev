import InitECandidate.Proofs.FrontendStages.Loop.Translate426
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody442_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody442_1 : HolLoopProg 64 :=
.mark loopBody442_0

def loopBody442_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody442_3 : HolLoopProg 64 :=
.mark loopBody442_2

def loopBody442_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody442_3, loopBody442_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody442_5 : HolLoopProg 64 :=
.mark loopBody442_4

def loopBody442_6 : HolLoopProg 64 :=
.seq loopBody442_5 loopBody442_1

def loopBody442_7 : HolLoopProg 64 :=
.mark loopBody442_6

def loopBody442_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody442_9 : HolLoopProg 64 :=
.mark loopBody442_8

def loopBody442_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody442_9, loopBody442_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody442_11 : HolLoopProg 64 :=
.mark loopBody442_10

def loopBody442_12 : HolLoopProg 64 :=
.seq loopBody442_11 loopBody442_1

def loopBody442_13 : HolLoopProg 64 :=
.mark loopBody442_12

def loopBody442_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody442_15 : HolLoopProg 64 :=
.mark loopBody442_14

def loopBody442_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody442_17 : HolLoopProg 64 :=
.mark loopBody442_16

def loopBody442_18 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 466) ([10]) (some (10, loopBody442_17, loopBody442_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody442_19 : HolLoopProg 64 :=
.mark loopBody442_18

def loopBody442_20 : HolLoopProg 64 :=
.seq loopBody442_19 loopBody442_1

def loopBody442_21 : HolLoopProg 64 :=
.mark loopBody442_20

def loopBody442_22 : HolLoopProg 64 :=
.seq loopBody442_15 loopBody442_21

def loopBody442_23 : HolLoopProg 64 :=
.mark loopBody442_22

def loopBody442_24 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_23

def loopBody442_25 : HolLoopProg 64 :=
.mark loopBody442_24

def loopBody442_26 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_25

def loopBody442_27 : HolLoopProg 64 :=
.mark loopBody442_26

def loopBody442_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 1)

def loopBody442_29 : HolLoopProg 64 :=
.mark loopBody442_28

def loopBody442_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 2)

def loopBody442_31 : HolLoopProg 64 :=
.mark loopBody442_30

def loopBody442_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 3)

def loopBody442_33 : HolLoopProg 64 :=
.mark loopBody442_32

def loopBody442_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody442_35 : HolLoopProg 64 :=
.mark loopBody442_34

def loopBody442_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 5)

def loopBody442_37 : HolLoopProg 64 :=
.mark loopBody442_36

def loopBody442_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 6)

def loopBody442_39 : HolLoopProg 64 :=
.mark loopBody442_38

def loopBody442_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 7)

def loopBody442_41 : HolLoopProg 64 :=
.mark loopBody442_40

def loopBody442_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 8)

def loopBody442_43 : HolLoopProg 64 :=
.mark loopBody442_42

def loopBody442_44 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 108) ([10, 11, 12, 13, 14, 15, 16, 17]) (some (10, loopBody442_17, loopBody442_1, (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))

def loopBody442_45 : HolLoopProg 64 :=
.mark loopBody442_44

def loopBody442_46 : HolLoopProg 64 :=
.seq loopBody442_45 loopBody442_1

def loopBody442_47 : HolLoopProg 64 :=
.mark loopBody442_46

def loopBody442_48 : HolLoopProg 64 :=
.seq loopBody442_43 loopBody442_47

def loopBody442_49 : HolLoopProg 64 :=
.mark loopBody442_48

def loopBody442_50 : HolLoopProg 64 :=
.seq loopBody442_41 loopBody442_49

def loopBody442_51 : HolLoopProg 64 :=
.mark loopBody442_50

def loopBody442_52 : HolLoopProg 64 :=
.seq loopBody442_39 loopBody442_51

def loopBody442_53 : HolLoopProg 64 :=
.mark loopBody442_52

def loopBody442_54 : HolLoopProg 64 :=
.seq loopBody442_37 loopBody442_53

def loopBody442_55 : HolLoopProg 64 :=
.mark loopBody442_54

def loopBody442_56 : HolLoopProg 64 :=
.seq loopBody442_35 loopBody442_55

def loopBody442_57 : HolLoopProg 64 :=
.mark loopBody442_56

def loopBody442_58 : HolLoopProg 64 :=
.seq loopBody442_33 loopBody442_57

def loopBody442_59 : HolLoopProg 64 :=
.mark loopBody442_58

def loopBody442_60 : HolLoopProg 64 :=
.seq loopBody442_31 loopBody442_59

def loopBody442_61 : HolLoopProg 64 :=
.mark loopBody442_60

def loopBody442_62 : HolLoopProg 64 :=
.seq loopBody442_29 loopBody442_61

def loopBody442_63 : HolLoopProg 64 :=
.mark loopBody442_62

def loopBody442_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody442_65 : HolLoopProg 64 :=
.mark loopBody442_64

def loopBody442_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody442_67 : HolLoopProg 64 :=
.mark loopBody442_66

def loopBody442_68 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 474) ([11]) (some (11, loopBody442_67, loopBody442_1, (Flapjack.Spt.ln)))

def loopBody442_69 : HolLoopProg 64 :=
.mark loopBody442_68

def loopBody442_70 : HolLoopProg 64 :=
.seq loopBody442_69 loopBody442_1

def loopBody442_71 : HolLoopProg 64 :=
.mark loopBody442_70

def loopBody442_72 : HolLoopProg 64 :=
.seq loopBody442_65 loopBody442_71

def loopBody442_73 : HolLoopProg 64 :=
.mark loopBody442_72

def loopBody442_74 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_73

def loopBody442_75 : HolLoopProg 64 :=
.mark loopBody442_74

def loopBody442_76 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_75

def loopBody442_77 : HolLoopProg 64 :=
.mark loopBody442_76

def loopBody442_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody442_79 : HolLoopProg 64 :=
.mark loopBody442_78

def loopBody442_80 : HolLoopProg 64 :=
.call (some ([10], Flapjack.Spt.ln)) (some 486) ([11]) (some (11, loopBody442_67, loopBody442_1, (Flapjack.Spt.ln)))

def loopBody442_81 : HolLoopProg 64 :=
.mark loopBody442_80

def loopBody442_82 : HolLoopProg 64 :=
.seq loopBody442_81 loopBody442_1

def loopBody442_83 : HolLoopProg 64 :=
.mark loopBody442_82

def loopBody442_84 : HolLoopProg 64 :=
.seq loopBody442_79 loopBody442_83

def loopBody442_85 : HolLoopProg 64 :=
.mark loopBody442_84

def loopBody442_86 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_85

def loopBody442_87 : HolLoopProg 64 :=
.mark loopBody442_86

def loopBody442_88 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_87

def loopBody442_89 : HolLoopProg 64 :=
.mark loopBody442_88

def loopBody442_90 : HolLoopProg 64 :=
.seq loopBody442_77 loopBody442_89

def loopBody442_91 : HolLoopProg 64 :=
.mark loopBody442_90

def loopBody442_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody442_93 : HolLoopProg 64 :=
.mark loopBody442_92

def loopBody442_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [10]

def loopBody442_95 : HolLoopProg 64 :=
.mark loopBody442_94

def loopBody442_96 : HolLoopProg 64 :=
.seq loopBody442_95 loopBody442_1

def loopBody442_97 : HolLoopProg 64 :=
.mark loopBody442_96

def loopBody442_98 : HolLoopProg 64 :=
.seq loopBody442_93 loopBody442_97

def loopBody442_99 : HolLoopProg 64 :=
.mark loopBody442_98

def loopBody442_100 : HolLoopProg 64 :=
.seq loopBody442_91 loopBody442_99

def loopBody442_101 : HolLoopProg 64 :=
.mark loopBody442_100

def loopBody442_102 : HolLoopProg 64 :=
.seq loopBody442_63 loopBody442_101

def loopBody442_103 : HolLoopProg 64 :=
.mark loopBody442_102

def loopBody442_104 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_103

def loopBody442_105 : HolLoopProg 64 :=
.mark loopBody442_104

def loopBody442_106 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_105

def loopBody442_107 : HolLoopProg 64 :=
.mark loopBody442_106

def loopBody442_108 : HolLoopProg 64 :=
.seq loopBody442_27 loopBody442_107

def loopBody442_109 : HolLoopProg 64 :=
.mark loopBody442_108

def loopBody442_110 : HolLoopProg 64 :=
.seq loopBody442_13 loopBody442_109

def loopBody442_111 : HolLoopProg 64 :=
.mark loopBody442_110

def loopBody442_112 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_111

def loopBody442_113 : HolLoopProg 64 :=
.mark loopBody442_112

def loopBody442_114 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_113

def loopBody442_115 : HolLoopProg 64 :=
.mark loopBody442_114

def loopBody442_116 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_115

def loopBody442_117 : HolLoopProg 64 :=
.mark loopBody442_116

def loopBody442_118 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_117

def loopBody442_119 : HolLoopProg 64 :=
.mark loopBody442_118

def loopBody442_120 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_119

def loopBody442_121 : HolLoopProg 64 :=
.mark loopBody442_120

def loopBody442_122 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_121

def loopBody442_123 : HolLoopProg 64 :=
.mark loopBody442_122

def loopBody442_124 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_123

def loopBody442_125 : HolLoopProg 64 :=
.mark loopBody442_124

def loopBody442_126 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_125

def loopBody442_127 : HolLoopProg 64 :=
.mark loopBody442_126

def loopBody442_128 : HolLoopProg 64 :=
.seq loopBody442_7 loopBody442_127

def loopBody442_129 : HolLoopProg 64 :=
.mark loopBody442_128

def loopBody442_130 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_129

def loopBody442_131 : HolLoopProg 64 :=
.mark loopBody442_130

def loopBody442_132 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_131

def loopBody442_133 : HolLoopProg 64 :=
.mark loopBody442_132

def loopBody442_134 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_133

def loopBody442_135 : HolLoopProg 64 :=
.mark loopBody442_134

def loopBody442_136 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_135

def loopBody442_137 : HolLoopProg 64 :=
.mark loopBody442_136

def loopBody442_138 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_137

def loopBody442_139 : HolLoopProg 64 :=
.mark loopBody442_138

def loopBody442_140 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_139

def loopBody442_141 : HolLoopProg 64 :=
.mark loopBody442_140

def loopBody442_142 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_141

def loopBody442_143 : HolLoopProg 64 :=
.mark loopBody442_142

def loopBody442_144 : HolLoopProg 64 :=
.seq loopBody442_1 loopBody442_143

def loopBody442_145 : HolLoopProg 64 :=
.mark loopBody442_144

def output442 : Nat × List Nat × HolLoopProg 64 :=
  (506, [], loopBody442_145)
end InitECandidate.Proofs.FrontendStages.Loop
