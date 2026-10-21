import InitECandidate.Proofs.FrontendStages.Loop.Translate259
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody275_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody275_1 : HolLoopProg 64 :=
.mark loopBody275_0

def loopBody275_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody275_3 : HolLoopProg 64 :=
.mark loopBody275_2

def loopBody275_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody275_5 : HolLoopProg 64 :=
.mark loopBody275_4

def loopBody275_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody275_7 : HolLoopProg 64 :=
.mark loopBody275_6

def loopBody275_8 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 169) ([4, 5]) (some (4, loopBody275_7, loopBody275_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody275_9 : HolLoopProg 64 :=
.mark loopBody275_8

def loopBody275_10 : HolLoopProg 64 :=
.seq loopBody275_9 loopBody275_1

def loopBody275_11 : HolLoopProg 64 :=
.mark loopBody275_10

def loopBody275_12 : HolLoopProg 64 :=
.seq loopBody275_5 loopBody275_11

def loopBody275_13 : HolLoopProg 64 :=
.mark loopBody275_12

def loopBody275_14 : HolLoopProg 64 :=
.seq loopBody275_3 loopBody275_13

def loopBody275_15 : HolLoopProg 64 :=
.mark loopBody275_14

def loopBody275_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 5#64))

def loopBody275_17 : HolLoopProg 64 :=
.mark loopBody275_16

def loopBody275_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody275_19 : HolLoopProg 64 :=
.mark loopBody275_18

def loopBody275_20 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody275_19, loopBody275_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody275_21 : HolLoopProg 64 :=
.mark loopBody275_20

def loopBody275_22 : HolLoopProg 64 :=
.seq loopBody275_21 loopBody275_1

def loopBody275_23 : HolLoopProg 64 :=
.mark loopBody275_22

def loopBody275_24 : HolLoopProg 64 :=
.seq loopBody275_17 loopBody275_23

def loopBody275_25 : HolLoopProg 64 :=
.mark loopBody275_24

def loopBody275_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody275_27 : HolLoopProg 64 :=
.mark loopBody275_26

def loopBody275_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody275_29 : HolLoopProg 64 :=
.mark loopBody275_28

def loopBody275_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody275_31 : HolLoopProg 64 :=
.mark loopBody275_30

def loopBody275_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody275_33 : HolLoopProg 64 :=
.mark loopBody275_32

def loopBody275_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody275_35 : HolLoopProg 64 :=
.mark loopBody275_34

def loopBody275_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody275_33 loopBody275_35 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody275_37 : HolLoopProg 64 :=
.mark loopBody275_36

def loopBody275_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody275_39 : HolLoopProg 64 :=
.mark loopBody275_38

def loopBody275_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody275_41 : HolLoopProg 64 :=
.mark loopBody275_40

def loopBody275_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody275_43 : HolLoopProg 64 :=
.mark loopBody275_42

def loopBody275_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 32#64)

def loopBody275_45 : HolLoopProg 64 :=
.mark loopBody275_44

def loopBody275_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody275_47 : HolLoopProg 64 :=
.mark loopBody275_46

def loopBody275_48 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 335) ([7, 8, 9]) (some (7, loopBody275_47, loopBody275_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody275_49 : HolLoopProg 64 :=
.mark loopBody275_48

def loopBody275_50 : HolLoopProg 64 :=
.seq loopBody275_49 loopBody275_1

def loopBody275_51 : HolLoopProg 64 :=
.mark loopBody275_50

def loopBody275_52 : HolLoopProg 64 :=
.seq loopBody275_45 loopBody275_51

def loopBody275_53 : HolLoopProg 64 :=
.mark loopBody275_52

def loopBody275_54 : HolLoopProg 64 :=
.seq loopBody275_43 loopBody275_53

def loopBody275_55 : HolLoopProg 64 :=
.mark loopBody275_54

def loopBody275_56 : HolLoopProg 64 :=
.seq loopBody275_41 loopBody275_55

def loopBody275_57 : HolLoopProg 64 :=
.mark loopBody275_56

def loopBody275_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 4,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 5#64)])

def loopBody275_59 : HolLoopProg 64 :=
.mark loopBody275_58

def loopBody275_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody275_61 : HolLoopProg 64 :=
.mark loopBody275_60

def loopBody275_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 32#64)

def loopBody275_63 : HolLoopProg 64 :=
.mark loopBody275_62

def loopBody275_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody275_65 : HolLoopProg 64 :=
.mark loopBody275_64

def loopBody275_66 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([8, 9, 10]) (some (8, loopBody275_65, loopBody275_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody275_67 : HolLoopProg 64 :=
.mark loopBody275_66

def loopBody275_68 : HolLoopProg 64 :=
.seq loopBody275_67 loopBody275_1

def loopBody275_69 : HolLoopProg 64 :=
.mark loopBody275_68

def loopBody275_70 : HolLoopProg 64 :=
.seq loopBody275_63 loopBody275_69

def loopBody275_71 : HolLoopProg 64 :=
.mark loopBody275_70

def loopBody275_72 : HolLoopProg 64 :=
.seq loopBody275_61 loopBody275_71

def loopBody275_73 : HolLoopProg 64 :=
.mark loopBody275_72

def loopBody275_74 : HolLoopProg 64 :=
.seq loopBody275_59 loopBody275_73

def loopBody275_75 : HolLoopProg 64 :=
.mark loopBody275_74

def loopBody275_76 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_75

def loopBody275_77 : HolLoopProg 64 :=
.mark loopBody275_76

def loopBody275_78 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_77

def loopBody275_79 : HolLoopProg 64 :=
.mark loopBody275_78

def loopBody275_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody275_81 : HolLoopProg 64 :=
.mark loopBody275_80

def loopBody275_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 7)

def loopBody275_83 : HolLoopProg 64 :=
.mark loopBody275_82

def loopBody275_84 : HolLoopProg 64 :=
.seq loopBody275_83 loopBody275_1

def loopBody275_85 : HolLoopProg 64 :=
.mark loopBody275_84

def loopBody275_86 : HolLoopProg 64 :=
.seq loopBody275_85 loopBody275_1

def loopBody275_87 : HolLoopProg 64 :=
.mark loopBody275_86

def loopBody275_88 : HolLoopProg 64 :=
.seq loopBody275_81 loopBody275_87

def loopBody275_89 : HolLoopProg 64 :=
.mark loopBody275_88

def loopBody275_90 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_89

def loopBody275_91 : HolLoopProg 64 :=
.mark loopBody275_90

def loopBody275_92 : HolLoopProg 64 :=
.seq loopBody275_79 loopBody275_91

def loopBody275_93 : HolLoopProg 64 :=
.mark loopBody275_92

def loopBody275_94 : HolLoopProg 64 :=
.seq loopBody275_57 loopBody275_93

def loopBody275_95 : HolLoopProg 64 :=
.mark loopBody275_94

def loopBody275_96 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_95

def loopBody275_97 : HolLoopProg 64 :=
.mark loopBody275_96

def loopBody275_98 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_97

def loopBody275_99 : HolLoopProg 64 :=
.mark loopBody275_98

def loopBody275_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody275_101 : HolLoopProg 64 :=
.mark loopBody275_100

def loopBody275_102 : HolLoopProg 64 :=
.seq loopBody275_99 loopBody275_101

def loopBody275_103 : HolLoopProg 64 :=
.mark loopBody275_102

def loopBody275_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody275_105 : HolLoopProg 64 :=
.mark loopBody275_104

def loopBody275_106 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody275_103 loopBody275_105 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody275_107 : HolLoopProg 64 :=
.mark loopBody275_106

def loopBody275_108 : HolLoopProg 64 :=
.seq loopBody275_107 loopBody275_1

def loopBody275_109 : HolLoopProg 64 :=
.mark loopBody275_108

def loopBody275_110 : HolLoopProg 64 :=
.seq loopBody275_39 loopBody275_109

def loopBody275_111 : HolLoopProg 64 :=
.mark loopBody275_110

def loopBody275_112 : HolLoopProg 64 :=
.seq loopBody275_37 loopBody275_111

def loopBody275_113 : HolLoopProg 64 :=
.mark loopBody275_112

def loopBody275_114 : HolLoopProg 64 :=
.seq loopBody275_31 loopBody275_113

def loopBody275_115 : HolLoopProg 64 :=
.mark loopBody275_114

def loopBody275_116 : HolLoopProg 64 :=
.seq loopBody275_29 loopBody275_115

def loopBody275_117 : HolLoopProg 64 :=
.mark loopBody275_116

def loopBody275_118 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody275_117 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody275_119 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody275_120 : HolLoopProg 64 :=
.mark loopBody275_119

def loopBody275_121 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody275_122 : HolLoopProg 64 :=
.mark loopBody275_121

def loopBody275_123 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6, 7]

def loopBody275_124 : HolLoopProg 64 :=
.mark loopBody275_123

def loopBody275_125 : HolLoopProg 64 :=
.seq loopBody275_124 loopBody275_1

def loopBody275_126 : HolLoopProg 64 :=
.mark loopBody275_125

def loopBody275_127 : HolLoopProg 64 :=
.seq loopBody275_122 loopBody275_126

def loopBody275_128 : HolLoopProg 64 :=
.mark loopBody275_127

def loopBody275_129 : HolLoopProg 64 :=
.seq loopBody275_120 loopBody275_128

def loopBody275_130 : HolLoopProg 64 :=
.mark loopBody275_129

def loopBody275_131 : HolLoopProg 64 :=
.seq loopBody275_118 loopBody275_130

def loopBody275_132 : HolLoopProg 64 :=
.seq loopBody275_27 loopBody275_131

def loopBody275_133 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_132

def loopBody275_134 : HolLoopProg 64 :=
.seq loopBody275_25 loopBody275_133

def loopBody275_135 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_134

def loopBody275_136 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_135

def loopBody275_137 : HolLoopProg 64 :=
.seq loopBody275_15 loopBody275_136

def loopBody275_138 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_137

def loopBody275_139 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_138

def loopBody275_140 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_139

def loopBody275_141 : HolLoopProg 64 :=
.seq loopBody275_1 loopBody275_140

def output275 : Nat × List Nat × HolLoopProg 64 :=
  (339, [0, 1], loopBody275_141)
end InitECandidate.Proofs.FrontendStages.Loop
