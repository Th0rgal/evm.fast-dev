import InitECandidate.Proofs.FrontendStages.Loop.Translate178
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody194_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody194_1 : HolLoopProg 64 :=
.mark loopBody194_0

def loopBody194_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody194_3 : HolLoopProg 64 :=
.mark loopBody194_2

def loopBody194_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody194_3, loopBody194_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody194_5 : HolLoopProg 64 :=
.mark loopBody194_4

def loopBody194_6 : HolLoopProg 64 :=
.seq loopBody194_5 loopBody194_1

def loopBody194_7 : HolLoopProg 64 :=
.mark loopBody194_6

def loopBody194_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 96#64)

def loopBody194_9 : HolLoopProg 64 :=
.mark loopBody194_8

def loopBody194_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody194_11 : HolLoopProg 64 :=
.mark loopBody194_10

def loopBody194_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody194_11, loopBody194_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody194_13 : HolLoopProg 64 :=
.mark loopBody194_12

def loopBody194_14 : HolLoopProg 64 :=
.seq loopBody194_13 loopBody194_1

def loopBody194_15 : HolLoopProg 64 :=
.mark loopBody194_14

def loopBody194_16 : HolLoopProg 64 :=
.seq loopBody194_9 loopBody194_15

def loopBody194_17 : HolLoopProg 64 :=
.mark loopBody194_16

def loopBody194_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody194_19 : HolLoopProg 64 :=
.mark loopBody194_18

def loopBody194_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 20#64)

def loopBody194_21 : HolLoopProg 64 :=
.mark loopBody194_20

def loopBody194_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody194_23 : HolLoopProg 64 :=
.mark loopBody194_22

def loopBody194_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody194_25 : HolLoopProg 64 :=
.mark loopBody194_24

def loopBody194_26 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 242) ([5, 6, 7]) (some (5, loopBody194_25, loopBody194_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody194_27 : HolLoopProg 64 :=
.mark loopBody194_26

def loopBody194_28 : HolLoopProg 64 :=
.seq loopBody194_27 loopBody194_1

def loopBody194_29 : HolLoopProg 64 :=
.mark loopBody194_28

def loopBody194_30 : HolLoopProg 64 :=
.seq loopBody194_23 loopBody194_29

def loopBody194_31 : HolLoopProg 64 :=
.mark loopBody194_30

def loopBody194_32 : HolLoopProg 64 :=
.seq loopBody194_21 loopBody194_31

def loopBody194_33 : HolLoopProg 64 :=
.mark loopBody194_32

def loopBody194_34 : HolLoopProg 64 :=
.seq loopBody194_19 loopBody194_33

def loopBody194_35 : HolLoopProg 64 :=
.mark loopBody194_34

def loopBody194_36 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_35

def loopBody194_37 : HolLoopProg 64 :=
.mark loopBody194_36

def loopBody194_38 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_37

def loopBody194_39 : HolLoopProg 64 :=
.mark loopBody194_38

def loopBody194_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 20#64])

def loopBody194_41 : HolLoopProg 64 :=
.mark loopBody194_40

def loopBody194_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 48#64)

def loopBody194_43 : HolLoopProg 64 :=
.mark loopBody194_42

def loopBody194_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 32#64])

def loopBody194_45 : HolLoopProg 64 :=
.mark loopBody194_44

def loopBody194_46 : HolLoopProg 64 :=
.seq loopBody194_45 loopBody194_29

def loopBody194_47 : HolLoopProg 64 :=
.mark loopBody194_46

def loopBody194_48 : HolLoopProg 64 :=
.seq loopBody194_43 loopBody194_47

def loopBody194_49 : HolLoopProg 64 :=
.mark loopBody194_48

def loopBody194_50 : HolLoopProg 64 :=
.seq loopBody194_41 loopBody194_49

def loopBody194_51 : HolLoopProg 64 :=
.mark loopBody194_50

def loopBody194_52 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_51

def loopBody194_53 : HolLoopProg 64 :=
.mark loopBody194_52

def loopBody194_54 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_53

def loopBody194_55 : HolLoopProg 64 :=
.mark loopBody194_54

def loopBody194_56 : HolLoopProg 64 :=
.seq loopBody194_39 loopBody194_55

def loopBody194_57 : HolLoopProg 64 :=
.mark loopBody194_56

def loopBody194_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 68#64])

def loopBody194_59 : HolLoopProg 64 :=
.mark loopBody194_58

def loopBody194_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 64#64])

def loopBody194_61 : HolLoopProg 64 :=
.mark loopBody194_60

def loopBody194_62 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 242) ([5, 6, 7]) (some (5, loopBody194_25, loopBody194_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody194_63 : HolLoopProg 64 :=
.mark loopBody194_62

def loopBody194_64 : HolLoopProg 64 :=
.seq loopBody194_63 loopBody194_1

def loopBody194_65 : HolLoopProg 64 :=
.mark loopBody194_64

def loopBody194_66 : HolLoopProg 64 :=
.seq loopBody194_61 loopBody194_65

def loopBody194_67 : HolLoopProg 64 :=
.mark loopBody194_66

def loopBody194_68 : HolLoopProg 64 :=
.seq loopBody194_43 loopBody194_67

def loopBody194_69 : HolLoopProg 64 :=
.mark loopBody194_68

def loopBody194_70 : HolLoopProg 64 :=
.seq loopBody194_59 loopBody194_69

def loopBody194_71 : HolLoopProg 64 :=
.mark loopBody194_70

def loopBody194_72 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_71

def loopBody194_73 : HolLoopProg 64 :=
.mark loopBody194_72

def loopBody194_74 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_73

def loopBody194_75 : HolLoopProg 64 :=
.mark loopBody194_74

def loopBody194_76 : HolLoopProg 64 :=
.seq loopBody194_57 loopBody194_75

def loopBody194_77 : HolLoopProg 64 :=
.mark loopBody194_76

def loopBody194_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody194_79 : HolLoopProg 64 :=
.mark loopBody194_78

def loopBody194_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 3#64)

def loopBody194_81 : HolLoopProg 64 :=
.mark loopBody194_80

def loopBody194_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 3#64)

def loopBody194_83 : HolLoopProg 64 :=
.mark loopBody194_82

def loopBody194_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody194_85 : HolLoopProg 64 :=
.mark loopBody194_84

def loopBody194_86 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 235) ([5, 6, 7, 8]) (some (5, loopBody194_25, loopBody194_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody194_87 : HolLoopProg 64 :=
.mark loopBody194_86

def loopBody194_88 : HolLoopProg 64 :=
.seq loopBody194_87 loopBody194_1

def loopBody194_89 : HolLoopProg 64 :=
.mark loopBody194_88

def loopBody194_90 : HolLoopProg 64 :=
.seq loopBody194_85 loopBody194_89

def loopBody194_91 : HolLoopProg 64 :=
.mark loopBody194_90

def loopBody194_92 : HolLoopProg 64 :=
.seq loopBody194_83 loopBody194_91

def loopBody194_93 : HolLoopProg 64 :=
.mark loopBody194_92

def loopBody194_94 : HolLoopProg 64 :=
.seq loopBody194_81 loopBody194_93

def loopBody194_95 : HolLoopProg 64 :=
.mark loopBody194_94

def loopBody194_96 : HolLoopProg 64 :=
.seq loopBody194_79 loopBody194_95

def loopBody194_97 : HolLoopProg 64 :=
.mark loopBody194_96

def loopBody194_98 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_97

def loopBody194_99 : HolLoopProg 64 :=
.mark loopBody194_98

def loopBody194_100 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_99

def loopBody194_101 : HolLoopProg 64 :=
.mark loopBody194_100

def loopBody194_102 : HolLoopProg 64 :=
.seq loopBody194_77 loopBody194_101

def loopBody194_103 : HolLoopProg 64 :=
.mark loopBody194_102

def loopBody194_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody194_105 : HolLoopProg 64 :=
.mark loopBody194_104

def loopBody194_106 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody194_25, loopBody194_1, (Flapjack.Spt.ln)))

def loopBody194_107 : HolLoopProg 64 :=
.mark loopBody194_106

def loopBody194_108 : HolLoopProg 64 :=
.seq loopBody194_107 loopBody194_1

def loopBody194_109 : HolLoopProg 64 :=
.mark loopBody194_108

def loopBody194_110 : HolLoopProg 64 :=
.seq loopBody194_105 loopBody194_109

def loopBody194_111 : HolLoopProg 64 :=
.mark loopBody194_110

def loopBody194_112 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_111

def loopBody194_113 : HolLoopProg 64 :=
.mark loopBody194_112

def loopBody194_114 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_113

def loopBody194_115 : HolLoopProg 64 :=
.mark loopBody194_114

def loopBody194_116 : HolLoopProg 64 :=
.seq loopBody194_103 loopBody194_115

def loopBody194_117 : HolLoopProg 64 :=
.mark loopBody194_116

def loopBody194_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody194_119 : HolLoopProg 64 :=
.mark loopBody194_118

def loopBody194_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody194_121 : HolLoopProg 64 :=
.mark loopBody194_120

def loopBody194_122 : HolLoopProg 64 :=
.seq loopBody194_121 loopBody194_1

def loopBody194_123 : HolLoopProg 64 :=
.mark loopBody194_122

def loopBody194_124 : HolLoopProg 64 :=
.seq loopBody194_119 loopBody194_123

def loopBody194_125 : HolLoopProg 64 :=
.mark loopBody194_124

def loopBody194_126 : HolLoopProg 64 :=
.seq loopBody194_117 loopBody194_125

def loopBody194_127 : HolLoopProg 64 :=
.mark loopBody194_126

def loopBody194_128 : HolLoopProg 64 :=
.seq loopBody194_17 loopBody194_127

def loopBody194_129 : HolLoopProg 64 :=
.mark loopBody194_128

def loopBody194_130 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_129

def loopBody194_131 : HolLoopProg 64 :=
.mark loopBody194_130

def loopBody194_132 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_131

def loopBody194_133 : HolLoopProg 64 :=
.mark loopBody194_132

def loopBody194_134 : HolLoopProg 64 :=
.seq loopBody194_7 loopBody194_133

def loopBody194_135 : HolLoopProg 64 :=
.mark loopBody194_134

def loopBody194_136 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_135

def loopBody194_137 : HolLoopProg 64 :=
.mark loopBody194_136

def loopBody194_138 : HolLoopProg 64 :=
.seq loopBody194_1 loopBody194_137

def loopBody194_139 : HolLoopProg 64 :=
.mark loopBody194_138

def output194 : Nat × List Nat × HolLoopProg 64 :=
  (258, [0, 1], loopBody194_139)
end InitECandidate.Proofs.FrontendStages.Loop
