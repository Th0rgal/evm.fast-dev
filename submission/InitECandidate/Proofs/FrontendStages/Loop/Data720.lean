import InitECandidate.Proofs.FrontendStages.Loop.Translate704
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody720_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody720_1 : HolLoopProg 64 :=
.mark loopBody720_0

def loopBody720_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody720_3 : HolLoopProg 64 :=
.mark loopBody720_2

def loopBody720_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody720_3, loopBody720_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody720_5 : HolLoopProg 64 :=
.mark loopBody720_4

def loopBody720_6 : HolLoopProg 64 :=
.seq loopBody720_5 loopBody720_1

def loopBody720_7 : HolLoopProg 64 :=
.mark loopBody720_6

def loopBody720_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 192#64)

def loopBody720_9 : HolLoopProg 64 :=
.mark loopBody720_8

def loopBody720_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody720_11 : HolLoopProg 64 :=
.mark loopBody720_10

def loopBody720_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody720_11, loopBody720_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody720_13 : HolLoopProg 64 :=
.mark loopBody720_12

def loopBody720_14 : HolLoopProg 64 :=
.seq loopBody720_13 loopBody720_1

def loopBody720_15 : HolLoopProg 64 :=
.mark loopBody720_14

def loopBody720_16 : HolLoopProg 64 :=
.seq loopBody720_9 loopBody720_15

def loopBody720_17 : HolLoopProg 64 :=
.mark loopBody720_16

def loopBody720_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody720_19 : HolLoopProg 64 :=
.mark loopBody720_18

def loopBody720_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody720_21 : HolLoopProg 64 :=
.mark loopBody720_20

def loopBody720_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody720_23 : HolLoopProg 64 :=
.mark loopBody720_22

def loopBody720_24 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 781) ([5, 6]) (some (5, loopBody720_23, loopBody720_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody720_25 : HolLoopProg 64 :=
.mark loopBody720_24

def loopBody720_26 : HolLoopProg 64 :=
.seq loopBody720_25 loopBody720_1

def loopBody720_27 : HolLoopProg 64 :=
.mark loopBody720_26

def loopBody720_28 : HolLoopProg 64 :=
.seq loopBody720_21 loopBody720_27

def loopBody720_29 : HolLoopProg 64 :=
.mark loopBody720_28

def loopBody720_30 : HolLoopProg 64 :=
.seq loopBody720_19 loopBody720_29

def loopBody720_31 : HolLoopProg 64 :=
.mark loopBody720_30

def loopBody720_32 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_31

def loopBody720_33 : HolLoopProg 64 :=
.mark loopBody720_32

def loopBody720_34 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_33

def loopBody720_35 : HolLoopProg 64 :=
.mark loopBody720_34

def loopBody720_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody720_37 : HolLoopProg 64 :=
.mark loopBody720_36

def loopBody720_38 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 724) ([5, 6]) (some (5, loopBody720_23, loopBody720_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody720_39 : HolLoopProg 64 :=
.mark loopBody720_38

def loopBody720_40 : HolLoopProg 64 :=
.seq loopBody720_39 loopBody720_1

def loopBody720_41 : HolLoopProg 64 :=
.mark loopBody720_40

def loopBody720_42 : HolLoopProg 64 :=
.seq loopBody720_37 loopBody720_41

def loopBody720_43 : HolLoopProg 64 :=
.mark loopBody720_42

def loopBody720_44 : HolLoopProg 64 :=
.seq loopBody720_19 loopBody720_43

def loopBody720_45 : HolLoopProg 64 :=
.mark loopBody720_44

def loopBody720_46 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_45

def loopBody720_47 : HolLoopProg 64 :=
.mark loopBody720_46

def loopBody720_48 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_47

def loopBody720_49 : HolLoopProg 64 :=
.mark loopBody720_48

def loopBody720_50 : HolLoopProg 64 :=
.seq loopBody720_35 loopBody720_49

def loopBody720_51 : HolLoopProg 64 :=
.mark loopBody720_50

def loopBody720_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 48#64])

def loopBody720_53 : HolLoopProg 64 :=
.mark loopBody720_52

def loopBody720_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 64#64])

def loopBody720_55 : HolLoopProg 64 :=
.mark loopBody720_54

def loopBody720_56 : HolLoopProg 64 :=
.seq loopBody720_55 loopBody720_41

def loopBody720_57 : HolLoopProg 64 :=
.mark loopBody720_56

def loopBody720_58 : HolLoopProg 64 :=
.seq loopBody720_53 loopBody720_57

def loopBody720_59 : HolLoopProg 64 :=
.mark loopBody720_58

def loopBody720_60 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_59

def loopBody720_61 : HolLoopProg 64 :=
.mark loopBody720_60

def loopBody720_62 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_61

def loopBody720_63 : HolLoopProg 64 :=
.mark loopBody720_62

def loopBody720_64 : HolLoopProg 64 :=
.seq loopBody720_51 loopBody720_63

def loopBody720_65 : HolLoopProg 64 :=
.mark loopBody720_64

def loopBody720_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 96#64])

def loopBody720_67 : HolLoopProg 64 :=
.mark loopBody720_66

def loopBody720_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 128#64])

def loopBody720_69 : HolLoopProg 64 :=
.mark loopBody720_68

def loopBody720_70 : HolLoopProg 64 :=
.seq loopBody720_69 loopBody720_41

def loopBody720_71 : HolLoopProg 64 :=
.mark loopBody720_70

def loopBody720_72 : HolLoopProg 64 :=
.seq loopBody720_67 loopBody720_71

def loopBody720_73 : HolLoopProg 64 :=
.mark loopBody720_72

def loopBody720_74 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_73

def loopBody720_75 : HolLoopProg 64 :=
.mark loopBody720_74

def loopBody720_76 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_75

def loopBody720_77 : HolLoopProg 64 :=
.mark loopBody720_76

def loopBody720_78 : HolLoopProg 64 :=
.seq loopBody720_65 loopBody720_77

def loopBody720_79 : HolLoopProg 64 :=
.mark loopBody720_78

def loopBody720_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 144#64])

def loopBody720_81 : HolLoopProg 64 :=
.mark loopBody720_80

def loopBody720_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 192#64])

def loopBody720_83 : HolLoopProg 64 :=
.mark loopBody720_82

def loopBody720_84 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 724) ([5, 6]) (some (5, loopBody720_23, loopBody720_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody720_85 : HolLoopProg 64 :=
.mark loopBody720_84

def loopBody720_86 : HolLoopProg 64 :=
.seq loopBody720_85 loopBody720_1

def loopBody720_87 : HolLoopProg 64 :=
.mark loopBody720_86

def loopBody720_88 : HolLoopProg 64 :=
.seq loopBody720_83 loopBody720_87

def loopBody720_89 : HolLoopProg 64 :=
.mark loopBody720_88

def loopBody720_90 : HolLoopProg 64 :=
.seq loopBody720_81 loopBody720_89

def loopBody720_91 : HolLoopProg 64 :=
.mark loopBody720_90

def loopBody720_92 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_91

def loopBody720_93 : HolLoopProg 64 :=
.mark loopBody720_92

def loopBody720_94 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_93

def loopBody720_95 : HolLoopProg 64 :=
.mark loopBody720_94

def loopBody720_96 : HolLoopProg 64 :=
.seq loopBody720_79 loopBody720_95

def loopBody720_97 : HolLoopProg 64 :=
.mark loopBody720_96

def loopBody720_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody720_99 : HolLoopProg 64 :=
.mark loopBody720_98

def loopBody720_100 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody720_23, loopBody720_1, (Flapjack.Spt.ln)))

def loopBody720_101 : HolLoopProg 64 :=
.mark loopBody720_100

def loopBody720_102 : HolLoopProg 64 :=
.seq loopBody720_101 loopBody720_1

def loopBody720_103 : HolLoopProg 64 :=
.mark loopBody720_102

def loopBody720_104 : HolLoopProg 64 :=
.seq loopBody720_99 loopBody720_103

def loopBody720_105 : HolLoopProg 64 :=
.mark loopBody720_104

def loopBody720_106 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_105

def loopBody720_107 : HolLoopProg 64 :=
.mark loopBody720_106

def loopBody720_108 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_107

def loopBody720_109 : HolLoopProg 64 :=
.mark loopBody720_108

def loopBody720_110 : HolLoopProg 64 :=
.seq loopBody720_97 loopBody720_109

def loopBody720_111 : HolLoopProg 64 :=
.mark loopBody720_110

def loopBody720_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody720_113 : HolLoopProg 64 :=
.mark loopBody720_112

def loopBody720_114 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody720_115 : HolLoopProg 64 :=
.mark loopBody720_114

def loopBody720_116 : HolLoopProg 64 :=
.seq loopBody720_115 loopBody720_1

def loopBody720_117 : HolLoopProg 64 :=
.mark loopBody720_116

def loopBody720_118 : HolLoopProg 64 :=
.seq loopBody720_113 loopBody720_117

def loopBody720_119 : HolLoopProg 64 :=
.mark loopBody720_118

def loopBody720_120 : HolLoopProg 64 :=
.seq loopBody720_111 loopBody720_119

def loopBody720_121 : HolLoopProg 64 :=
.mark loopBody720_120

def loopBody720_122 : HolLoopProg 64 :=
.seq loopBody720_17 loopBody720_121

def loopBody720_123 : HolLoopProg 64 :=
.mark loopBody720_122

def loopBody720_124 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_123

def loopBody720_125 : HolLoopProg 64 :=
.mark loopBody720_124

def loopBody720_126 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_125

def loopBody720_127 : HolLoopProg 64 :=
.mark loopBody720_126

def loopBody720_128 : HolLoopProg 64 :=
.seq loopBody720_7 loopBody720_127

def loopBody720_129 : HolLoopProg 64 :=
.mark loopBody720_128

def loopBody720_130 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_129

def loopBody720_131 : HolLoopProg 64 :=
.mark loopBody720_130

def loopBody720_132 : HolLoopProg 64 :=
.seq loopBody720_1 loopBody720_131

def loopBody720_133 : HolLoopProg 64 :=
.mark loopBody720_132

def output720 : Nat × List Nat × HolLoopProg 64 :=
  (784, [0, 1], loopBody720_133)
end InitECandidate.Proofs.FrontendStages.Loop
