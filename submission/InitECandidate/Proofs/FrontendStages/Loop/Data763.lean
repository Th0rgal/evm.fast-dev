import InitECandidate.Proofs.FrontendStages.Loop.Translate747
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody763_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody763_1 : HolLoopProg 64 :=
.mark loopBody763_0

def loopBody763_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody763_3 : HolLoopProg 64 :=
.mark loopBody763_2

def loopBody763_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64]))

def loopBody763_5 : HolLoopProg 64 :=
.mark loopBody763_4

def loopBody763_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody763_7 : HolLoopProg 64 :=
.mark loopBody763_6

def loopBody763_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody763_9 : HolLoopProg 64 :=
.mark loopBody763_8

def loopBody763_10 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 461) ([4]) (some (4, loopBody763_9, loopBody763_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody763_11 : HolLoopProg 64 :=
.mark loopBody763_10

def loopBody763_12 : HolLoopProg 64 :=
.seq loopBody763_11 loopBody763_1

def loopBody763_13 : HolLoopProg 64 :=
.mark loopBody763_12

def loopBody763_14 : HolLoopProg 64 :=
.seq loopBody763_7 loopBody763_13

def loopBody763_15 : HolLoopProg 64 :=
.mark loopBody763_14

def loopBody763_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody763_17 : HolLoopProg 64 :=
.mark loopBody763_16

def loopBody763_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 12#64)

def loopBody763_19 : HolLoopProg 64 :=
.mark loopBody763_18

def loopBody763_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 7 7 5 6)

def loopBody763_21 : HolLoopProg 64 :=
.mark loopBody763_20

def loopBody763_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 60#64, Flapjack.HolLoopExp.var 7])

def loopBody763_23 : HolLoopProg 64 :=
.mark loopBody763_22

def loopBody763_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody763_25 : HolLoopProg 64 :=
.mark loopBody763_24

def loopBody763_26 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 466) ([8]) (some (5, loopBody763_25, loopBody763_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody763_27 : HolLoopProg 64 :=
.mark loopBody763_26

def loopBody763_28 : HolLoopProg 64 :=
.seq loopBody763_27 loopBody763_1

def loopBody763_29 : HolLoopProg 64 :=
.mark loopBody763_28

def loopBody763_30 : HolLoopProg 64 :=
.seq loopBody763_23 loopBody763_29

def loopBody763_31 : HolLoopProg 64 :=
.mark loopBody763_30

def loopBody763_32 : HolLoopProg 64 :=
.seq loopBody763_21 loopBody763_31

def loopBody763_33 : HolLoopProg 64 :=
.mark loopBody763_32

def loopBody763_34 : HolLoopProg 64 :=
.seq loopBody763_19 loopBody763_33

def loopBody763_35 : HolLoopProg 64 :=
.mark loopBody763_34

def loopBody763_36 : HolLoopProg 64 :=
.seq loopBody763_17 loopBody763_35

def loopBody763_37 : HolLoopProg 64 :=
.mark loopBody763_36

def loopBody763_38 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_37

def loopBody763_39 : HolLoopProg 64 :=
.mark loopBody763_38

def loopBody763_40 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_39

def loopBody763_41 : HolLoopProg 64 :=
.mark loopBody763_40

def loopBody763_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody763_43 : HolLoopProg 64 :=
.mark loopBody763_42

def loopBody763_44 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 68) ([5]) (some (5, loopBody763_25, loopBody763_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))

def loopBody763_45 : HolLoopProg 64 :=
.mark loopBody763_44

def loopBody763_46 : HolLoopProg 64 :=
.seq loopBody763_45 loopBody763_1

def loopBody763_47 : HolLoopProg 64 :=
.mark loopBody763_46

def loopBody763_48 : HolLoopProg 64 :=
.seq loopBody763_43 loopBody763_47

def loopBody763_49 : HolLoopProg 64 :=
.mark loopBody763_48

def loopBody763_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 88#64]))

def loopBody763_51 : HolLoopProg 64 :=
.mark loopBody763_50

def loopBody763_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody763_53 : HolLoopProg 64 :=
.mark loopBody763_52

def loopBody763_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody763_55 : HolLoopProg 64 :=
.mark loopBody763_54

def loopBody763_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody763_57 : HolLoopProg 64 :=
.mark loopBody763_56

def loopBody763_58 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 153) ([6, 7, 8]) (some (6, loopBody763_57, loopBody763_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody763_59 : HolLoopProg 64 :=
.mark loopBody763_58

def loopBody763_60 : HolLoopProg 64 :=
.seq loopBody763_59 loopBody763_1

def loopBody763_61 : HolLoopProg 64 :=
.mark loopBody763_60

def loopBody763_62 : HolLoopProg 64 :=
.seq loopBody763_55 loopBody763_61

def loopBody763_63 : HolLoopProg 64 :=
.mark loopBody763_62

def loopBody763_64 : HolLoopProg 64 :=
.seq loopBody763_53 loopBody763_63

def loopBody763_65 : HolLoopProg 64 :=
.mark loopBody763_64

def loopBody763_66 : HolLoopProg 64 :=
.seq loopBody763_51 loopBody763_65

def loopBody763_67 : HolLoopProg 64 :=
.mark loopBody763_66

def loopBody763_68 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_67

def loopBody763_69 : HolLoopProg 64 :=
.mark loopBody763_68

def loopBody763_70 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_69

def loopBody763_71 : HolLoopProg 64 :=
.mark loopBody763_70

def loopBody763_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody763_73 : HolLoopProg 64 :=
.mark loopBody763_72

def loopBody763_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody763_75 : HolLoopProg 64 :=
.mark loopBody763_74

def loopBody763_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody763_77 : HolLoopProg 64 :=
.mark loopBody763_76

def loopBody763_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 5) 7

def loopBody763_79 : HolLoopProg 64 :=
.mark loopBody763_78

def loopBody763_80 : HolLoopProg 64 :=
.seq loopBody763_79 loopBody763_1

def loopBody763_81 : HolLoopProg 64 :=
.mark loopBody763_80

def loopBody763_82 : HolLoopProg 64 :=
.seq loopBody763_77 loopBody763_81

def loopBody763_83 : HolLoopProg 64 :=
.mark loopBody763_82

def loopBody763_84 : HolLoopProg 64 :=
.seq loopBody763_83 loopBody763_1

def loopBody763_85 : HolLoopProg 64 :=
.mark loopBody763_84

def loopBody763_86 : HolLoopProg 64 :=
.seq loopBody763_75 loopBody763_85

def loopBody763_87 : HolLoopProg 64 :=
.mark loopBody763_86

def loopBody763_88 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_87

def loopBody763_89 : HolLoopProg 64 :=
.mark loopBody763_88

def loopBody763_90 : HolLoopProg 64 :=
.seq loopBody763_73 loopBody763_89

def loopBody763_91 : HolLoopProg 64 :=
.mark loopBody763_90

def loopBody763_92 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_91

def loopBody763_93 : HolLoopProg 64 :=
.mark loopBody763_92

def loopBody763_94 : HolLoopProg 64 :=
.seq loopBody763_71 loopBody763_93

def loopBody763_95 : HolLoopProg 64 :=
.mark loopBody763_94

def loopBody763_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody763_97 : HolLoopProg 64 :=
.mark loopBody763_96

def loopBody763_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 32#64)

def loopBody763_99 : HolLoopProg 64 :=
.mark loopBody763_98

def loopBody763_100 : HolLoopProg 64 :=
.seq loopBody763_99 loopBody763_85

def loopBody763_101 : HolLoopProg 64 :=
.mark loopBody763_100

def loopBody763_102 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_101

def loopBody763_103 : HolLoopProg 64 :=
.mark loopBody763_102

def loopBody763_104 : HolLoopProg 64 :=
.seq loopBody763_97 loopBody763_103

def loopBody763_105 : HolLoopProg 64 :=
.mark loopBody763_104

def loopBody763_106 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_105

def loopBody763_107 : HolLoopProg 64 :=
.mark loopBody763_106

def loopBody763_108 : HolLoopProg 64 :=
.seq loopBody763_95 loopBody763_107

def loopBody763_109 : HolLoopProg 64 :=
.mark loopBody763_108

def loopBody763_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody763_111 : HolLoopProg 64 :=
.mark loopBody763_110

def loopBody763_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody763_113 : HolLoopProg 64 :=
.mark loopBody763_112

def loopBody763_114 : HolLoopProg 64 :=
.seq loopBody763_113 loopBody763_1

def loopBody763_115 : HolLoopProg 64 :=
.mark loopBody763_114

def loopBody763_116 : HolLoopProg 64 :=
.seq loopBody763_111 loopBody763_115

def loopBody763_117 : HolLoopProg 64 :=
.mark loopBody763_116

def loopBody763_118 : HolLoopProg 64 :=
.seq loopBody763_109 loopBody763_117

def loopBody763_119 : HolLoopProg 64 :=
.mark loopBody763_118

def loopBody763_120 : HolLoopProg 64 :=
.seq loopBody763_49 loopBody763_119

def loopBody763_121 : HolLoopProg 64 :=
.mark loopBody763_120

def loopBody763_122 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_121

def loopBody763_123 : HolLoopProg 64 :=
.mark loopBody763_122

def loopBody763_124 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_123

def loopBody763_125 : HolLoopProg 64 :=
.mark loopBody763_124

def loopBody763_126 : HolLoopProg 64 :=
.seq loopBody763_41 loopBody763_125

def loopBody763_127 : HolLoopProg 64 :=
.mark loopBody763_126

def loopBody763_128 : HolLoopProg 64 :=
.seq loopBody763_15 loopBody763_127

def loopBody763_129 : HolLoopProg 64 :=
.mark loopBody763_128

def loopBody763_130 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_129

def loopBody763_131 : HolLoopProg 64 :=
.mark loopBody763_130

def loopBody763_132 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_131

def loopBody763_133 : HolLoopProg 64 :=
.mark loopBody763_132

def loopBody763_134 : HolLoopProg 64 :=
.seq loopBody763_5 loopBody763_133

def loopBody763_135 : HolLoopProg 64 :=
.mark loopBody763_134

def loopBody763_136 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_135

def loopBody763_137 : HolLoopProg 64 :=
.mark loopBody763_136

def loopBody763_138 : HolLoopProg 64 :=
.seq loopBody763_3 loopBody763_137

def loopBody763_139 : HolLoopProg 64 :=
.mark loopBody763_138

def loopBody763_140 : HolLoopProg 64 :=
.seq loopBody763_1 loopBody763_139

def loopBody763_141 : HolLoopProg 64 :=
.mark loopBody763_140

def output763 : Nat × List Nat × HolLoopProg 64 :=
  (827, [], loopBody763_141)
end InitECandidate.Proofs.FrontendStages.Loop
