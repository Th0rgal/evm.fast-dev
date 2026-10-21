import InitECandidate.Proofs.FrontendStages.Loop.Translate669
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody685_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody685_1 : HolLoopProg 64 :=
.mark loopBody685_0

def loopBody685_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody685_3 : HolLoopProg 64 :=
.mark loopBody685_2

def loopBody685_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody685_3, loopBody685_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody685_5 : HolLoopProg 64 :=
.mark loopBody685_4

def loopBody685_6 : HolLoopProg 64 :=
.seq loopBody685_5 loopBody685_1

def loopBody685_7 : HolLoopProg 64 :=
.mark loopBody685_6

def loopBody685_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 96#64)

def loopBody685_9 : HolLoopProg 64 :=
.mark loopBody685_8

def loopBody685_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody685_11 : HolLoopProg 64 :=
.mark loopBody685_10

def loopBody685_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody685_11, loopBody685_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody685_13 : HolLoopProg 64 :=
.mark loopBody685_12

def loopBody685_14 : HolLoopProg 64 :=
.seq loopBody685_13 loopBody685_1

def loopBody685_15 : HolLoopProg 64 :=
.mark loopBody685_14

def loopBody685_16 : HolLoopProg 64 :=
.seq loopBody685_9 loopBody685_15

def loopBody685_17 : HolLoopProg 64 :=
.mark loopBody685_16

def loopBody685_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody685_19 : HolLoopProg 64 :=
.mark loopBody685_18

def loopBody685_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 192#64])

def loopBody685_21 : HolLoopProg 64 :=
.mark loopBody685_20

def loopBody685_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody685_23 : HolLoopProg 64 :=
.mark loopBody685_22

def loopBody685_24 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 737) ([5, 6]) (some (5, loopBody685_23, loopBody685_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody685_25 : HolLoopProg 64 :=
.mark loopBody685_24

def loopBody685_26 : HolLoopProg 64 :=
.seq loopBody685_25 loopBody685_1

def loopBody685_27 : HolLoopProg 64 :=
.mark loopBody685_26

def loopBody685_28 : HolLoopProg 64 :=
.seq loopBody685_21 loopBody685_27

def loopBody685_29 : HolLoopProg 64 :=
.mark loopBody685_28

def loopBody685_30 : HolLoopProg 64 :=
.seq loopBody685_19 loopBody685_29

def loopBody685_31 : HolLoopProg 64 :=
.mark loopBody685_30

def loopBody685_32 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_31

def loopBody685_33 : HolLoopProg 64 :=
.mark loopBody685_32

def loopBody685_34 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_33

def loopBody685_35 : HolLoopProg 64 :=
.mark loopBody685_34

def loopBody685_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody685_37 : HolLoopProg 64 :=
.mark loopBody685_36

def loopBody685_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64])

def loopBody685_39 : HolLoopProg 64 :=
.mark loopBody685_38

def loopBody685_40 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 725) ([5, 6]) (some (5, loopBody685_23, loopBody685_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody685_41 : HolLoopProg 64 :=
.mark loopBody685_40

def loopBody685_42 : HolLoopProg 64 :=
.seq loopBody685_41 loopBody685_1

def loopBody685_43 : HolLoopProg 64 :=
.mark loopBody685_42

def loopBody685_44 : HolLoopProg 64 :=
.seq loopBody685_39 loopBody685_43

def loopBody685_45 : HolLoopProg 64 :=
.mark loopBody685_44

def loopBody685_46 : HolLoopProg 64 :=
.seq loopBody685_37 loopBody685_45

def loopBody685_47 : HolLoopProg 64 :=
.mark loopBody685_46

def loopBody685_48 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_47

def loopBody685_49 : HolLoopProg 64 :=
.mark loopBody685_48

def loopBody685_50 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_49

def loopBody685_51 : HolLoopProg 64 :=
.mark loopBody685_50

def loopBody685_52 : HolLoopProg 64 :=
.seq loopBody685_35 loopBody685_51

def loopBody685_53 : HolLoopProg 64 :=
.mark loopBody685_52

def loopBody685_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody685_55 : HolLoopProg 64 :=
.mark loopBody685_54

def loopBody685_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody685_57 : HolLoopProg 64 :=
.mark loopBody685_56

def loopBody685_58 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 725) ([5, 6]) (some (5, loopBody685_23, loopBody685_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody685_59 : HolLoopProg 64 :=
.mark loopBody685_58

def loopBody685_60 : HolLoopProg 64 :=
.seq loopBody685_59 loopBody685_1

def loopBody685_61 : HolLoopProg 64 :=
.mark loopBody685_60

def loopBody685_62 : HolLoopProg 64 :=
.seq loopBody685_57 loopBody685_61

def loopBody685_63 : HolLoopProg 64 :=
.mark loopBody685_62

def loopBody685_64 : HolLoopProg 64 :=
.seq loopBody685_55 loopBody685_63

def loopBody685_65 : HolLoopProg 64 :=
.mark loopBody685_64

def loopBody685_66 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_65

def loopBody685_67 : HolLoopProg 64 :=
.mark loopBody685_66

def loopBody685_68 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_67

def loopBody685_69 : HolLoopProg 64 :=
.mark loopBody685_68

def loopBody685_70 : HolLoopProg 64 :=
.seq loopBody685_53 loopBody685_69

def loopBody685_71 : HolLoopProg 64 :=
.mark loopBody685_70

def loopBody685_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody685_73 : HolLoopProg 64 :=
.mark loopBody685_72

def loopBody685_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody685_75 : HolLoopProg 64 :=
.mark loopBody685_74

def loopBody685_76 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 725) ([5, 6]) (some (5, loopBody685_23, loopBody685_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody685_77 : HolLoopProg 64 :=
.mark loopBody685_76

def loopBody685_78 : HolLoopProg 64 :=
.seq loopBody685_77 loopBody685_1

def loopBody685_79 : HolLoopProg 64 :=
.mark loopBody685_78

def loopBody685_80 : HolLoopProg 64 :=
.seq loopBody685_75 loopBody685_79

def loopBody685_81 : HolLoopProg 64 :=
.mark loopBody685_80

def loopBody685_82 : HolLoopProg 64 :=
.seq loopBody685_73 loopBody685_81

def loopBody685_83 : HolLoopProg 64 :=
.mark loopBody685_82

def loopBody685_84 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_83

def loopBody685_85 : HolLoopProg 64 :=
.mark loopBody685_84

def loopBody685_86 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_85

def loopBody685_87 : HolLoopProg 64 :=
.mark loopBody685_86

def loopBody685_88 : HolLoopProg 64 :=
.seq loopBody685_71 loopBody685_87

def loopBody685_89 : HolLoopProg 64 :=
.mark loopBody685_88

def loopBody685_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody685_91 : HolLoopProg 64 :=
.mark loopBody685_90

def loopBody685_92 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody685_23, loopBody685_1, (Flapjack.Spt.ln)))

def loopBody685_93 : HolLoopProg 64 :=
.mark loopBody685_92

def loopBody685_94 : HolLoopProg 64 :=
.seq loopBody685_93 loopBody685_1

def loopBody685_95 : HolLoopProg 64 :=
.mark loopBody685_94

def loopBody685_96 : HolLoopProg 64 :=
.seq loopBody685_91 loopBody685_95

def loopBody685_97 : HolLoopProg 64 :=
.mark loopBody685_96

def loopBody685_98 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_97

def loopBody685_99 : HolLoopProg 64 :=
.mark loopBody685_98

def loopBody685_100 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_99

def loopBody685_101 : HolLoopProg 64 :=
.mark loopBody685_100

def loopBody685_102 : HolLoopProg 64 :=
.seq loopBody685_89 loopBody685_101

def loopBody685_103 : HolLoopProg 64 :=
.mark loopBody685_102

def loopBody685_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody685_105 : HolLoopProg 64 :=
.mark loopBody685_104

def loopBody685_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody685_107 : HolLoopProg 64 :=
.mark loopBody685_106

def loopBody685_108 : HolLoopProg 64 :=
.seq loopBody685_107 loopBody685_1

def loopBody685_109 : HolLoopProg 64 :=
.mark loopBody685_108

def loopBody685_110 : HolLoopProg 64 :=
.seq loopBody685_105 loopBody685_109

def loopBody685_111 : HolLoopProg 64 :=
.mark loopBody685_110

def loopBody685_112 : HolLoopProg 64 :=
.seq loopBody685_103 loopBody685_111

def loopBody685_113 : HolLoopProg 64 :=
.mark loopBody685_112

def loopBody685_114 : HolLoopProg 64 :=
.seq loopBody685_17 loopBody685_113

def loopBody685_115 : HolLoopProg 64 :=
.mark loopBody685_114

def loopBody685_116 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_115

def loopBody685_117 : HolLoopProg 64 :=
.mark loopBody685_116

def loopBody685_118 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_117

def loopBody685_119 : HolLoopProg 64 :=
.mark loopBody685_118

def loopBody685_120 : HolLoopProg 64 :=
.seq loopBody685_7 loopBody685_119

def loopBody685_121 : HolLoopProg 64 :=
.mark loopBody685_120

def loopBody685_122 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_121

def loopBody685_123 : HolLoopProg 64 :=
.mark loopBody685_122

def loopBody685_124 : HolLoopProg 64 :=
.seq loopBody685_1 loopBody685_123

def loopBody685_125 : HolLoopProg 64 :=
.mark loopBody685_124

def output685 : Nat × List Nat × HolLoopProg 64 :=
  (749, [0, 1], loopBody685_125)
end InitECandidate.Proofs.FrontendStages.Loop
