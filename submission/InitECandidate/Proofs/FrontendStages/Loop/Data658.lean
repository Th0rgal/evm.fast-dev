import InitECandidate.Proofs.FrontendStages.Loop.Translate642
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody658_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody658_1 : HolLoopProg 64 :=
.mark loopBody658_0

def loopBody658_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody658_3 : HolLoopProg 64 :=
.mark loopBody658_2

def loopBody658_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody658_5 : HolLoopProg 64 :=
.mark loopBody658_4

def loopBody658_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody658_7 : HolLoopProg 64 :=
.mark loopBody658_6

def loopBody658_8 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 89) ([8, 9]) (some (8, loopBody658_7, loopBody658_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody658_9 : HolLoopProg 64 :=
.mark loopBody658_8

def loopBody658_10 : HolLoopProg 64 :=
.seq loopBody658_9 loopBody658_1

def loopBody658_11 : HolLoopProg 64 :=
.mark loopBody658_10

def loopBody658_12 : HolLoopProg 64 :=
.seq loopBody658_5 loopBody658_11

def loopBody658_13 : HolLoopProg 64 :=
.mark loopBody658_12

def loopBody658_14 : HolLoopProg 64 :=
.seq loopBody658_3 loopBody658_13

def loopBody658_15 : HolLoopProg 64 :=
.mark loopBody658_14

def loopBody658_16 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_15

def loopBody658_17 : HolLoopProg 64 :=
.mark loopBody658_16

def loopBody658_18 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_17

def loopBody658_19 : HolLoopProg 64 :=
.mark loopBody658_18

def loopBody658_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 8#64])

def loopBody658_21 : HolLoopProg 64 :=
.mark loopBody658_20

def loopBody658_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody658_23 : HolLoopProg 64 :=
.mark loopBody658_22

def loopBody658_24 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 89) ([8, 9]) (some (8, loopBody658_7, loopBody658_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody658_25 : HolLoopProg 64 :=
.mark loopBody658_24

def loopBody658_26 : HolLoopProg 64 :=
.seq loopBody658_25 loopBody658_1

def loopBody658_27 : HolLoopProg 64 :=
.mark loopBody658_26

def loopBody658_28 : HolLoopProg 64 :=
.seq loopBody658_23 loopBody658_27

def loopBody658_29 : HolLoopProg 64 :=
.mark loopBody658_28

def loopBody658_30 : HolLoopProg 64 :=
.seq loopBody658_21 loopBody658_29

def loopBody658_31 : HolLoopProg 64 :=
.mark loopBody658_30

def loopBody658_32 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_31

def loopBody658_33 : HolLoopProg 64 :=
.mark loopBody658_32

def loopBody658_34 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_33

def loopBody658_35 : HolLoopProg 64 :=
.mark loopBody658_34

def loopBody658_36 : HolLoopProg 64 :=
.seq loopBody658_19 loopBody658_35

def loopBody658_37 : HolLoopProg 64 :=
.mark loopBody658_36

def loopBody658_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 16#64])

def loopBody658_39 : HolLoopProg 64 :=
.mark loopBody658_38

def loopBody658_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody658_41 : HolLoopProg 64 :=
.mark loopBody658_40

def loopBody658_42 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))) (some 89) ([8, 9]) (some (8, loopBody658_7, loopBody658_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.ls PUnit.unit))))

def loopBody658_43 : HolLoopProg 64 :=
.mark loopBody658_42

def loopBody658_44 : HolLoopProg 64 :=
.seq loopBody658_43 loopBody658_1

def loopBody658_45 : HolLoopProg 64 :=
.mark loopBody658_44

def loopBody658_46 : HolLoopProg 64 :=
.seq loopBody658_41 loopBody658_45

def loopBody658_47 : HolLoopProg 64 :=
.mark loopBody658_46

def loopBody658_48 : HolLoopProg 64 :=
.seq loopBody658_39 loopBody658_47

def loopBody658_49 : HolLoopProg 64 :=
.mark loopBody658_48

def loopBody658_50 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_49

def loopBody658_51 : HolLoopProg 64 :=
.mark loopBody658_50

def loopBody658_52 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_51

def loopBody658_53 : HolLoopProg 64 :=
.mark loopBody658_52

def loopBody658_54 : HolLoopProg 64 :=
.seq loopBody658_37 loopBody658_53

def loopBody658_55 : HolLoopProg 64 :=
.mark loopBody658_54

def loopBody658_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 24#64])

def loopBody658_57 : HolLoopProg 64 :=
.mark loopBody658_56

def loopBody658_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody658_59 : HolLoopProg 64 :=
.mark loopBody658_58

def loopBody658_60 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))) (some 89) ([8, 9]) (some (8, loopBody658_7, loopBody658_1, (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody658_61 : HolLoopProg 64 :=
.mark loopBody658_60

def loopBody658_62 : HolLoopProg 64 :=
.seq loopBody658_61 loopBody658_1

def loopBody658_63 : HolLoopProg 64 :=
.mark loopBody658_62

def loopBody658_64 : HolLoopProg 64 :=
.seq loopBody658_59 loopBody658_63

def loopBody658_65 : HolLoopProg 64 :=
.mark loopBody658_64

def loopBody658_66 : HolLoopProg 64 :=
.seq loopBody658_57 loopBody658_65

def loopBody658_67 : HolLoopProg 64 :=
.mark loopBody658_66

def loopBody658_68 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_67

def loopBody658_69 : HolLoopProg 64 :=
.mark loopBody658_68

def loopBody658_70 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_69

def loopBody658_71 : HolLoopProg 64 :=
.mark loopBody658_70

def loopBody658_72 : HolLoopProg 64 :=
.seq loopBody658_55 loopBody658_71

def loopBody658_73 : HolLoopProg 64 :=
.mark loopBody658_72

def loopBody658_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 32#64])

def loopBody658_75 : HolLoopProg 64 :=
.mark loopBody658_74

def loopBody658_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 1)

def loopBody658_77 : HolLoopProg 64 :=
.mark loopBody658_76

def loopBody658_78 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)) (some 89) ([8, 9]) (some (8, loopBody658_7, loopBody658_1, (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)))

def loopBody658_79 : HolLoopProg 64 :=
.mark loopBody658_78

def loopBody658_80 : HolLoopProg 64 :=
.seq loopBody658_79 loopBody658_1

def loopBody658_81 : HolLoopProg 64 :=
.mark loopBody658_80

def loopBody658_82 : HolLoopProg 64 :=
.seq loopBody658_77 loopBody658_81

def loopBody658_83 : HolLoopProg 64 :=
.mark loopBody658_82

def loopBody658_84 : HolLoopProg 64 :=
.seq loopBody658_75 loopBody658_83

def loopBody658_85 : HolLoopProg 64 :=
.mark loopBody658_84

def loopBody658_86 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_85

def loopBody658_87 : HolLoopProg 64 :=
.mark loopBody658_86

def loopBody658_88 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_87

def loopBody658_89 : HolLoopProg 64 :=
.mark loopBody658_88

def loopBody658_90 : HolLoopProg 64 :=
.seq loopBody658_73 loopBody658_89

def loopBody658_91 : HolLoopProg 64 :=
.mark loopBody658_90

def loopBody658_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 40#64])

def loopBody658_93 : HolLoopProg 64 :=
.mark loopBody658_92

def loopBody658_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody658_95 : HolLoopProg 64 :=
.mark loopBody658_94

def loopBody658_96 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.ln)) (some 89) ([8, 9]) (some (8, loopBody658_7, loopBody658_1, (Flapjack.Spt.ln)))

def loopBody658_97 : HolLoopProg 64 :=
.mark loopBody658_96

def loopBody658_98 : HolLoopProg 64 :=
.seq loopBody658_97 loopBody658_1

def loopBody658_99 : HolLoopProg 64 :=
.mark loopBody658_98

def loopBody658_100 : HolLoopProg 64 :=
.seq loopBody658_95 loopBody658_99

def loopBody658_101 : HolLoopProg 64 :=
.mark loopBody658_100

def loopBody658_102 : HolLoopProg 64 :=
.seq loopBody658_93 loopBody658_101

def loopBody658_103 : HolLoopProg 64 :=
.mark loopBody658_102

def loopBody658_104 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_103

def loopBody658_105 : HolLoopProg 64 :=
.mark loopBody658_104

def loopBody658_106 : HolLoopProg 64 :=
.seq loopBody658_1 loopBody658_105

def loopBody658_107 : HolLoopProg 64 :=
.mark loopBody658_106

def loopBody658_108 : HolLoopProg 64 :=
.seq loopBody658_91 loopBody658_107

def loopBody658_109 : HolLoopProg 64 :=
.mark loopBody658_108

def loopBody658_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody658_111 : HolLoopProg 64 :=
.mark loopBody658_110

def loopBody658_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody658_113 : HolLoopProg 64 :=
.mark loopBody658_112

def loopBody658_114 : HolLoopProg 64 :=
.seq loopBody658_113 loopBody658_1

def loopBody658_115 : HolLoopProg 64 :=
.mark loopBody658_114

def loopBody658_116 : HolLoopProg 64 :=
.seq loopBody658_111 loopBody658_115

def loopBody658_117 : HolLoopProg 64 :=
.mark loopBody658_116

def loopBody658_118 : HolLoopProg 64 :=
.seq loopBody658_109 loopBody658_117

def loopBody658_119 : HolLoopProg 64 :=
.mark loopBody658_118

def output658 : Nat × List Nat × HolLoopProg 64 :=
  (722, [0, 1, 2, 3, 4, 5, 6], loopBody658_119)
end InitECandidate.Proofs.FrontendStages.Loop
