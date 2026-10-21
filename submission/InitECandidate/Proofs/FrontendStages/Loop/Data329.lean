import InitECandidate.Proofs.FrontendStages.Loop.Translate313
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody329_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody329_1 : HolLoopProg 64 :=
.mark loopBody329_0

def loopBody329_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody329_3 : HolLoopProg 64 :=
.mark loopBody329_2

def loopBody329_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 69) ([]) (some (2, loopBody329_3, loopBody329_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody329_5 : HolLoopProg 64 :=
.mark loopBody329_4

def loopBody329_6 : HolLoopProg 64 :=
.seq loopBody329_5 loopBody329_1

def loopBody329_7 : HolLoopProg 64 :=
.mark loopBody329_6

def loopBody329_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 32#64)

def loopBody329_9 : HolLoopProg 64 :=
.mark loopBody329_8

def loopBody329_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody329_11 : HolLoopProg 64 :=
.mark loopBody329_10

def loopBody329_12 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([3]) (some (3, loopBody329_11, loopBody329_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody329_13 : HolLoopProg 64 :=
.mark loopBody329_12

def loopBody329_14 : HolLoopProg 64 :=
.seq loopBody329_13 loopBody329_1

def loopBody329_15 : HolLoopProg 64 :=
.mark loopBody329_14

def loopBody329_16 : HolLoopProg 64 :=
.seq loopBody329_9 loopBody329_15

def loopBody329_17 : HolLoopProg 64 :=
.mark loopBody329_16

def loopBody329_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody329_19 : HolLoopProg 64 :=
.mark loopBody329_18

def loopBody329_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 20#64)

def loopBody329_21 : HolLoopProg 64 :=
.mark loopBody329_20

def loopBody329_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody329_23 : HolLoopProg 64 :=
.mark loopBody329_22

def loopBody329_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody329_25 : HolLoopProg 64 :=
.mark loopBody329_24

def loopBody329_26 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 158) ([4, 5, 6]) (some (4, loopBody329_25, loopBody329_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody329_27 : HolLoopProg 64 :=
.mark loopBody329_26

def loopBody329_28 : HolLoopProg 64 :=
.seq loopBody329_27 loopBody329_1

def loopBody329_29 : HolLoopProg 64 :=
.mark loopBody329_28

def loopBody329_30 : HolLoopProg 64 :=
.seq loopBody329_23 loopBody329_29

def loopBody329_31 : HolLoopProg 64 :=
.mark loopBody329_30

def loopBody329_32 : HolLoopProg 64 :=
.seq loopBody329_21 loopBody329_31

def loopBody329_33 : HolLoopProg 64 :=
.mark loopBody329_32

def loopBody329_34 : HolLoopProg 64 :=
.seq loopBody329_19 loopBody329_33

def loopBody329_35 : HolLoopProg 64 :=
.mark loopBody329_34

def loopBody329_36 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_35

def loopBody329_37 : HolLoopProg 64 :=
.mark loopBody329_36

def loopBody329_38 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_37

def loopBody329_39 : HolLoopProg 64 :=
.mark loopBody329_38

def loopBody329_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 168#64]),
        Flapjack.HolLoopExp.const 24#64]))

def loopBody329_41 : HolLoopProg 64 :=
.mark loopBody329_40

def loopBody329_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody329_43 : HolLoopProg 64 :=
.mark loopBody329_42

def loopBody329_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody329_45 : HolLoopProg 64 :=
.mark loopBody329_44

def loopBody329_46 : HolLoopProg 64 :=
.call (some ([3, 4, 5], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 303) ([6, 7]) (some (6, loopBody329_45, loopBody329_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody329_47 : HolLoopProg 64 :=
.mark loopBody329_46

def loopBody329_48 : HolLoopProg 64 :=
.seq loopBody329_47 loopBody329_1

def loopBody329_49 : HolLoopProg 64 :=
.mark loopBody329_48

def loopBody329_50 : HolLoopProg 64 :=
.seq loopBody329_43 loopBody329_49

def loopBody329_51 : HolLoopProg 64 :=
.mark loopBody329_50

def loopBody329_52 : HolLoopProg 64 :=
.seq loopBody329_41 loopBody329_51

def loopBody329_53 : HolLoopProg 64 :=
.mark loopBody329_52

def loopBody329_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody329_55 : HolLoopProg 64 :=
.mark loopBody329_54

def loopBody329_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody329_57 : HolLoopProg 64 :=
.mark loopBody329_56

def loopBody329_58 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))) (some 70) ([7]) (some (7, loopBody329_57, loopBody329_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody329_59 : HolLoopProg 64 :=
.mark loopBody329_58

def loopBody329_60 : HolLoopProg 64 :=
.seq loopBody329_59 loopBody329_1

def loopBody329_61 : HolLoopProg 64 :=
.mark loopBody329_60

def loopBody329_62 : HolLoopProg 64 :=
.seq loopBody329_55 loopBody329_61

def loopBody329_63 : HolLoopProg 64 :=
.mark loopBody329_62

def loopBody329_64 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_63

def loopBody329_65 : HolLoopProg 64 :=
.mark loopBody329_64

def loopBody329_66 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_65

def loopBody329_67 : HolLoopProg 64 :=
.mark loopBody329_66

def loopBody329_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody329_69 : HolLoopProg 64 :=
.mark loopBody329_68

def loopBody329_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody329_71 : HolLoopProg 64 :=
.mark loopBody329_70

def loopBody329_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody329_73 : HolLoopProg 64 :=
.mark loopBody329_72

def loopBody329_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6, 7, 8]

def loopBody329_75 : HolLoopProg 64 :=
.mark loopBody329_74

def loopBody329_76 : HolLoopProg 64 :=
.seq loopBody329_75 loopBody329_1

def loopBody329_77 : HolLoopProg 64 :=
.mark loopBody329_76

def loopBody329_78 : HolLoopProg 64 :=
.seq loopBody329_73 loopBody329_77

def loopBody329_79 : HolLoopProg 64 :=
.mark loopBody329_78

def loopBody329_80 : HolLoopProg 64 :=
.seq loopBody329_71 loopBody329_79

def loopBody329_81 : HolLoopProg 64 :=
.mark loopBody329_80

def loopBody329_82 : HolLoopProg 64 :=
.seq loopBody329_69 loopBody329_81

def loopBody329_83 : HolLoopProg 64 :=
.mark loopBody329_82

def loopBody329_84 : HolLoopProg 64 :=
.seq loopBody329_67 loopBody329_83

def loopBody329_85 : HolLoopProg 64 :=
.mark loopBody329_84

def loopBody329_86 : HolLoopProg 64 :=
.seq loopBody329_53 loopBody329_85

def loopBody329_87 : HolLoopProg 64 :=
.mark loopBody329_86

def loopBody329_88 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_87

def loopBody329_89 : HolLoopProg 64 :=
.mark loopBody329_88

def loopBody329_90 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_89

def loopBody329_91 : HolLoopProg 64 :=
.mark loopBody329_90

def loopBody329_92 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_91

def loopBody329_93 : HolLoopProg 64 :=
.mark loopBody329_92

def loopBody329_94 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_93

def loopBody329_95 : HolLoopProg 64 :=
.mark loopBody329_94

def loopBody329_96 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_95

def loopBody329_97 : HolLoopProg 64 :=
.mark loopBody329_96

def loopBody329_98 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_97

def loopBody329_99 : HolLoopProg 64 :=
.mark loopBody329_98

def loopBody329_100 : HolLoopProg 64 :=
.seq loopBody329_39 loopBody329_99

def loopBody329_101 : HolLoopProg 64 :=
.mark loopBody329_100

def loopBody329_102 : HolLoopProg 64 :=
.seq loopBody329_17 loopBody329_101

def loopBody329_103 : HolLoopProg 64 :=
.mark loopBody329_102

def loopBody329_104 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_103

def loopBody329_105 : HolLoopProg 64 :=
.mark loopBody329_104

def loopBody329_106 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_105

def loopBody329_107 : HolLoopProg 64 :=
.mark loopBody329_106

def loopBody329_108 : HolLoopProg 64 :=
.seq loopBody329_7 loopBody329_107

def loopBody329_109 : HolLoopProg 64 :=
.mark loopBody329_108

def loopBody329_110 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_109

def loopBody329_111 : HolLoopProg 64 :=
.mark loopBody329_110

def loopBody329_112 : HolLoopProg 64 :=
.seq loopBody329_1 loopBody329_111

def loopBody329_113 : HolLoopProg 64 :=
.mark loopBody329_112

def output329 : Nat × List Nat × HolLoopProg 64 :=
  (393, [0], loopBody329_113)
end InitECandidate.Proofs.FrontendStages.Loop
