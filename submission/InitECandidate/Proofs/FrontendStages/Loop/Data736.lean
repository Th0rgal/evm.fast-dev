import InitECandidate.Proofs.FrontendStages.Loop.Translate720
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody736_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody736_1 : HolLoopProg 64 :=
.mark loopBody736_0

def loopBody736_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody736_3 : HolLoopProg 64 :=
.mark loopBody736_2

def loopBody736_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody736_3, loopBody736_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody736_5 : HolLoopProg 64 :=
.mark loopBody736_4

def loopBody736_6 : HolLoopProg 64 :=
.seq loopBody736_5 loopBody736_1

def loopBody736_7 : HolLoopProg 64 :=
.mark loopBody736_6

def loopBody736_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 288#64)

def loopBody736_9 : HolLoopProg 64 :=
.mark loopBody736_8

def loopBody736_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody736_11 : HolLoopProg 64 :=
.mark loopBody736_10

def loopBody736_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody736_11, loopBody736_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody736_13 : HolLoopProg 64 :=
.mark loopBody736_12

def loopBody736_14 : HolLoopProg 64 :=
.seq loopBody736_13 loopBody736_1

def loopBody736_15 : HolLoopProg 64 :=
.mark loopBody736_14

def loopBody736_16 : HolLoopProg 64 :=
.seq loopBody736_9 loopBody736_15

def loopBody736_17 : HolLoopProg 64 :=
.mark loopBody736_16

def loopBody736_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody736_19 : HolLoopProg 64 :=
.mark loopBody736_18

def loopBody736_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody736_21 : HolLoopProg 64 :=
.mark loopBody736_20

def loopBody736_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody736_23 : HolLoopProg 64 :=
.mark loopBody736_22

def loopBody736_24 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 797) ([5, 6]) (some (5, loopBody736_23, loopBody736_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody736_25 : HolLoopProg 64 :=
.mark loopBody736_24

def loopBody736_26 : HolLoopProg 64 :=
.seq loopBody736_25 loopBody736_1

def loopBody736_27 : HolLoopProg 64 :=
.mark loopBody736_26

def loopBody736_28 : HolLoopProg 64 :=
.seq loopBody736_21 loopBody736_27

def loopBody736_29 : HolLoopProg 64 :=
.mark loopBody736_28

def loopBody736_30 : HolLoopProg 64 :=
.seq loopBody736_19 loopBody736_29

def loopBody736_31 : HolLoopProg 64 :=
.mark loopBody736_30

def loopBody736_32 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_31

def loopBody736_33 : HolLoopProg 64 :=
.mark loopBody736_32

def loopBody736_34 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_33

def loopBody736_35 : HolLoopProg 64 :=
.mark loopBody736_34

def loopBody736_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody736_37 : HolLoopProg 64 :=
.mark loopBody736_36

def loopBody736_38 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 799) ([5, 6]) (some (5, loopBody736_23, loopBody736_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody736_39 : HolLoopProg 64 :=
.mark loopBody736_38

def loopBody736_40 : HolLoopProg 64 :=
.seq loopBody736_39 loopBody736_1

def loopBody736_41 : HolLoopProg 64 :=
.mark loopBody736_40

def loopBody736_42 : HolLoopProg 64 :=
.seq loopBody736_37 loopBody736_41

def loopBody736_43 : HolLoopProg 64 :=
.mark loopBody736_42

def loopBody736_44 : HolLoopProg 64 :=
.seq loopBody736_19 loopBody736_43

def loopBody736_45 : HolLoopProg 64 :=
.mark loopBody736_44

def loopBody736_46 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_45

def loopBody736_47 : HolLoopProg 64 :=
.mark loopBody736_46

def loopBody736_48 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_47

def loopBody736_49 : HolLoopProg 64 :=
.mark loopBody736_48

def loopBody736_50 : HolLoopProg 64 :=
.seq loopBody736_35 loopBody736_49

def loopBody736_51 : HolLoopProg 64 :=
.mark loopBody736_50

def loopBody736_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody736_53 : HolLoopProg 64 :=
.mark loopBody736_52

def loopBody736_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 1632#64])

def loopBody736_55 : HolLoopProg 64 :=
.mark loopBody736_54

def loopBody736_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 10#64)

def loopBody736_57 : HolLoopProg 64 :=
.mark loopBody736_56

def loopBody736_58 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 780) ([5, 6, 7, 8]) (some (5, loopBody736_23, loopBody736_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody736_59 : HolLoopProg 64 :=
.mark loopBody736_58

def loopBody736_60 : HolLoopProg 64 :=
.seq loopBody736_59 loopBody736_1

def loopBody736_61 : HolLoopProg 64 :=
.mark loopBody736_60

def loopBody736_62 : HolLoopProg 64 :=
.seq loopBody736_57 loopBody736_61

def loopBody736_63 : HolLoopProg 64 :=
.mark loopBody736_62

def loopBody736_64 : HolLoopProg 64 :=
.seq loopBody736_55 loopBody736_63

def loopBody736_65 : HolLoopProg 64 :=
.mark loopBody736_64

def loopBody736_66 : HolLoopProg 64 :=
.seq loopBody736_37 loopBody736_65

def loopBody736_67 : HolLoopProg 64 :=
.mark loopBody736_66

def loopBody736_68 : HolLoopProg 64 :=
.seq loopBody736_53 loopBody736_67

def loopBody736_69 : HolLoopProg 64 :=
.mark loopBody736_68

def loopBody736_70 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_69

def loopBody736_71 : HolLoopProg 64 :=
.mark loopBody736_70

def loopBody736_72 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_71

def loopBody736_73 : HolLoopProg 64 :=
.mark loopBody736_72

def loopBody736_74 : HolLoopProg 64 :=
.seq loopBody736_51 loopBody736_73

def loopBody736_75 : HolLoopProg 64 :=
.mark loopBody736_74

def loopBody736_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody736_77 : HolLoopProg 64 :=
.mark loopBody736_76

def loopBody736_78 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody736_23, loopBody736_1, (Flapjack.Spt.ln)))

def loopBody736_79 : HolLoopProg 64 :=
.mark loopBody736_78

def loopBody736_80 : HolLoopProg 64 :=
.seq loopBody736_79 loopBody736_1

def loopBody736_81 : HolLoopProg 64 :=
.mark loopBody736_80

def loopBody736_82 : HolLoopProg 64 :=
.seq loopBody736_77 loopBody736_81

def loopBody736_83 : HolLoopProg 64 :=
.mark loopBody736_82

def loopBody736_84 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_83

def loopBody736_85 : HolLoopProg 64 :=
.mark loopBody736_84

def loopBody736_86 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_85

def loopBody736_87 : HolLoopProg 64 :=
.mark loopBody736_86

def loopBody736_88 : HolLoopProg 64 :=
.seq loopBody736_75 loopBody736_87

def loopBody736_89 : HolLoopProg 64 :=
.mark loopBody736_88

def loopBody736_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody736_91 : HolLoopProg 64 :=
.mark loopBody736_90

def loopBody736_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody736_93 : HolLoopProg 64 :=
.mark loopBody736_92

def loopBody736_94 : HolLoopProg 64 :=
.seq loopBody736_93 loopBody736_1

def loopBody736_95 : HolLoopProg 64 :=
.mark loopBody736_94

def loopBody736_96 : HolLoopProg 64 :=
.seq loopBody736_91 loopBody736_95

def loopBody736_97 : HolLoopProg 64 :=
.mark loopBody736_96

def loopBody736_98 : HolLoopProg 64 :=
.seq loopBody736_89 loopBody736_97

def loopBody736_99 : HolLoopProg 64 :=
.mark loopBody736_98

def loopBody736_100 : HolLoopProg 64 :=
.seq loopBody736_17 loopBody736_99

def loopBody736_101 : HolLoopProg 64 :=
.mark loopBody736_100

def loopBody736_102 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_101

def loopBody736_103 : HolLoopProg 64 :=
.mark loopBody736_102

def loopBody736_104 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_103

def loopBody736_105 : HolLoopProg 64 :=
.mark loopBody736_104

def loopBody736_106 : HolLoopProg 64 :=
.seq loopBody736_7 loopBody736_105

def loopBody736_107 : HolLoopProg 64 :=
.mark loopBody736_106

def loopBody736_108 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_107

def loopBody736_109 : HolLoopProg 64 :=
.mark loopBody736_108

def loopBody736_110 : HolLoopProg 64 :=
.seq loopBody736_1 loopBody736_109

def loopBody736_111 : HolLoopProg 64 :=
.mark loopBody736_110

def output736 : Nat × List Nat × HolLoopProg 64 :=
  (800, [0, 1], loopBody736_111)
end InitECandidate.Proofs.FrontendStages.Loop
