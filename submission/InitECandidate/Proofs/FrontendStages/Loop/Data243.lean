import InitECandidate.Proofs.FrontendStages.Loop.Translate227
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody243_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody243_1 : HolLoopProg 64 :=
.mark loopBody243_0

def loopBody243_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody243_3 : HolLoopProg 64 :=
.mark loopBody243_2

def loopBody243_4 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (4, loopBody243_3, loopBody243_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody243_5 : HolLoopProg 64 :=
.mark loopBody243_4

def loopBody243_6 : HolLoopProg 64 :=
.seq loopBody243_5 loopBody243_1

def loopBody243_7 : HolLoopProg 64 :=
.mark loopBody243_6

def loopBody243_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody243_9 : HolLoopProg 64 :=
.mark loopBody243_8

def loopBody243_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody243_11 : HolLoopProg 64 :=
.mark loopBody243_10

def loopBody243_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody243_13 : HolLoopProg 64 :=
.mark loopBody243_12

def loopBody243_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody243_15 : HolLoopProg 64 :=
.mark loopBody243_14

def loopBody243_16 : HolLoopProg 64 :=
.call (some ([4, 5], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 306) ([6, 7, 8]) (some (6, loopBody243_15, loopBody243_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody243_17 : HolLoopProg 64 :=
.mark loopBody243_16

def loopBody243_18 : HolLoopProg 64 :=
.seq loopBody243_17 loopBody243_1

def loopBody243_19 : HolLoopProg 64 :=
.mark loopBody243_18

def loopBody243_20 : HolLoopProg 64 :=
.seq loopBody243_13 loopBody243_19

def loopBody243_21 : HolLoopProg 64 :=
.mark loopBody243_20

def loopBody243_22 : HolLoopProg 64 :=
.seq loopBody243_11 loopBody243_21

def loopBody243_23 : HolLoopProg 64 :=
.mark loopBody243_22

def loopBody243_24 : HolLoopProg 64 :=
.seq loopBody243_9 loopBody243_23

def loopBody243_25 : HolLoopProg 64 :=
.mark loopBody243_24

def loopBody243_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody243_27 : HolLoopProg 64 :=
.mark loopBody243_26

def loopBody243_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody243_29 : HolLoopProg 64 :=
.mark loopBody243_28

def loopBody243_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody243_31 : HolLoopProg 64 :=
.mark loopBody243_30

def loopBody243_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody243_33 : HolLoopProg 64 :=
.mark loopBody243_32

def loopBody243_34 : HolLoopProg 64 :=
.call (some ([6, 7, 8], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 302) ([9, 10, 11]) (some (9, loopBody243_33, loopBody243_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody243_35 : HolLoopProg 64 :=
.mark loopBody243_34

def loopBody243_36 : HolLoopProg 64 :=
.seq loopBody243_35 loopBody243_1

def loopBody243_37 : HolLoopProg 64 :=
.mark loopBody243_36

def loopBody243_38 : HolLoopProg 64 :=
.seq loopBody243_31 loopBody243_37

def loopBody243_39 : HolLoopProg 64 :=
.mark loopBody243_38

def loopBody243_40 : HolLoopProg 64 :=
.seq loopBody243_29 loopBody243_39

def loopBody243_41 : HolLoopProg 64 :=
.mark loopBody243_40

def loopBody243_42 : HolLoopProg 64 :=
.seq loopBody243_27 loopBody243_41

def loopBody243_43 : HolLoopProg 64 :=
.mark loopBody243_42

def loopBody243_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody243_45 : HolLoopProg 64 :=
.mark loopBody243_44

def loopBody243_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody243_47 : HolLoopProg 64 :=
.mark loopBody243_46

def loopBody243_48 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))) (some 70) ([10]) (some (10, loopBody243_47, loopBody243_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody243_49 : HolLoopProg 64 :=
.mark loopBody243_48

def loopBody243_50 : HolLoopProg 64 :=
.seq loopBody243_49 loopBody243_1

def loopBody243_51 : HolLoopProg 64 :=
.mark loopBody243_50

def loopBody243_52 : HolLoopProg 64 :=
.seq loopBody243_45 loopBody243_51

def loopBody243_53 : HolLoopProg 64 :=
.mark loopBody243_52

def loopBody243_54 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_53

def loopBody243_55 : HolLoopProg 64 :=
.mark loopBody243_54

def loopBody243_56 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_55

def loopBody243_57 : HolLoopProg 64 :=
.mark loopBody243_56

def loopBody243_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody243_59 : HolLoopProg 64 :=
.mark loopBody243_58

def loopBody243_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 7)

def loopBody243_61 : HolLoopProg 64 :=
.mark loopBody243_60

def loopBody243_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 8)

def loopBody243_63 : HolLoopProg 64 :=
.mark loopBody243_62

def loopBody243_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9, 10, 11]

def loopBody243_65 : HolLoopProg 64 :=
.mark loopBody243_64

def loopBody243_66 : HolLoopProg 64 :=
.seq loopBody243_65 loopBody243_1

def loopBody243_67 : HolLoopProg 64 :=
.mark loopBody243_66

def loopBody243_68 : HolLoopProg 64 :=
.seq loopBody243_63 loopBody243_67

def loopBody243_69 : HolLoopProg 64 :=
.mark loopBody243_68

def loopBody243_70 : HolLoopProg 64 :=
.seq loopBody243_61 loopBody243_69

def loopBody243_71 : HolLoopProg 64 :=
.mark loopBody243_70

def loopBody243_72 : HolLoopProg 64 :=
.seq loopBody243_59 loopBody243_71

def loopBody243_73 : HolLoopProg 64 :=
.mark loopBody243_72

def loopBody243_74 : HolLoopProg 64 :=
.seq loopBody243_57 loopBody243_73

def loopBody243_75 : HolLoopProg 64 :=
.mark loopBody243_74

def loopBody243_76 : HolLoopProg 64 :=
.seq loopBody243_43 loopBody243_75

def loopBody243_77 : HolLoopProg 64 :=
.mark loopBody243_76

def loopBody243_78 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_77

def loopBody243_79 : HolLoopProg 64 :=
.mark loopBody243_78

def loopBody243_80 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_79

def loopBody243_81 : HolLoopProg 64 :=
.mark loopBody243_80

def loopBody243_82 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_81

def loopBody243_83 : HolLoopProg 64 :=
.mark loopBody243_82

def loopBody243_84 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_83

def loopBody243_85 : HolLoopProg 64 :=
.mark loopBody243_84

def loopBody243_86 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_85

def loopBody243_87 : HolLoopProg 64 :=
.mark loopBody243_86

def loopBody243_88 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_87

def loopBody243_89 : HolLoopProg 64 :=
.mark loopBody243_88

def loopBody243_90 : HolLoopProg 64 :=
.seq loopBody243_25 loopBody243_89

def loopBody243_91 : HolLoopProg 64 :=
.mark loopBody243_90

def loopBody243_92 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_91

def loopBody243_93 : HolLoopProg 64 :=
.mark loopBody243_92

def loopBody243_94 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_93

def loopBody243_95 : HolLoopProg 64 :=
.mark loopBody243_94

def loopBody243_96 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_95

def loopBody243_97 : HolLoopProg 64 :=
.mark loopBody243_96

def loopBody243_98 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_97

def loopBody243_99 : HolLoopProg 64 :=
.mark loopBody243_98

def loopBody243_100 : HolLoopProg 64 :=
.seq loopBody243_7 loopBody243_99

def loopBody243_101 : HolLoopProg 64 :=
.mark loopBody243_100

def loopBody243_102 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_101

def loopBody243_103 : HolLoopProg 64 :=
.mark loopBody243_102

def loopBody243_104 : HolLoopProg 64 :=
.seq loopBody243_1 loopBody243_103

def loopBody243_105 : HolLoopProg 64 :=
.mark loopBody243_104

def output243 : Nat × List Nat × HolLoopProg 64 :=
  (307, [0, 1, 2], loopBody243_105)
end InitECandidate.Proofs.FrontendStages.Loop
