import InitECandidate.Proofs.FrontendStages.Loop.Translate273
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody289_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody289_1 : HolLoopProg 64 :=
.mark loopBody289_0

def loopBody289_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody289_3 : HolLoopProg 64 :=
.mark loopBody289_2

def loopBody289_4 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 69) ([]) (some (6, loopBody289_3, loopBody289_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody289_5 : HolLoopProg 64 :=
.mark loopBody289_4

def loopBody289_6 : HolLoopProg 64 :=
.seq loopBody289_5 loopBody289_1

def loopBody289_7 : HolLoopProg 64 :=
.mark loopBody289_6

def loopBody289_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 32#64)

def loopBody289_9 : HolLoopProg 64 :=
.mark loopBody289_8

def loopBody289_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody289_11 : HolLoopProg 64 :=
.mark loopBody289_10

def loopBody289_12 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([7]) (some (7, loopBody289_11, loopBody289_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody289_13 : HolLoopProg 64 :=
.mark loopBody289_12

def loopBody289_14 : HolLoopProg 64 :=
.seq loopBody289_13 loopBody289_1

def loopBody289_15 : HolLoopProg 64 :=
.mark loopBody289_14

def loopBody289_16 : HolLoopProg 64 :=
.seq loopBody289_9 loopBody289_15

def loopBody289_17 : HolLoopProg 64 :=
.mark loopBody289_16

def loopBody289_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody289_19 : HolLoopProg 64 :=
.mark loopBody289_18

def loopBody289_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody289_21 : HolLoopProg 64 :=
.mark loopBody289_20

def loopBody289_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody289_23 : HolLoopProg 64 :=
.mark loopBody289_22

def loopBody289_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 4)

def loopBody289_25 : HolLoopProg 64 :=
.mark loopBody289_24

def loopBody289_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 6)

def loopBody289_27 : HolLoopProg 64 :=
.mark loopBody289_26

def loopBody289_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody289_29 : HolLoopProg 64 :=
.mark loopBody289_28

def loopBody289_30 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 148) ([8, 9, 10, 11, 12]) (some (8, loopBody289_29, loopBody289_1, (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))

def loopBody289_31 : HolLoopProg 64 :=
.mark loopBody289_30

def loopBody289_32 : HolLoopProg 64 :=
.seq loopBody289_31 loopBody289_1

def loopBody289_33 : HolLoopProg 64 :=
.mark loopBody289_32

def loopBody289_34 : HolLoopProg 64 :=
.seq loopBody289_27 loopBody289_33

def loopBody289_35 : HolLoopProg 64 :=
.mark loopBody289_34

def loopBody289_36 : HolLoopProg 64 :=
.seq loopBody289_25 loopBody289_35

def loopBody289_37 : HolLoopProg 64 :=
.mark loopBody289_36

def loopBody289_38 : HolLoopProg 64 :=
.seq loopBody289_23 loopBody289_37

def loopBody289_39 : HolLoopProg 64 :=
.mark loopBody289_38

def loopBody289_40 : HolLoopProg 64 :=
.seq loopBody289_21 loopBody289_39

def loopBody289_41 : HolLoopProg 64 :=
.mark loopBody289_40

def loopBody289_42 : HolLoopProg 64 :=
.seq loopBody289_19 loopBody289_41

def loopBody289_43 : HolLoopProg 64 :=
.mark loopBody289_42

def loopBody289_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 0)

def loopBody289_45 : HolLoopProg 64 :=
.mark loopBody289_44

def loopBody289_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 6)

def loopBody289_47 : HolLoopProg 64 :=
.mark loopBody289_46

def loopBody289_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 7)

def loopBody289_49 : HolLoopProg 64 :=
.mark loopBody289_48

def loopBody289_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody289_51 : HolLoopProg 64 :=
.mark loopBody289_50

def loopBody289_52 : HolLoopProg 64 :=
.call (some ([8], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 176) ([9, 10, 11]) (some (9, loopBody289_51, loopBody289_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody289_53 : HolLoopProg 64 :=
.mark loopBody289_52

def loopBody289_54 : HolLoopProg 64 :=
.seq loopBody289_53 loopBody289_1

def loopBody289_55 : HolLoopProg 64 :=
.mark loopBody289_54

def loopBody289_56 : HolLoopProg 64 :=
.seq loopBody289_49 loopBody289_55

def loopBody289_57 : HolLoopProg 64 :=
.mark loopBody289_56

def loopBody289_58 : HolLoopProg 64 :=
.seq loopBody289_47 loopBody289_57

def loopBody289_59 : HolLoopProg 64 :=
.mark loopBody289_58

def loopBody289_60 : HolLoopProg 64 :=
.seq loopBody289_45 loopBody289_59

def loopBody289_61 : HolLoopProg 64 :=
.mark loopBody289_60

def loopBody289_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody289_63 : HolLoopProg 64 :=
.mark loopBody289_62

def loopBody289_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody289_65 : HolLoopProg 64 :=
.mark loopBody289_64

def loopBody289_66 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)) (some 70) ([10]) (some (10, loopBody289_65, loopBody289_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  Flapjack.Spt.ln)))

def loopBody289_67 : HolLoopProg 64 :=
.mark loopBody289_66

def loopBody289_68 : HolLoopProg 64 :=
.seq loopBody289_67 loopBody289_1

def loopBody289_69 : HolLoopProg 64 :=
.mark loopBody289_68

def loopBody289_70 : HolLoopProg 64 :=
.seq loopBody289_63 loopBody289_69

def loopBody289_71 : HolLoopProg 64 :=
.mark loopBody289_70

def loopBody289_72 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_71

def loopBody289_73 : HolLoopProg 64 :=
.mark loopBody289_72

def loopBody289_74 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_73

def loopBody289_75 : HolLoopProg 64 :=
.mark loopBody289_74

def loopBody289_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 8)

def loopBody289_77 : HolLoopProg 64 :=
.mark loopBody289_76

def loopBody289_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9]

def loopBody289_79 : HolLoopProg 64 :=
.mark loopBody289_78

def loopBody289_80 : HolLoopProg 64 :=
.seq loopBody289_79 loopBody289_1

def loopBody289_81 : HolLoopProg 64 :=
.mark loopBody289_80

def loopBody289_82 : HolLoopProg 64 :=
.seq loopBody289_77 loopBody289_81

def loopBody289_83 : HolLoopProg 64 :=
.mark loopBody289_82

def loopBody289_84 : HolLoopProg 64 :=
.seq loopBody289_75 loopBody289_83

def loopBody289_85 : HolLoopProg 64 :=
.mark loopBody289_84

def loopBody289_86 : HolLoopProg 64 :=
.seq loopBody289_61 loopBody289_85

def loopBody289_87 : HolLoopProg 64 :=
.mark loopBody289_86

def loopBody289_88 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_87

def loopBody289_89 : HolLoopProg 64 :=
.mark loopBody289_88

def loopBody289_90 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_89

def loopBody289_91 : HolLoopProg 64 :=
.mark loopBody289_90

def loopBody289_92 : HolLoopProg 64 :=
.seq loopBody289_43 loopBody289_91

def loopBody289_93 : HolLoopProg 64 :=
.mark loopBody289_92

def loopBody289_94 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_93

def loopBody289_95 : HolLoopProg 64 :=
.mark loopBody289_94

def loopBody289_96 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_95

def loopBody289_97 : HolLoopProg 64 :=
.mark loopBody289_96

def loopBody289_98 : HolLoopProg 64 :=
.seq loopBody289_17 loopBody289_97

def loopBody289_99 : HolLoopProg 64 :=
.mark loopBody289_98

def loopBody289_100 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_99

def loopBody289_101 : HolLoopProg 64 :=
.mark loopBody289_100

def loopBody289_102 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_101

def loopBody289_103 : HolLoopProg 64 :=
.mark loopBody289_102

def loopBody289_104 : HolLoopProg 64 :=
.seq loopBody289_7 loopBody289_103

def loopBody289_105 : HolLoopProg 64 :=
.mark loopBody289_104

def loopBody289_106 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_105

def loopBody289_107 : HolLoopProg 64 :=
.mark loopBody289_106

def loopBody289_108 : HolLoopProg 64 :=
.seq loopBody289_1 loopBody289_107

def loopBody289_109 : HolLoopProg 64 :=
.mark loopBody289_108

def output289 : Nat × List Nat × HolLoopProg 64 :=
  (353, [0, 1, 2, 3, 4], loopBody289_109)
end InitECandidate.Proofs.FrontendStages.Loop
