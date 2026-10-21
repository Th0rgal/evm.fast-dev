import InitECandidate.Proofs.FrontendStages.Loop.Translate438
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody454_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody454_1 : HolLoopProg 64 :=
.mark loopBody454_0

def loopBody454_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody454_3 : HolLoopProg 64 :=
.mark loopBody454_2

def loopBody454_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody454_3, loopBody454_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody454_5 : HolLoopProg 64 :=
.mark loopBody454_4

def loopBody454_6 : HolLoopProg 64 :=
.seq loopBody454_5 loopBody454_1

def loopBody454_7 : HolLoopProg 64 :=
.mark loopBody454_6

def loopBody454_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 5#64)

def loopBody454_9 : HolLoopProg 64 :=
.mark loopBody454_8

def loopBody454_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody454_11 : HolLoopProg 64 :=
.mark loopBody454_10

def loopBody454_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 466) ([6]) (some (6, loopBody454_11, loopBody454_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody454_13 : HolLoopProg 64 :=
.mark loopBody454_12

def loopBody454_14 : HolLoopProg 64 :=
.seq loopBody454_13 loopBody454_1

def loopBody454_15 : HolLoopProg 64 :=
.mark loopBody454_14

def loopBody454_16 : HolLoopProg 64 :=
.seq loopBody454_9 loopBody454_15

def loopBody454_17 : HolLoopProg 64 :=
.mark loopBody454_16

def loopBody454_18 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_17

def loopBody454_19 : HolLoopProg 64 :=
.mark loopBody454_18

def loopBody454_20 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_19

def loopBody454_21 : HolLoopProg 64 :=
.mark loopBody454_20

def loopBody454_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody454_23 : HolLoopProg 64 :=
.mark loopBody454_22

def loopBody454_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody454_25 : HolLoopProg 64 :=
.mark loopBody454_24

def loopBody454_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody454_27 : HolLoopProg 64 :=
.mark loopBody454_26

def loopBody454_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody454_29 : HolLoopProg 64 :=
.mark loopBody454_28

def loopBody454_30 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 138) ([6, 7, 8, 9]) (some (6, loopBody454_11, loopBody454_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody454_31 : HolLoopProg 64 :=
.mark loopBody454_30

def loopBody454_32 : HolLoopProg 64 :=
.seq loopBody454_31 loopBody454_1

def loopBody454_33 : HolLoopProg 64 :=
.mark loopBody454_32

def loopBody454_34 : HolLoopProg 64 :=
.seq loopBody454_29 loopBody454_33

def loopBody454_35 : HolLoopProg 64 :=
.mark loopBody454_34

def loopBody454_36 : HolLoopProg 64 :=
.seq loopBody454_27 loopBody454_35

def loopBody454_37 : HolLoopProg 64 :=
.mark loopBody454_36

def loopBody454_38 : HolLoopProg 64 :=
.seq loopBody454_25 loopBody454_37

def loopBody454_39 : HolLoopProg 64 :=
.mark loopBody454_38

def loopBody454_40 : HolLoopProg 64 :=
.seq loopBody454_23 loopBody454_39

def loopBody454_41 : HolLoopProg 64 :=
.mark loopBody454_40

def loopBody454_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 256#64, Flapjack.HolLoopExp.var 5])

def loopBody454_43 : HolLoopProg 64 :=
.mark loopBody454_42

def loopBody454_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody454_45 : HolLoopProg 64 :=
.mark loopBody454_44

def loopBody454_46 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 473) ([7]) (some (7, loopBody454_45, loopBody454_1, (Flapjack.Spt.ln)))

def loopBody454_47 : HolLoopProg 64 :=
.mark loopBody454_46

def loopBody454_48 : HolLoopProg 64 :=
.seq loopBody454_47 loopBody454_1

def loopBody454_49 : HolLoopProg 64 :=
.mark loopBody454_48

def loopBody454_50 : HolLoopProg 64 :=
.seq loopBody454_43 loopBody454_49

def loopBody454_51 : HolLoopProg 64 :=
.mark loopBody454_50

def loopBody454_52 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_51

def loopBody454_53 : HolLoopProg 64 :=
.mark loopBody454_52

def loopBody454_54 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_53

def loopBody454_55 : HolLoopProg 64 :=
.mark loopBody454_54

def loopBody454_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody454_57 : HolLoopProg 64 :=
.mark loopBody454_56

def loopBody454_58 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 486) ([7]) (some (7, loopBody454_45, loopBody454_1, (Flapjack.Spt.ln)))

def loopBody454_59 : HolLoopProg 64 :=
.mark loopBody454_58

def loopBody454_60 : HolLoopProg 64 :=
.seq loopBody454_59 loopBody454_1

def loopBody454_61 : HolLoopProg 64 :=
.mark loopBody454_60

def loopBody454_62 : HolLoopProg 64 :=
.seq loopBody454_57 loopBody454_61

def loopBody454_63 : HolLoopProg 64 :=
.mark loopBody454_62

def loopBody454_64 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_63

def loopBody454_65 : HolLoopProg 64 :=
.mark loopBody454_64

def loopBody454_66 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_65

def loopBody454_67 : HolLoopProg 64 :=
.mark loopBody454_66

def loopBody454_68 : HolLoopProg 64 :=
.seq loopBody454_55 loopBody454_67

def loopBody454_69 : HolLoopProg 64 :=
.mark loopBody454_68

def loopBody454_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody454_71 : HolLoopProg 64 :=
.mark loopBody454_70

def loopBody454_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody454_73 : HolLoopProg 64 :=
.mark loopBody454_72

def loopBody454_74 : HolLoopProg 64 :=
.seq loopBody454_73 loopBody454_1

def loopBody454_75 : HolLoopProg 64 :=
.mark loopBody454_74

def loopBody454_76 : HolLoopProg 64 :=
.seq loopBody454_71 loopBody454_75

def loopBody454_77 : HolLoopProg 64 :=
.mark loopBody454_76

def loopBody454_78 : HolLoopProg 64 :=
.seq loopBody454_69 loopBody454_77

def loopBody454_79 : HolLoopProg 64 :=
.mark loopBody454_78

def loopBody454_80 : HolLoopProg 64 :=
.seq loopBody454_41 loopBody454_79

def loopBody454_81 : HolLoopProg 64 :=
.mark loopBody454_80

def loopBody454_82 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_81

def loopBody454_83 : HolLoopProg 64 :=
.mark loopBody454_82

def loopBody454_84 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_83

def loopBody454_85 : HolLoopProg 64 :=
.mark loopBody454_84

def loopBody454_86 : HolLoopProg 64 :=
.seq loopBody454_21 loopBody454_85

def loopBody454_87 : HolLoopProg 64 :=
.mark loopBody454_86

def loopBody454_88 : HolLoopProg 64 :=
.seq loopBody454_7 loopBody454_87

def loopBody454_89 : HolLoopProg 64 :=
.mark loopBody454_88

def loopBody454_90 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_89

def loopBody454_91 : HolLoopProg 64 :=
.mark loopBody454_90

def loopBody454_92 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_91

def loopBody454_93 : HolLoopProg 64 :=
.mark loopBody454_92

def loopBody454_94 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_93

def loopBody454_95 : HolLoopProg 64 :=
.mark loopBody454_94

def loopBody454_96 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_95

def loopBody454_97 : HolLoopProg 64 :=
.mark loopBody454_96

def loopBody454_98 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_97

def loopBody454_99 : HolLoopProg 64 :=
.mark loopBody454_98

def loopBody454_100 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_99

def loopBody454_101 : HolLoopProg 64 :=
.mark loopBody454_100

def loopBody454_102 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_101

def loopBody454_103 : HolLoopProg 64 :=
.mark loopBody454_102

def loopBody454_104 : HolLoopProg 64 :=
.seq loopBody454_1 loopBody454_103

def loopBody454_105 : HolLoopProg 64 :=
.mark loopBody454_104

def output454 : Nat × List Nat × HolLoopProg 64 :=
  (518, [], loopBody454_105)
end InitECandidate.Proofs.FrontendStages.Loop
