import InitECandidate.Proofs.FrontendStages.Loop.Translate429
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody445_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody445_1 : HolLoopProg 64 :=
.mark loopBody445_0

def loopBody445_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody445_3 : HolLoopProg 64 :=
.mark loopBody445_2

def loopBody445_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody445_3, loopBody445_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody445_5 : HolLoopProg 64 :=
.mark loopBody445_4

def loopBody445_6 : HolLoopProg 64 :=
.seq loopBody445_5 loopBody445_1

def loopBody445_7 : HolLoopProg 64 :=
.mark loopBody445_6

def loopBody445_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 3#64)

def loopBody445_9 : HolLoopProg 64 :=
.mark loopBody445_8

def loopBody445_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody445_11 : HolLoopProg 64 :=
.mark loopBody445_10

def loopBody445_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 466) ([6]) (some (6, loopBody445_11, loopBody445_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody445_13 : HolLoopProg 64 :=
.mark loopBody445_12

def loopBody445_14 : HolLoopProg 64 :=
.seq loopBody445_13 loopBody445_1

def loopBody445_15 : HolLoopProg 64 :=
.mark loopBody445_14

def loopBody445_16 : HolLoopProg 64 :=
.seq loopBody445_9 loopBody445_15

def loopBody445_17 : HolLoopProg 64 :=
.mark loopBody445_16

def loopBody445_18 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_17

def loopBody445_19 : HolLoopProg 64 :=
.mark loopBody445_18

def loopBody445_20 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_19

def loopBody445_21 : HolLoopProg 64 :=
.mark loopBody445_20

def loopBody445_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody445_23 : HolLoopProg 64 :=
.mark loopBody445_22

def loopBody445_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody445_25 : HolLoopProg 64 :=
.mark loopBody445_24

def loopBody445_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody445_27 : HolLoopProg 64 :=
.mark loopBody445_26

def loopBody445_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody445_29 : HolLoopProg 64 :=
.mark loopBody445_28

def loopBody445_30 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 102) ([6, 7, 8, 9]) (some (6, loopBody445_11, loopBody445_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody445_31 : HolLoopProg 64 :=
.mark loopBody445_30

def loopBody445_32 : HolLoopProg 64 :=
.seq loopBody445_31 loopBody445_1

def loopBody445_33 : HolLoopProg 64 :=
.mark loopBody445_32

def loopBody445_34 : HolLoopProg 64 :=
.seq loopBody445_29 loopBody445_33

def loopBody445_35 : HolLoopProg 64 :=
.mark loopBody445_34

def loopBody445_36 : HolLoopProg 64 :=
.seq loopBody445_27 loopBody445_35

def loopBody445_37 : HolLoopProg 64 :=
.mark loopBody445_36

def loopBody445_38 : HolLoopProg 64 :=
.seq loopBody445_25 loopBody445_37

def loopBody445_39 : HolLoopProg 64 :=
.mark loopBody445_38

def loopBody445_40 : HolLoopProg 64 :=
.seq loopBody445_23 loopBody445_39

def loopBody445_41 : HolLoopProg 64 :=
.mark loopBody445_40

def loopBody445_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody445_43 : HolLoopProg 64 :=
.mark loopBody445_42

def loopBody445_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody445_45 : HolLoopProg 64 :=
.mark loopBody445_44

def loopBody445_46 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 474) ([7]) (some (7, loopBody445_45, loopBody445_1, (Flapjack.Spt.ln)))

def loopBody445_47 : HolLoopProg 64 :=
.mark loopBody445_46

def loopBody445_48 : HolLoopProg 64 :=
.seq loopBody445_47 loopBody445_1

def loopBody445_49 : HolLoopProg 64 :=
.mark loopBody445_48

def loopBody445_50 : HolLoopProg 64 :=
.seq loopBody445_43 loopBody445_49

def loopBody445_51 : HolLoopProg 64 :=
.mark loopBody445_50

def loopBody445_52 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_51

def loopBody445_53 : HolLoopProg 64 :=
.mark loopBody445_52

def loopBody445_54 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_53

def loopBody445_55 : HolLoopProg 64 :=
.mark loopBody445_54

def loopBody445_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody445_57 : HolLoopProg 64 :=
.mark loopBody445_56

def loopBody445_58 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 486) ([7]) (some (7, loopBody445_45, loopBody445_1, (Flapjack.Spt.ln)))

def loopBody445_59 : HolLoopProg 64 :=
.mark loopBody445_58

def loopBody445_60 : HolLoopProg 64 :=
.seq loopBody445_59 loopBody445_1

def loopBody445_61 : HolLoopProg 64 :=
.mark loopBody445_60

def loopBody445_62 : HolLoopProg 64 :=
.seq loopBody445_57 loopBody445_61

def loopBody445_63 : HolLoopProg 64 :=
.mark loopBody445_62

def loopBody445_64 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_63

def loopBody445_65 : HolLoopProg 64 :=
.mark loopBody445_64

def loopBody445_66 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_65

def loopBody445_67 : HolLoopProg 64 :=
.mark loopBody445_66

def loopBody445_68 : HolLoopProg 64 :=
.seq loopBody445_55 loopBody445_67

def loopBody445_69 : HolLoopProg 64 :=
.mark loopBody445_68

def loopBody445_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody445_71 : HolLoopProg 64 :=
.mark loopBody445_70

def loopBody445_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody445_73 : HolLoopProg 64 :=
.mark loopBody445_72

def loopBody445_74 : HolLoopProg 64 :=
.seq loopBody445_73 loopBody445_1

def loopBody445_75 : HolLoopProg 64 :=
.mark loopBody445_74

def loopBody445_76 : HolLoopProg 64 :=
.seq loopBody445_71 loopBody445_75

def loopBody445_77 : HolLoopProg 64 :=
.mark loopBody445_76

def loopBody445_78 : HolLoopProg 64 :=
.seq loopBody445_69 loopBody445_77

def loopBody445_79 : HolLoopProg 64 :=
.mark loopBody445_78

def loopBody445_80 : HolLoopProg 64 :=
.seq loopBody445_41 loopBody445_79

def loopBody445_81 : HolLoopProg 64 :=
.mark loopBody445_80

def loopBody445_82 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_81

def loopBody445_83 : HolLoopProg 64 :=
.mark loopBody445_82

def loopBody445_84 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_83

def loopBody445_85 : HolLoopProg 64 :=
.mark loopBody445_84

def loopBody445_86 : HolLoopProg 64 :=
.seq loopBody445_21 loopBody445_85

def loopBody445_87 : HolLoopProg 64 :=
.mark loopBody445_86

def loopBody445_88 : HolLoopProg 64 :=
.seq loopBody445_7 loopBody445_87

def loopBody445_89 : HolLoopProg 64 :=
.mark loopBody445_88

def loopBody445_90 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_89

def loopBody445_91 : HolLoopProg 64 :=
.mark loopBody445_90

def loopBody445_92 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_91

def loopBody445_93 : HolLoopProg 64 :=
.mark loopBody445_92

def loopBody445_94 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_93

def loopBody445_95 : HolLoopProg 64 :=
.mark loopBody445_94

def loopBody445_96 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_95

def loopBody445_97 : HolLoopProg 64 :=
.mark loopBody445_96

def loopBody445_98 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_97

def loopBody445_99 : HolLoopProg 64 :=
.mark loopBody445_98

def loopBody445_100 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_99

def loopBody445_101 : HolLoopProg 64 :=
.mark loopBody445_100

def loopBody445_102 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_101

def loopBody445_103 : HolLoopProg 64 :=
.mark loopBody445_102

def loopBody445_104 : HolLoopProg 64 :=
.seq loopBody445_1 loopBody445_103

def loopBody445_105 : HolLoopProg 64 :=
.mark loopBody445_104

def output445 : Nat × List Nat × HolLoopProg 64 :=
  (509, [], loopBody445_105)
end InitECandidate.Proofs.FrontendStages.Loop
