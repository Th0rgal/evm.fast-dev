import InitECandidate.Proofs.FrontendStages.Loop.Translate286
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody302_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody302_1 : HolLoopProg 64 :=
.mark loopBody302_0

def loopBody302_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody302_3 : HolLoopProg 64 :=
.mark loopBody302_2

def loopBody302_4 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 69) ([]) (some (5, loopBody302_3, loopBody302_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody302_5 : HolLoopProg 64 :=
.mark loopBody302_4

def loopBody302_6 : HolLoopProg 64 :=
.seq loopBody302_5 loopBody302_1

def loopBody302_7 : HolLoopProg 64 :=
.mark loopBody302_6

def loopBody302_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody302_9 : HolLoopProg 64 :=
.mark loopBody302_8

def loopBody302_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody302_11 : HolLoopProg 64 :=
.mark loopBody302_10

def loopBody302_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody302_13 : HolLoopProg 64 :=
.mark loopBody302_12

def loopBody302_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody302_15 : HolLoopProg 64 :=
.mark loopBody302_14

def loopBody302_16 : HolLoopProg 64 :=
.call (some
  ([5, 6],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 363) ([7, 8, 9]) (some (7, loopBody302_15, loopBody302_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody302_17 : HolLoopProg 64 :=
.mark loopBody302_16

def loopBody302_18 : HolLoopProg 64 :=
.seq loopBody302_17 loopBody302_1

def loopBody302_19 : HolLoopProg 64 :=
.mark loopBody302_18

def loopBody302_20 : HolLoopProg 64 :=
.seq loopBody302_13 loopBody302_19

def loopBody302_21 : HolLoopProg 64 :=
.mark loopBody302_20

def loopBody302_22 : HolLoopProg 64 :=
.seq loopBody302_11 loopBody302_21

def loopBody302_23 : HolLoopProg 64 :=
.mark loopBody302_22

def loopBody302_24 : HolLoopProg 64 :=
.seq loopBody302_9 loopBody302_23

def loopBody302_25 : HolLoopProg 64 :=
.mark loopBody302_24

def loopBody302_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody302_27 : HolLoopProg 64 :=
.mark loopBody302_26

def loopBody302_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody302_29 : HolLoopProg 64 :=
.mark loopBody302_28

def loopBody302_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody302_31 : HolLoopProg 64 :=
.mark loopBody302_30

def loopBody302_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody302_33 : HolLoopProg 64 :=
.mark loopBody302_32

def loopBody302_34 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 158) ([8, 9, 10]) (some (8, loopBody302_33, loopBody302_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody302_35 : HolLoopProg 64 :=
.mark loopBody302_34

def loopBody302_36 : HolLoopProg 64 :=
.seq loopBody302_35 loopBody302_1

def loopBody302_37 : HolLoopProg 64 :=
.mark loopBody302_36

def loopBody302_38 : HolLoopProg 64 :=
.seq loopBody302_31 loopBody302_37

def loopBody302_39 : HolLoopProg 64 :=
.mark loopBody302_38

def loopBody302_40 : HolLoopProg 64 :=
.seq loopBody302_29 loopBody302_39

def loopBody302_41 : HolLoopProg 64 :=
.mark loopBody302_40

def loopBody302_42 : HolLoopProg 64 :=
.seq loopBody302_27 loopBody302_41

def loopBody302_43 : HolLoopProg 64 :=
.mark loopBody302_42

def loopBody302_44 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_43

def loopBody302_45 : HolLoopProg 64 :=
.mark loopBody302_44

def loopBody302_46 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_45

def loopBody302_47 : HolLoopProg 64 :=
.mark loopBody302_46

def loopBody302_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody302_49 : HolLoopProg 64 :=
.mark loopBody302_48

def loopBody302_50 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.ln)) (some 70) ([8]) (some (8, loopBody302_33, loopBody302_1, (Flapjack.Spt.ln)))

def loopBody302_51 : HolLoopProg 64 :=
.mark loopBody302_50

def loopBody302_52 : HolLoopProg 64 :=
.seq loopBody302_51 loopBody302_1

def loopBody302_53 : HolLoopProg 64 :=
.mark loopBody302_52

def loopBody302_54 : HolLoopProg 64 :=
.seq loopBody302_49 loopBody302_53

def loopBody302_55 : HolLoopProg 64 :=
.mark loopBody302_54

def loopBody302_56 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_55

def loopBody302_57 : HolLoopProg 64 :=
.mark loopBody302_56

def loopBody302_58 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_57

def loopBody302_59 : HolLoopProg 64 :=
.mark loopBody302_58

def loopBody302_60 : HolLoopProg 64 :=
.seq loopBody302_47 loopBody302_59

def loopBody302_61 : HolLoopProg 64 :=
.mark loopBody302_60

def loopBody302_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody302_63 : HolLoopProg 64 :=
.mark loopBody302_62

def loopBody302_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody302_65 : HolLoopProg 64 :=
.mark loopBody302_64

def loopBody302_66 : HolLoopProg 64 :=
.seq loopBody302_65 loopBody302_1

def loopBody302_67 : HolLoopProg 64 :=
.mark loopBody302_66

def loopBody302_68 : HolLoopProg 64 :=
.seq loopBody302_63 loopBody302_67

def loopBody302_69 : HolLoopProg 64 :=
.mark loopBody302_68

def loopBody302_70 : HolLoopProg 64 :=
.seq loopBody302_61 loopBody302_69

def loopBody302_71 : HolLoopProg 64 :=
.mark loopBody302_70

def loopBody302_72 : HolLoopProg 64 :=
.seq loopBody302_25 loopBody302_71

def loopBody302_73 : HolLoopProg 64 :=
.mark loopBody302_72

def loopBody302_74 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_73

def loopBody302_75 : HolLoopProg 64 :=
.mark loopBody302_74

def loopBody302_76 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_75

def loopBody302_77 : HolLoopProg 64 :=
.mark loopBody302_76

def loopBody302_78 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_77

def loopBody302_79 : HolLoopProg 64 :=
.mark loopBody302_78

def loopBody302_80 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_79

def loopBody302_81 : HolLoopProg 64 :=
.mark loopBody302_80

def loopBody302_82 : HolLoopProg 64 :=
.seq loopBody302_7 loopBody302_81

def loopBody302_83 : HolLoopProg 64 :=
.mark loopBody302_82

def loopBody302_84 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_83

def loopBody302_85 : HolLoopProg 64 :=
.mark loopBody302_84

def loopBody302_86 : HolLoopProg 64 :=
.seq loopBody302_1 loopBody302_85

def loopBody302_87 : HolLoopProg 64 :=
.mark loopBody302_86

def output302 : Nat × List Nat × HolLoopProg 64 :=
  (366, [0, 1, 2, 3], loopBody302_87)
end InitECandidate.Proofs.FrontendStages.Loop
