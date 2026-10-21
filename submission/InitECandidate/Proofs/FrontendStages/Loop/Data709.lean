import InitECandidate.Proofs.FrontendStages.Loop.Translate693
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody709_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody709_1 : HolLoopProg 64 :=
.mark loopBody709_0

def loopBody709_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody709_3 : HolLoopProg 64 :=
.mark loopBody709_2

def loopBody709_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 69) ([]) (some (2, loopBody709_3, loopBody709_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody709_5 : HolLoopProg 64 :=
.mark loopBody709_4

def loopBody709_6 : HolLoopProg 64 :=
.seq loopBody709_5 loopBody709_1

def loopBody709_7 : HolLoopProg 64 :=
.mark loopBody709_6

def loopBody709_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 144#64)

def loopBody709_9 : HolLoopProg 64 :=
.mark loopBody709_8

def loopBody709_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody709_11 : HolLoopProg 64 :=
.mark loopBody709_10

def loopBody709_12 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([3]) (some (3, loopBody709_11, loopBody709_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody709_13 : HolLoopProg 64 :=
.mark loopBody709_12

def loopBody709_14 : HolLoopProg 64 :=
.seq loopBody709_13 loopBody709_1

def loopBody709_15 : HolLoopProg 64 :=
.mark loopBody709_14

def loopBody709_16 : HolLoopProg 64 :=
.seq loopBody709_9 loopBody709_15

def loopBody709_17 : HolLoopProg 64 :=
.mark loopBody709_16

def loopBody709_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody709_19 : HolLoopProg 64 :=
.mark loopBody709_18

def loopBody709_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody709_21 : HolLoopProg 64 :=
.mark loopBody709_20

def loopBody709_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 1344#64])

def loopBody709_23 : HolLoopProg 64 :=
.mark loopBody709_22

def loopBody709_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 4#64)

def loopBody709_25 : HolLoopProg 64 :=
.mark loopBody709_24

def loopBody709_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody709_27 : HolLoopProg 64 :=
.mark loopBody709_26

def loopBody709_28 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 768) ([4, 5, 6, 7]) (some (4, loopBody709_27, loopBody709_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody709_29 : HolLoopProg 64 :=
.mark loopBody709_28

def loopBody709_30 : HolLoopProg 64 :=
.seq loopBody709_29 loopBody709_1

def loopBody709_31 : HolLoopProg 64 :=
.mark loopBody709_30

def loopBody709_32 : HolLoopProg 64 :=
.seq loopBody709_25 loopBody709_31

def loopBody709_33 : HolLoopProg 64 :=
.mark loopBody709_32

def loopBody709_34 : HolLoopProg 64 :=
.seq loopBody709_23 loopBody709_33

def loopBody709_35 : HolLoopProg 64 :=
.mark loopBody709_34

def loopBody709_36 : HolLoopProg 64 :=
.seq loopBody709_21 loopBody709_35

def loopBody709_37 : HolLoopProg 64 :=
.mark loopBody709_36

def loopBody709_38 : HolLoopProg 64 :=
.seq loopBody709_19 loopBody709_37

def loopBody709_39 : HolLoopProg 64 :=
.mark loopBody709_38

def loopBody709_40 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_39

def loopBody709_41 : HolLoopProg 64 :=
.mark loopBody709_40

def loopBody709_42 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_41

def loopBody709_43 : HolLoopProg 64 :=
.mark loopBody709_42

def loopBody709_44 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 763) ([4]) (some (4, loopBody709_27, loopBody709_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody709_45 : HolLoopProg 64 :=
.mark loopBody709_44

def loopBody709_46 : HolLoopProg 64 :=
.seq loopBody709_45 loopBody709_1

def loopBody709_47 : HolLoopProg 64 :=
.mark loopBody709_46

def loopBody709_48 : HolLoopProg 64 :=
.seq loopBody709_19 loopBody709_47

def loopBody709_49 : HolLoopProg 64 :=
.mark loopBody709_48

def loopBody709_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody709_51 : HolLoopProg 64 :=
.mark loopBody709_50

def loopBody709_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody709_53 : HolLoopProg 64 :=
.mark loopBody709_52

def loopBody709_54 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 70) ([5]) (some (5, loopBody709_53, loopBody709_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody709_55 : HolLoopProg 64 :=
.mark loopBody709_54

def loopBody709_56 : HolLoopProg 64 :=
.seq loopBody709_55 loopBody709_1

def loopBody709_57 : HolLoopProg 64 :=
.mark loopBody709_56

def loopBody709_58 : HolLoopProg 64 :=
.seq loopBody709_51 loopBody709_57

def loopBody709_59 : HolLoopProg 64 :=
.mark loopBody709_58

def loopBody709_60 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_59

def loopBody709_61 : HolLoopProg 64 :=
.mark loopBody709_60

def loopBody709_62 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_61

def loopBody709_63 : HolLoopProg 64 :=
.mark loopBody709_62

def loopBody709_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody709_65 : HolLoopProg 64 :=
.mark loopBody709_64

def loopBody709_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody709_67 : HolLoopProg 64 :=
.mark loopBody709_66

def loopBody709_68 : HolLoopProg 64 :=
.seq loopBody709_67 loopBody709_1

def loopBody709_69 : HolLoopProg 64 :=
.mark loopBody709_68

def loopBody709_70 : HolLoopProg 64 :=
.seq loopBody709_65 loopBody709_69

def loopBody709_71 : HolLoopProg 64 :=
.mark loopBody709_70

def loopBody709_72 : HolLoopProg 64 :=
.seq loopBody709_63 loopBody709_71

def loopBody709_73 : HolLoopProg 64 :=
.mark loopBody709_72

def loopBody709_74 : HolLoopProg 64 :=
.seq loopBody709_49 loopBody709_73

def loopBody709_75 : HolLoopProg 64 :=
.mark loopBody709_74

def loopBody709_76 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_75

def loopBody709_77 : HolLoopProg 64 :=
.mark loopBody709_76

def loopBody709_78 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_77

def loopBody709_79 : HolLoopProg 64 :=
.mark loopBody709_78

def loopBody709_80 : HolLoopProg 64 :=
.seq loopBody709_43 loopBody709_79

def loopBody709_81 : HolLoopProg 64 :=
.mark loopBody709_80

def loopBody709_82 : HolLoopProg 64 :=
.seq loopBody709_17 loopBody709_81

def loopBody709_83 : HolLoopProg 64 :=
.mark loopBody709_82

def loopBody709_84 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_83

def loopBody709_85 : HolLoopProg 64 :=
.mark loopBody709_84

def loopBody709_86 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_85

def loopBody709_87 : HolLoopProg 64 :=
.mark loopBody709_86

def loopBody709_88 : HolLoopProg 64 :=
.seq loopBody709_7 loopBody709_87

def loopBody709_89 : HolLoopProg 64 :=
.mark loopBody709_88

def loopBody709_90 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_89

def loopBody709_91 : HolLoopProg 64 :=
.mark loopBody709_90

def loopBody709_92 : HolLoopProg 64 :=
.seq loopBody709_1 loopBody709_91

def loopBody709_93 : HolLoopProg 64 :=
.mark loopBody709_92

def output709 : Nat × List Nat × HolLoopProg 64 :=
  (773, [0], loopBody709_93)
end InitECandidate.Proofs.FrontendStages.Loop
