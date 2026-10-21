import InitECandidate.Proofs.FrontendStages.Loop.Translate705
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody721_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody721_1 : HolLoopProg 64 :=
.mark loopBody721_0

def loopBody721_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody721_3 : HolLoopProg 64 :=
.mark loopBody721_2

def loopBody721_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 69) ([]) (some (2, loopBody721_3, loopBody721_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody721_5 : HolLoopProg 64 :=
.mark loopBody721_4

def loopBody721_6 : HolLoopProg 64 :=
.seq loopBody721_5 loopBody721_1

def loopBody721_7 : HolLoopProg 64 :=
.mark loopBody721_6

def loopBody721_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 288#64)

def loopBody721_9 : HolLoopProg 64 :=
.mark loopBody721_8

def loopBody721_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody721_11 : HolLoopProg 64 :=
.mark loopBody721_10

def loopBody721_12 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([3]) (some (3, loopBody721_11, loopBody721_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody721_13 : HolLoopProg 64 :=
.mark loopBody721_12

def loopBody721_14 : HolLoopProg 64 :=
.seq loopBody721_13 loopBody721_1

def loopBody721_15 : HolLoopProg 64 :=
.mark loopBody721_14

def loopBody721_16 : HolLoopProg 64 :=
.seq loopBody721_9 loopBody721_15

def loopBody721_17 : HolLoopProg 64 :=
.mark loopBody721_16

def loopBody721_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody721_19 : HolLoopProg 64 :=
.mark loopBody721_18

def loopBody721_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody721_21 : HolLoopProg 64 :=
.mark loopBody721_20

def loopBody721_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 392#64]),
      Flapjack.HolLoopExp.const 1344#64])

def loopBody721_23 : HolLoopProg 64 :=
.mark loopBody721_22

def loopBody721_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 4#64)

def loopBody721_25 : HolLoopProg 64 :=
.mark loopBody721_24

def loopBody721_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody721_27 : HolLoopProg 64 :=
.mark loopBody721_26

def loopBody721_28 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 780) ([4, 5, 6, 7]) (some (4, loopBody721_27, loopBody721_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody721_29 : HolLoopProg 64 :=
.mark loopBody721_28

def loopBody721_30 : HolLoopProg 64 :=
.seq loopBody721_29 loopBody721_1

def loopBody721_31 : HolLoopProg 64 :=
.mark loopBody721_30

def loopBody721_32 : HolLoopProg 64 :=
.seq loopBody721_25 loopBody721_31

def loopBody721_33 : HolLoopProg 64 :=
.mark loopBody721_32

def loopBody721_34 : HolLoopProg 64 :=
.seq loopBody721_23 loopBody721_33

def loopBody721_35 : HolLoopProg 64 :=
.mark loopBody721_34

def loopBody721_36 : HolLoopProg 64 :=
.seq loopBody721_21 loopBody721_35

def loopBody721_37 : HolLoopProg 64 :=
.mark loopBody721_36

def loopBody721_38 : HolLoopProg 64 :=
.seq loopBody721_19 loopBody721_37

def loopBody721_39 : HolLoopProg 64 :=
.mark loopBody721_38

def loopBody721_40 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_39

def loopBody721_41 : HolLoopProg 64 :=
.mark loopBody721_40

def loopBody721_42 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_41

def loopBody721_43 : HolLoopProg 64 :=
.mark loopBody721_42

def loopBody721_44 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 775) ([4]) (some (4, loopBody721_27, loopBody721_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody721_45 : HolLoopProg 64 :=
.mark loopBody721_44

def loopBody721_46 : HolLoopProg 64 :=
.seq loopBody721_45 loopBody721_1

def loopBody721_47 : HolLoopProg 64 :=
.mark loopBody721_46

def loopBody721_48 : HolLoopProg 64 :=
.seq loopBody721_19 loopBody721_47

def loopBody721_49 : HolLoopProg 64 :=
.mark loopBody721_48

def loopBody721_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody721_51 : HolLoopProg 64 :=
.mark loopBody721_50

def loopBody721_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody721_53 : HolLoopProg 64 :=
.mark loopBody721_52

def loopBody721_54 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 70) ([5]) (some (5, loopBody721_53, loopBody721_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody721_55 : HolLoopProg 64 :=
.mark loopBody721_54

def loopBody721_56 : HolLoopProg 64 :=
.seq loopBody721_55 loopBody721_1

def loopBody721_57 : HolLoopProg 64 :=
.mark loopBody721_56

def loopBody721_58 : HolLoopProg 64 :=
.seq loopBody721_51 loopBody721_57

def loopBody721_59 : HolLoopProg 64 :=
.mark loopBody721_58

def loopBody721_60 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_59

def loopBody721_61 : HolLoopProg 64 :=
.mark loopBody721_60

def loopBody721_62 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_61

def loopBody721_63 : HolLoopProg 64 :=
.mark loopBody721_62

def loopBody721_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody721_65 : HolLoopProg 64 :=
.mark loopBody721_64

def loopBody721_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody721_67 : HolLoopProg 64 :=
.mark loopBody721_66

def loopBody721_68 : HolLoopProg 64 :=
.seq loopBody721_67 loopBody721_1

def loopBody721_69 : HolLoopProg 64 :=
.mark loopBody721_68

def loopBody721_70 : HolLoopProg 64 :=
.seq loopBody721_65 loopBody721_69

def loopBody721_71 : HolLoopProg 64 :=
.mark loopBody721_70

def loopBody721_72 : HolLoopProg 64 :=
.seq loopBody721_63 loopBody721_71

def loopBody721_73 : HolLoopProg 64 :=
.mark loopBody721_72

def loopBody721_74 : HolLoopProg 64 :=
.seq loopBody721_49 loopBody721_73

def loopBody721_75 : HolLoopProg 64 :=
.mark loopBody721_74

def loopBody721_76 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_75

def loopBody721_77 : HolLoopProg 64 :=
.mark loopBody721_76

def loopBody721_78 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_77

def loopBody721_79 : HolLoopProg 64 :=
.mark loopBody721_78

def loopBody721_80 : HolLoopProg 64 :=
.seq loopBody721_43 loopBody721_79

def loopBody721_81 : HolLoopProg 64 :=
.mark loopBody721_80

def loopBody721_82 : HolLoopProg 64 :=
.seq loopBody721_17 loopBody721_81

def loopBody721_83 : HolLoopProg 64 :=
.mark loopBody721_82

def loopBody721_84 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_83

def loopBody721_85 : HolLoopProg 64 :=
.mark loopBody721_84

def loopBody721_86 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_85

def loopBody721_87 : HolLoopProg 64 :=
.mark loopBody721_86

def loopBody721_88 : HolLoopProg 64 :=
.seq loopBody721_7 loopBody721_87

def loopBody721_89 : HolLoopProg 64 :=
.mark loopBody721_88

def loopBody721_90 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_89

def loopBody721_91 : HolLoopProg 64 :=
.mark loopBody721_90

def loopBody721_92 : HolLoopProg 64 :=
.seq loopBody721_1 loopBody721_91

def loopBody721_93 : HolLoopProg 64 :=
.mark loopBody721_92

def output721 : Nat × List Nat × HolLoopProg 64 :=
  (785, [0], loopBody721_93)
end InitECandidate.Proofs.FrontendStages.Loop
