import InitECandidate.Proofs.FrontendStages.Loop.Translate692
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody708_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody708_1 : HolLoopProg 64 :=
.mark loopBody708_0

def loopBody708_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody708_3 : HolLoopProg 64 :=
.mark loopBody708_2

def loopBody708_4 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 69) ([]) (some (3, loopBody708_3, loopBody708_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody708_5 : HolLoopProg 64 :=
.mark loopBody708_4

def loopBody708_6 : HolLoopProg 64 :=
.seq loopBody708_5 loopBody708_1

def loopBody708_7 : HolLoopProg 64 :=
.mark loopBody708_6

def loopBody708_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 96#64)

def loopBody708_9 : HolLoopProg 64 :=
.mark loopBody708_8

def loopBody708_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody708_11 : HolLoopProg 64 :=
.mark loopBody708_10

def loopBody708_12 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([4]) (some (4, loopBody708_11, loopBody708_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody708_13 : HolLoopProg 64 :=
.mark loopBody708_12

def loopBody708_14 : HolLoopProg 64 :=
.seq loopBody708_13 loopBody708_1

def loopBody708_15 : HolLoopProg 64 :=
.mark loopBody708_14

def loopBody708_16 : HolLoopProg 64 :=
.seq loopBody708_9 loopBody708_15

def loopBody708_17 : HolLoopProg 64 :=
.mark loopBody708_16

def loopBody708_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody708_19 : HolLoopProg 64 :=
.mark loopBody708_18

def loopBody708_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody708_21 : HolLoopProg 64 :=
.mark loopBody708_20

def loopBody708_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody708_23 : HolLoopProg 64 :=
.mark loopBody708_22

def loopBody708_24 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 769) ([5, 6]) (some (5, loopBody708_23, loopBody708_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody708_25 : HolLoopProg 64 :=
.mark loopBody708_24

def loopBody708_26 : HolLoopProg 64 :=
.seq loopBody708_25 loopBody708_1

def loopBody708_27 : HolLoopProg 64 :=
.mark loopBody708_26

def loopBody708_28 : HolLoopProg 64 :=
.seq loopBody708_21 loopBody708_27

def loopBody708_29 : HolLoopProg 64 :=
.mark loopBody708_28

def loopBody708_30 : HolLoopProg 64 :=
.seq loopBody708_19 loopBody708_29

def loopBody708_31 : HolLoopProg 64 :=
.mark loopBody708_30

def loopBody708_32 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_31

def loopBody708_33 : HolLoopProg 64 :=
.mark loopBody708_32

def loopBody708_34 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_33

def loopBody708_35 : HolLoopProg 64 :=
.mark loopBody708_34

def loopBody708_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody708_37 : HolLoopProg 64 :=
.mark loopBody708_36

def loopBody708_38 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 724) ([5, 6]) (some (5, loopBody708_23, loopBody708_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody708_39 : HolLoopProg 64 :=
.mark loopBody708_38

def loopBody708_40 : HolLoopProg 64 :=
.seq loopBody708_39 loopBody708_1

def loopBody708_41 : HolLoopProg 64 :=
.mark loopBody708_40

def loopBody708_42 : HolLoopProg 64 :=
.seq loopBody708_37 loopBody708_41

def loopBody708_43 : HolLoopProg 64 :=
.mark loopBody708_42

def loopBody708_44 : HolLoopProg 64 :=
.seq loopBody708_19 loopBody708_43

def loopBody708_45 : HolLoopProg 64 :=
.mark loopBody708_44

def loopBody708_46 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_45

def loopBody708_47 : HolLoopProg 64 :=
.mark loopBody708_46

def loopBody708_48 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_47

def loopBody708_49 : HolLoopProg 64 :=
.mark loopBody708_48

def loopBody708_50 : HolLoopProg 64 :=
.seq loopBody708_35 loopBody708_49

def loopBody708_51 : HolLoopProg 64 :=
.mark loopBody708_50

def loopBody708_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 48#64])

def loopBody708_53 : HolLoopProg 64 :=
.mark loopBody708_52

def loopBody708_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 64#64])

def loopBody708_55 : HolLoopProg 64 :=
.mark loopBody708_54

def loopBody708_56 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 724) ([5, 6]) (some (5, loopBody708_23, loopBody708_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody708_57 : HolLoopProg 64 :=
.mark loopBody708_56

def loopBody708_58 : HolLoopProg 64 :=
.seq loopBody708_57 loopBody708_1

def loopBody708_59 : HolLoopProg 64 :=
.mark loopBody708_58

def loopBody708_60 : HolLoopProg 64 :=
.seq loopBody708_55 loopBody708_59

def loopBody708_61 : HolLoopProg 64 :=
.mark loopBody708_60

def loopBody708_62 : HolLoopProg 64 :=
.seq loopBody708_53 loopBody708_61

def loopBody708_63 : HolLoopProg 64 :=
.mark loopBody708_62

def loopBody708_64 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_63

def loopBody708_65 : HolLoopProg 64 :=
.mark loopBody708_64

def loopBody708_66 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_65

def loopBody708_67 : HolLoopProg 64 :=
.mark loopBody708_66

def loopBody708_68 : HolLoopProg 64 :=
.seq loopBody708_51 loopBody708_67

def loopBody708_69 : HolLoopProg 64 :=
.mark loopBody708_68

def loopBody708_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody708_71 : HolLoopProg 64 :=
.mark loopBody708_70

def loopBody708_72 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.ln)) (some 70) ([5]) (some (5, loopBody708_23, loopBody708_1, (Flapjack.Spt.ln)))

def loopBody708_73 : HolLoopProg 64 :=
.mark loopBody708_72

def loopBody708_74 : HolLoopProg 64 :=
.seq loopBody708_73 loopBody708_1

def loopBody708_75 : HolLoopProg 64 :=
.mark loopBody708_74

def loopBody708_76 : HolLoopProg 64 :=
.seq loopBody708_71 loopBody708_75

def loopBody708_77 : HolLoopProg 64 :=
.mark loopBody708_76

def loopBody708_78 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_77

def loopBody708_79 : HolLoopProg 64 :=
.mark loopBody708_78

def loopBody708_80 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_79

def loopBody708_81 : HolLoopProg 64 :=
.mark loopBody708_80

def loopBody708_82 : HolLoopProg 64 :=
.seq loopBody708_69 loopBody708_81

def loopBody708_83 : HolLoopProg 64 :=
.mark loopBody708_82

def loopBody708_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody708_85 : HolLoopProg 64 :=
.mark loopBody708_84

def loopBody708_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody708_87 : HolLoopProg 64 :=
.mark loopBody708_86

def loopBody708_88 : HolLoopProg 64 :=
.seq loopBody708_87 loopBody708_1

def loopBody708_89 : HolLoopProg 64 :=
.mark loopBody708_88

def loopBody708_90 : HolLoopProg 64 :=
.seq loopBody708_85 loopBody708_89

def loopBody708_91 : HolLoopProg 64 :=
.mark loopBody708_90

def loopBody708_92 : HolLoopProg 64 :=
.seq loopBody708_83 loopBody708_91

def loopBody708_93 : HolLoopProg 64 :=
.mark loopBody708_92

def loopBody708_94 : HolLoopProg 64 :=
.seq loopBody708_17 loopBody708_93

def loopBody708_95 : HolLoopProg 64 :=
.mark loopBody708_94

def loopBody708_96 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_95

def loopBody708_97 : HolLoopProg 64 :=
.mark loopBody708_96

def loopBody708_98 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_97

def loopBody708_99 : HolLoopProg 64 :=
.mark loopBody708_98

def loopBody708_100 : HolLoopProg 64 :=
.seq loopBody708_7 loopBody708_99

def loopBody708_101 : HolLoopProg 64 :=
.mark loopBody708_100

def loopBody708_102 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_101

def loopBody708_103 : HolLoopProg 64 :=
.mark loopBody708_102

def loopBody708_104 : HolLoopProg 64 :=
.seq loopBody708_1 loopBody708_103

def loopBody708_105 : HolLoopProg 64 :=
.mark loopBody708_104

def output708 : Nat × List Nat × HolLoopProg 64 :=
  (772, [0, 1], loopBody708_105)
end InitECandidate.Proofs.FrontendStages.Loop
