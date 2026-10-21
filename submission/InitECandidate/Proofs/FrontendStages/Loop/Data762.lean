import InitECandidate.Proofs.FrontendStages.Loop.Translate746
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody762_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody762_1 : HolLoopProg 64 :=
.mark loopBody762_0

def loopBody762_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody762_3 : HolLoopProg 64 :=
.mark loopBody762_2

def loopBody762_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64]))

def loopBody762_5 : HolLoopProg 64 :=
.mark loopBody762_4

def loopBody762_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody762_7 : HolLoopProg 64 :=
.mark loopBody762_6

def loopBody762_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody762_9 : HolLoopProg 64 :=
.mark loopBody762_8

def loopBody762_10 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 461) ([4]) (some (4, loopBody762_9, loopBody762_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody762_11 : HolLoopProg 64 :=
.mark loopBody762_10

def loopBody762_12 : HolLoopProg 64 :=
.seq loopBody762_11 loopBody762_1

def loopBody762_13 : HolLoopProg 64 :=
.mark loopBody762_12

def loopBody762_14 : HolLoopProg 64 :=
.seq loopBody762_7 loopBody762_13

def loopBody762_15 : HolLoopProg 64 :=
.mark loopBody762_14

def loopBody762_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody762_17 : HolLoopProg 64 :=
.mark loopBody762_16

def loopBody762_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 3#64)

def loopBody762_19 : HolLoopProg 64 :=
.mark loopBody762_18

def loopBody762_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 7 7 5 6)

def loopBody762_21 : HolLoopProg 64 :=
.mark loopBody762_20

def loopBody762_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 15#64, Flapjack.HolLoopExp.var 7])

def loopBody762_23 : HolLoopProg 64 :=
.mark loopBody762_22

def loopBody762_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody762_25 : HolLoopProg 64 :=
.mark loopBody762_24

def loopBody762_26 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 466) ([8]) (some (5, loopBody762_25, loopBody762_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody762_27 : HolLoopProg 64 :=
.mark loopBody762_26

def loopBody762_28 : HolLoopProg 64 :=
.seq loopBody762_27 loopBody762_1

def loopBody762_29 : HolLoopProg 64 :=
.mark loopBody762_28

def loopBody762_30 : HolLoopProg 64 :=
.seq loopBody762_23 loopBody762_29

def loopBody762_31 : HolLoopProg 64 :=
.mark loopBody762_30

def loopBody762_32 : HolLoopProg 64 :=
.seq loopBody762_21 loopBody762_31

def loopBody762_33 : HolLoopProg 64 :=
.mark loopBody762_32

def loopBody762_34 : HolLoopProg 64 :=
.seq loopBody762_19 loopBody762_33

def loopBody762_35 : HolLoopProg 64 :=
.mark loopBody762_34

def loopBody762_36 : HolLoopProg 64 :=
.seq loopBody762_17 loopBody762_35

def loopBody762_37 : HolLoopProg 64 :=
.mark loopBody762_36

def loopBody762_38 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_37

def loopBody762_39 : HolLoopProg 64 :=
.mark loopBody762_38

def loopBody762_40 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_39

def loopBody762_41 : HolLoopProg 64 :=
.mark loopBody762_40

def loopBody762_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 120#64])

def loopBody762_43 : HolLoopProg 64 :=
.mark loopBody762_42

def loopBody762_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 88#64]))

def loopBody762_45 : HolLoopProg 64 :=
.mark loopBody762_44

def loopBody762_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody762_47 : HolLoopProg 64 :=
.mark loopBody762_46

def loopBody762_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 4) 6

def loopBody762_49 : HolLoopProg 64 :=
.mark loopBody762_48

def loopBody762_50 : HolLoopProg 64 :=
.seq loopBody762_49 loopBody762_1

def loopBody762_51 : HolLoopProg 64 :=
.mark loopBody762_50

def loopBody762_52 : HolLoopProg 64 :=
.seq loopBody762_47 loopBody762_51

def loopBody762_53 : HolLoopProg 64 :=
.mark loopBody762_52

def loopBody762_54 : HolLoopProg 64 :=
.seq loopBody762_53 loopBody762_1

def loopBody762_55 : HolLoopProg 64 :=
.mark loopBody762_54

def loopBody762_56 : HolLoopProg 64 :=
.seq loopBody762_45 loopBody762_55

def loopBody762_57 : HolLoopProg 64 :=
.mark loopBody762_56

def loopBody762_58 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_57

def loopBody762_59 : HolLoopProg 64 :=
.mark loopBody762_58

def loopBody762_60 : HolLoopProg 64 :=
.seq loopBody762_43 loopBody762_59

def loopBody762_61 : HolLoopProg 64 :=
.mark loopBody762_60

def loopBody762_62 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_61

def loopBody762_63 : HolLoopProg 64 :=
.mark loopBody762_62

def loopBody762_64 : HolLoopProg 64 :=
.seq loopBody762_41 loopBody762_63

def loopBody762_65 : HolLoopProg 64 :=
.mark loopBody762_64

def loopBody762_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 128#64])

def loopBody762_67 : HolLoopProg 64 :=
.mark loopBody762_66

def loopBody762_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody762_69 : HolLoopProg 64 :=
.mark loopBody762_68

def loopBody762_70 : HolLoopProg 64 :=
.seq loopBody762_69 loopBody762_55

def loopBody762_71 : HolLoopProg 64 :=
.mark loopBody762_70

def loopBody762_72 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_71

def loopBody762_73 : HolLoopProg 64 :=
.mark loopBody762_72

def loopBody762_74 : HolLoopProg 64 :=
.seq loopBody762_67 loopBody762_73

def loopBody762_75 : HolLoopProg 64 :=
.mark loopBody762_74

def loopBody762_76 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_75

def loopBody762_77 : HolLoopProg 64 :=
.mark loopBody762_76

def loopBody762_78 : HolLoopProg 64 :=
.seq loopBody762_65 loopBody762_77

def loopBody762_79 : HolLoopProg 64 :=
.mark loopBody762_78

def loopBody762_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody762_81 : HolLoopProg 64 :=
.mark loopBody762_80

def loopBody762_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody762_83 : HolLoopProg 64 :=
.mark loopBody762_82

def loopBody762_84 : HolLoopProg 64 :=
.seq loopBody762_83 loopBody762_1

def loopBody762_85 : HolLoopProg 64 :=
.mark loopBody762_84

def loopBody762_86 : HolLoopProg 64 :=
.seq loopBody762_81 loopBody762_85

def loopBody762_87 : HolLoopProg 64 :=
.mark loopBody762_86

def loopBody762_88 : HolLoopProg 64 :=
.seq loopBody762_79 loopBody762_87

def loopBody762_89 : HolLoopProg 64 :=
.mark loopBody762_88

def loopBody762_90 : HolLoopProg 64 :=
.seq loopBody762_15 loopBody762_89

def loopBody762_91 : HolLoopProg 64 :=
.mark loopBody762_90

def loopBody762_92 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_91

def loopBody762_93 : HolLoopProg 64 :=
.mark loopBody762_92

def loopBody762_94 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_93

def loopBody762_95 : HolLoopProg 64 :=
.mark loopBody762_94

def loopBody762_96 : HolLoopProg 64 :=
.seq loopBody762_5 loopBody762_95

def loopBody762_97 : HolLoopProg 64 :=
.mark loopBody762_96

def loopBody762_98 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_97

def loopBody762_99 : HolLoopProg 64 :=
.mark loopBody762_98

def loopBody762_100 : HolLoopProg 64 :=
.seq loopBody762_3 loopBody762_99

def loopBody762_101 : HolLoopProg 64 :=
.mark loopBody762_100

def loopBody762_102 : HolLoopProg 64 :=
.seq loopBody762_1 loopBody762_101

def loopBody762_103 : HolLoopProg 64 :=
.mark loopBody762_102

def output762 : Nat × List Nat × HolLoopProg 64 :=
  (826, [], loopBody762_103)
end InitECandidate.Proofs.FrontendStages.Loop
