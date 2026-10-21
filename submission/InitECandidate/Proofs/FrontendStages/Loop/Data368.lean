import InitECandidate.Proofs.FrontendStages.Loop.Translate352
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody368_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody368_1 : HolLoopProg 64 :=
.mark loopBody368_0

def loopBody368_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 24#64)

def loopBody368_3 : HolLoopProg 64 :=
.mark loopBody368_2

def loopBody368_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody368_5 : HolLoopProg 64 :=
.mark loopBody368_4

def loopBody368_6 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 74) ([3]) (some (3, loopBody368_5, loopBody368_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody368_7 : HolLoopProg 64 :=
.mark loopBody368_6

def loopBody368_8 : HolLoopProg 64 :=
.seq loopBody368_7 loopBody368_1

def loopBody368_9 : HolLoopProg 64 :=
.mark loopBody368_8

def loopBody368_10 : HolLoopProg 64 :=
.seq loopBody368_3 loopBody368_9

def loopBody368_11 : HolLoopProg 64 :=
.mark loopBody368_10

def loopBody368_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody368_13 : HolLoopProg 64 :=
.mark loopBody368_12

def loopBody368_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody368_15 : HolLoopProg 64 :=
.mark loopBody368_14

def loopBody368_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 6 6 4 5)

def loopBody368_17 : HolLoopProg 64 :=
.mark loopBody368_16

def loopBody368_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody368_19 : HolLoopProg 64 :=
.mark loopBody368_18

def loopBody368_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody368_21 : HolLoopProg 64 :=
.mark loopBody368_20

def loopBody368_22 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 74) ([7]) (some (4, loopBody368_21, loopBody368_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody368_23 : HolLoopProg 64 :=
.mark loopBody368_22

def loopBody368_24 : HolLoopProg 64 :=
.seq loopBody368_23 loopBody368_1

def loopBody368_25 : HolLoopProg 64 :=
.mark loopBody368_24

def loopBody368_26 : HolLoopProg 64 :=
.seq loopBody368_19 loopBody368_25

def loopBody368_27 : HolLoopProg 64 :=
.mark loopBody368_26

def loopBody368_28 : HolLoopProg 64 :=
.seq loopBody368_17 loopBody368_27

def loopBody368_29 : HolLoopProg 64 :=
.mark loopBody368_28

def loopBody368_30 : HolLoopProg 64 :=
.seq loopBody368_15 loopBody368_29

def loopBody368_31 : HolLoopProg 64 :=
.mark loopBody368_30

def loopBody368_32 : HolLoopProg 64 :=
.seq loopBody368_13 loopBody368_31

def loopBody368_33 : HolLoopProg 64 :=
.mark loopBody368_32

def loopBody368_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 0#64])

def loopBody368_35 : HolLoopProg 64 :=
.mark loopBody368_34

def loopBody368_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody368_37 : HolLoopProg 64 :=
.mark loopBody368_36

def loopBody368_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody368_39 : HolLoopProg 64 :=
.mark loopBody368_38

def loopBody368_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 4) 6

def loopBody368_41 : HolLoopProg 64 :=
.mark loopBody368_40

def loopBody368_42 : HolLoopProg 64 :=
.seq loopBody368_41 loopBody368_1

def loopBody368_43 : HolLoopProg 64 :=
.mark loopBody368_42

def loopBody368_44 : HolLoopProg 64 :=
.seq loopBody368_39 loopBody368_43

def loopBody368_45 : HolLoopProg 64 :=
.mark loopBody368_44

def loopBody368_46 : HolLoopProg 64 :=
.seq loopBody368_45 loopBody368_1

def loopBody368_47 : HolLoopProg 64 :=
.mark loopBody368_46

def loopBody368_48 : HolLoopProg 64 :=
.seq loopBody368_37 loopBody368_47

def loopBody368_49 : HolLoopProg 64 :=
.mark loopBody368_48

def loopBody368_50 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_49

def loopBody368_51 : HolLoopProg 64 :=
.mark loopBody368_50

def loopBody368_52 : HolLoopProg 64 :=
.seq loopBody368_35 loopBody368_51

def loopBody368_53 : HolLoopProg 64 :=
.mark loopBody368_52

def loopBody368_54 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_53

def loopBody368_55 : HolLoopProg 64 :=
.mark loopBody368_54

def loopBody368_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64])

def loopBody368_57 : HolLoopProg 64 :=
.mark loopBody368_56

def loopBody368_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody368_59 : HolLoopProg 64 :=
.mark loopBody368_58

def loopBody368_60 : HolLoopProg 64 :=
.seq loopBody368_59 loopBody368_47

def loopBody368_61 : HolLoopProg 64 :=
.mark loopBody368_60

def loopBody368_62 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_61

def loopBody368_63 : HolLoopProg 64 :=
.mark loopBody368_62

def loopBody368_64 : HolLoopProg 64 :=
.seq loopBody368_57 loopBody368_63

def loopBody368_65 : HolLoopProg 64 :=
.mark loopBody368_64

def loopBody368_66 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_65

def loopBody368_67 : HolLoopProg 64 :=
.mark loopBody368_66

def loopBody368_68 : HolLoopProg 64 :=
.seq loopBody368_55 loopBody368_67

def loopBody368_69 : HolLoopProg 64 :=
.mark loopBody368_68

def loopBody368_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 16#64])

def loopBody368_71 : HolLoopProg 64 :=
.mark loopBody368_70

def loopBody368_72 : HolLoopProg 64 :=
.seq loopBody368_15 loopBody368_47

def loopBody368_73 : HolLoopProg 64 :=
.mark loopBody368_72

def loopBody368_74 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_73

def loopBody368_75 : HolLoopProg 64 :=
.mark loopBody368_74

def loopBody368_76 : HolLoopProg 64 :=
.seq loopBody368_71 loopBody368_75

def loopBody368_77 : HolLoopProg 64 :=
.mark loopBody368_76

def loopBody368_78 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_77

def loopBody368_79 : HolLoopProg 64 :=
.mark loopBody368_78

def loopBody368_80 : HolLoopProg 64 :=
.seq loopBody368_69 loopBody368_79

def loopBody368_81 : HolLoopProg 64 :=
.mark loopBody368_80

def loopBody368_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody368_83 : HolLoopProg 64 :=
.mark loopBody368_82

def loopBody368_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody368_85 : HolLoopProg 64 :=
.mark loopBody368_84

def loopBody368_86 : HolLoopProg 64 :=
.seq loopBody368_85 loopBody368_1

def loopBody368_87 : HolLoopProg 64 :=
.mark loopBody368_86

def loopBody368_88 : HolLoopProg 64 :=
.seq loopBody368_83 loopBody368_87

def loopBody368_89 : HolLoopProg 64 :=
.mark loopBody368_88

def loopBody368_90 : HolLoopProg 64 :=
.seq loopBody368_81 loopBody368_89

def loopBody368_91 : HolLoopProg 64 :=
.mark loopBody368_90

def loopBody368_92 : HolLoopProg 64 :=
.seq loopBody368_33 loopBody368_91

def loopBody368_93 : HolLoopProg 64 :=
.mark loopBody368_92

def loopBody368_94 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_93

def loopBody368_95 : HolLoopProg 64 :=
.mark loopBody368_94

def loopBody368_96 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_95

def loopBody368_97 : HolLoopProg 64 :=
.mark loopBody368_96

def loopBody368_98 : HolLoopProg 64 :=
.seq loopBody368_11 loopBody368_97

def loopBody368_99 : HolLoopProg 64 :=
.mark loopBody368_98

def loopBody368_100 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_99

def loopBody368_101 : HolLoopProg 64 :=
.mark loopBody368_100

def loopBody368_102 : HolLoopProg 64 :=
.seq loopBody368_1 loopBody368_101

def loopBody368_103 : HolLoopProg 64 :=
.mark loopBody368_102

def output368 : Nat × List Nat × HolLoopProg 64 :=
  (432, [0, 1], loopBody368_103)
end InitECandidate.Proofs.FrontendStages.Loop
