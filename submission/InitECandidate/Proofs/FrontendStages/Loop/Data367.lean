import InitECandidate.Proofs.FrontendStages.Loop.Translate351
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody367_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody367_1 : HolLoopProg 64 :=
.mark loopBody367_0

def loopBody367_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 24#64)

def loopBody367_3 : HolLoopProg 64 :=
.mark loopBody367_2

def loopBody367_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody367_5 : HolLoopProg 64 :=
.mark loopBody367_4

def loopBody367_6 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 68) ([3]) (some (3, loopBody367_5, loopBody367_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody367_7 : HolLoopProg 64 :=
.mark loopBody367_6

def loopBody367_8 : HolLoopProg 64 :=
.seq loopBody367_7 loopBody367_1

def loopBody367_9 : HolLoopProg 64 :=
.mark loopBody367_8

def loopBody367_10 : HolLoopProg 64 :=
.seq loopBody367_3 loopBody367_9

def loopBody367_11 : HolLoopProg 64 :=
.mark loopBody367_10

def loopBody367_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody367_13 : HolLoopProg 64 :=
.mark loopBody367_12

def loopBody367_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody367_15 : HolLoopProg 64 :=
.mark loopBody367_14

def loopBody367_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 6 6 4 5)

def loopBody367_17 : HolLoopProg 64 :=
.mark loopBody367_16

def loopBody367_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody367_19 : HolLoopProg 64 :=
.mark loopBody367_18

def loopBody367_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody367_21 : HolLoopProg 64 :=
.mark loopBody367_20

def loopBody367_22 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))) (some 68) ([7]) (some (4, loopBody367_21, loopBody367_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody367_23 : HolLoopProg 64 :=
.mark loopBody367_22

def loopBody367_24 : HolLoopProg 64 :=
.seq loopBody367_23 loopBody367_1

def loopBody367_25 : HolLoopProg 64 :=
.mark loopBody367_24

def loopBody367_26 : HolLoopProg 64 :=
.seq loopBody367_19 loopBody367_25

def loopBody367_27 : HolLoopProg 64 :=
.mark loopBody367_26

def loopBody367_28 : HolLoopProg 64 :=
.seq loopBody367_17 loopBody367_27

def loopBody367_29 : HolLoopProg 64 :=
.mark loopBody367_28

def loopBody367_30 : HolLoopProg 64 :=
.seq loopBody367_15 loopBody367_29

def loopBody367_31 : HolLoopProg 64 :=
.mark loopBody367_30

def loopBody367_32 : HolLoopProg 64 :=
.seq loopBody367_13 loopBody367_31

def loopBody367_33 : HolLoopProg 64 :=
.mark loopBody367_32

def loopBody367_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 0#64])

def loopBody367_35 : HolLoopProg 64 :=
.mark loopBody367_34

def loopBody367_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody367_37 : HolLoopProg 64 :=
.mark loopBody367_36

def loopBody367_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody367_39 : HolLoopProg 64 :=
.mark loopBody367_38

def loopBody367_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 4) 6

def loopBody367_41 : HolLoopProg 64 :=
.mark loopBody367_40

def loopBody367_42 : HolLoopProg 64 :=
.seq loopBody367_41 loopBody367_1

def loopBody367_43 : HolLoopProg 64 :=
.mark loopBody367_42

def loopBody367_44 : HolLoopProg 64 :=
.seq loopBody367_39 loopBody367_43

def loopBody367_45 : HolLoopProg 64 :=
.mark loopBody367_44

def loopBody367_46 : HolLoopProg 64 :=
.seq loopBody367_45 loopBody367_1

def loopBody367_47 : HolLoopProg 64 :=
.mark loopBody367_46

def loopBody367_48 : HolLoopProg 64 :=
.seq loopBody367_37 loopBody367_47

def loopBody367_49 : HolLoopProg 64 :=
.mark loopBody367_48

def loopBody367_50 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_49

def loopBody367_51 : HolLoopProg 64 :=
.mark loopBody367_50

def loopBody367_52 : HolLoopProg 64 :=
.seq loopBody367_35 loopBody367_51

def loopBody367_53 : HolLoopProg 64 :=
.mark loopBody367_52

def loopBody367_54 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_53

def loopBody367_55 : HolLoopProg 64 :=
.mark loopBody367_54

def loopBody367_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64])

def loopBody367_57 : HolLoopProg 64 :=
.mark loopBody367_56

def loopBody367_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody367_59 : HolLoopProg 64 :=
.mark loopBody367_58

def loopBody367_60 : HolLoopProg 64 :=
.seq loopBody367_59 loopBody367_47

def loopBody367_61 : HolLoopProg 64 :=
.mark loopBody367_60

def loopBody367_62 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_61

def loopBody367_63 : HolLoopProg 64 :=
.mark loopBody367_62

def loopBody367_64 : HolLoopProg 64 :=
.seq loopBody367_57 loopBody367_63

def loopBody367_65 : HolLoopProg 64 :=
.mark loopBody367_64

def loopBody367_66 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_65

def loopBody367_67 : HolLoopProg 64 :=
.mark loopBody367_66

def loopBody367_68 : HolLoopProg 64 :=
.seq loopBody367_55 loopBody367_67

def loopBody367_69 : HolLoopProg 64 :=
.mark loopBody367_68

def loopBody367_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 16#64])

def loopBody367_71 : HolLoopProg 64 :=
.mark loopBody367_70

def loopBody367_72 : HolLoopProg 64 :=
.seq loopBody367_15 loopBody367_47

def loopBody367_73 : HolLoopProg 64 :=
.mark loopBody367_72

def loopBody367_74 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_73

def loopBody367_75 : HolLoopProg 64 :=
.mark loopBody367_74

def loopBody367_76 : HolLoopProg 64 :=
.seq loopBody367_71 loopBody367_75

def loopBody367_77 : HolLoopProg 64 :=
.mark loopBody367_76

def loopBody367_78 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_77

def loopBody367_79 : HolLoopProg 64 :=
.mark loopBody367_78

def loopBody367_80 : HolLoopProg 64 :=
.seq loopBody367_69 loopBody367_79

def loopBody367_81 : HolLoopProg 64 :=
.mark loopBody367_80

def loopBody367_82 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody367_83 : HolLoopProg 64 :=
.mark loopBody367_82

def loopBody367_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody367_85 : HolLoopProg 64 :=
.mark loopBody367_84

def loopBody367_86 : HolLoopProg 64 :=
.seq loopBody367_85 loopBody367_1

def loopBody367_87 : HolLoopProg 64 :=
.mark loopBody367_86

def loopBody367_88 : HolLoopProg 64 :=
.seq loopBody367_83 loopBody367_87

def loopBody367_89 : HolLoopProg 64 :=
.mark loopBody367_88

def loopBody367_90 : HolLoopProg 64 :=
.seq loopBody367_81 loopBody367_89

def loopBody367_91 : HolLoopProg 64 :=
.mark loopBody367_90

def loopBody367_92 : HolLoopProg 64 :=
.seq loopBody367_33 loopBody367_91

def loopBody367_93 : HolLoopProg 64 :=
.mark loopBody367_92

def loopBody367_94 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_93

def loopBody367_95 : HolLoopProg 64 :=
.mark loopBody367_94

def loopBody367_96 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_95

def loopBody367_97 : HolLoopProg 64 :=
.mark loopBody367_96

def loopBody367_98 : HolLoopProg 64 :=
.seq loopBody367_11 loopBody367_97

def loopBody367_99 : HolLoopProg 64 :=
.mark loopBody367_98

def loopBody367_100 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_99

def loopBody367_101 : HolLoopProg 64 :=
.mark loopBody367_100

def loopBody367_102 : HolLoopProg 64 :=
.seq loopBody367_1 loopBody367_101

def loopBody367_103 : HolLoopProg 64 :=
.mark loopBody367_102

def output367 : Nat × List Nat × HolLoopProg 64 :=
  (431, [0, 1], loopBody367_103)
end InitECandidate.Proofs.FrontendStages.Loop
