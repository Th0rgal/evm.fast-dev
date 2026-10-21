import InitECandidate.Proofs.FrontendStages.Loop.Translate361
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody377_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody377_1 : HolLoopProg 64 :=
.mark loopBody377_0

def loopBody377_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody377_3 : HolLoopProg 64 :=
.mark loopBody377_2

def loopBody377_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody377_5 : HolLoopProg 64 :=
.mark loopBody377_4

def loopBody377_6 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 435) ([5]) (some (5, loopBody377_5, loopBody377_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody377_7 : HolLoopProg 64 :=
.mark loopBody377_6

def loopBody377_8 : HolLoopProg 64 :=
.seq loopBody377_7 loopBody377_1

def loopBody377_9 : HolLoopProg 64 :=
.mark loopBody377_8

def loopBody377_10 : HolLoopProg 64 :=
.seq loopBody377_3 loopBody377_9

def loopBody377_11 : HolLoopProg 64 :=
.mark loopBody377_10

def loopBody377_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 32#64]))

def loopBody377_13 : HolLoopProg 64 :=
.mark loopBody377_12

def loopBody377_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 24#64)

def loopBody377_15 : HolLoopProg 64 :=
.mark loopBody377_14

def loopBody377_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody377_17 : HolLoopProg 64 :=
.mark loopBody377_16

def loopBody377_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody377_19 : HolLoopProg 64 :=
.mark loopBody377_18

def loopBody377_20 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 436) ([6, 7, 8]) (some (6, loopBody377_19, loopBody377_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody377_21 : HolLoopProg 64 :=
.mark loopBody377_20

def loopBody377_22 : HolLoopProg 64 :=
.seq loopBody377_21 loopBody377_1

def loopBody377_23 : HolLoopProg 64 :=
.mark loopBody377_22

def loopBody377_24 : HolLoopProg 64 :=
.seq loopBody377_17 loopBody377_23

def loopBody377_25 : HolLoopProg 64 :=
.mark loopBody377_24

def loopBody377_26 : HolLoopProg 64 :=
.seq loopBody377_15 loopBody377_25

def loopBody377_27 : HolLoopProg 64 :=
.mark loopBody377_26

def loopBody377_28 : HolLoopProg 64 :=
.seq loopBody377_13 loopBody377_27

def loopBody377_29 : HolLoopProg 64 :=
.mark loopBody377_28

def loopBody377_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 8#64])

def loopBody377_31 : HolLoopProg 64 :=
.mark loopBody377_30

def loopBody377_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody377_33 : HolLoopProg 64 :=
.mark loopBody377_32

def loopBody377_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 7)

def loopBody377_35 : HolLoopProg 64 :=
.mark loopBody377_34

def loopBody377_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 6) 8

def loopBody377_37 : HolLoopProg 64 :=
.mark loopBody377_36

def loopBody377_38 : HolLoopProg 64 :=
.seq loopBody377_37 loopBody377_1

def loopBody377_39 : HolLoopProg 64 :=
.mark loopBody377_38

def loopBody377_40 : HolLoopProg 64 :=
.seq loopBody377_35 loopBody377_39

def loopBody377_41 : HolLoopProg 64 :=
.mark loopBody377_40

def loopBody377_42 : HolLoopProg 64 :=
.seq loopBody377_41 loopBody377_1

def loopBody377_43 : HolLoopProg 64 :=
.mark loopBody377_42

def loopBody377_44 : HolLoopProg 64 :=
.seq loopBody377_33 loopBody377_43

def loopBody377_45 : HolLoopProg 64 :=
.mark loopBody377_44

def loopBody377_46 : HolLoopProg 64 :=
.seq loopBody377_1 loopBody377_45

def loopBody377_47 : HolLoopProg 64 :=
.mark loopBody377_46

def loopBody377_48 : HolLoopProg 64 :=
.seq loopBody377_31 loopBody377_47

def loopBody377_49 : HolLoopProg 64 :=
.mark loopBody377_48

def loopBody377_50 : HolLoopProg 64 :=
.seq loopBody377_1 loopBody377_49

def loopBody377_51 : HolLoopProg 64 :=
.mark loopBody377_50

def loopBody377_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 16#64])

def loopBody377_53 : HolLoopProg 64 :=
.mark loopBody377_52

def loopBody377_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody377_55 : HolLoopProg 64 :=
.mark loopBody377_54

def loopBody377_56 : HolLoopProg 64 :=
.seq loopBody377_55 loopBody377_43

def loopBody377_57 : HolLoopProg 64 :=
.mark loopBody377_56

def loopBody377_58 : HolLoopProg 64 :=
.seq loopBody377_1 loopBody377_57

def loopBody377_59 : HolLoopProg 64 :=
.mark loopBody377_58

def loopBody377_60 : HolLoopProg 64 :=
.seq loopBody377_53 loopBody377_59

def loopBody377_61 : HolLoopProg 64 :=
.mark loopBody377_60

def loopBody377_62 : HolLoopProg 64 :=
.seq loopBody377_1 loopBody377_61

def loopBody377_63 : HolLoopProg 64 :=
.mark loopBody377_62

def loopBody377_64 : HolLoopProg 64 :=
.seq loopBody377_51 loopBody377_63

def loopBody377_65 : HolLoopProg 64 :=
.mark loopBody377_64

def loopBody377_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody377_67 : HolLoopProg 64 :=
.mark loopBody377_66

def loopBody377_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody377_69 : HolLoopProg 64 :=
.mark loopBody377_68

def loopBody377_70 : HolLoopProg 64 :=
.seq loopBody377_69 loopBody377_1

def loopBody377_71 : HolLoopProg 64 :=
.mark loopBody377_70

def loopBody377_72 : HolLoopProg 64 :=
.seq loopBody377_67 loopBody377_71

def loopBody377_73 : HolLoopProg 64 :=
.mark loopBody377_72

def loopBody377_74 : HolLoopProg 64 :=
.seq loopBody377_65 loopBody377_73

def loopBody377_75 : HolLoopProg 64 :=
.mark loopBody377_74

def loopBody377_76 : HolLoopProg 64 :=
.seq loopBody377_29 loopBody377_75

def loopBody377_77 : HolLoopProg 64 :=
.mark loopBody377_76

def loopBody377_78 : HolLoopProg 64 :=
.seq loopBody377_1 loopBody377_77

def loopBody377_79 : HolLoopProg 64 :=
.mark loopBody377_78

def loopBody377_80 : HolLoopProg 64 :=
.seq loopBody377_1 loopBody377_79

def loopBody377_81 : HolLoopProg 64 :=
.mark loopBody377_80

def loopBody377_82 : HolLoopProg 64 :=
.seq loopBody377_11 loopBody377_81

def loopBody377_83 : HolLoopProg 64 :=
.mark loopBody377_82

def loopBody377_84 : HolLoopProg 64 :=
.seq loopBody377_1 loopBody377_83

def loopBody377_85 : HolLoopProg 64 :=
.mark loopBody377_84

def loopBody377_86 : HolLoopProg 64 :=
.seq loopBody377_1 loopBody377_85

def loopBody377_87 : HolLoopProg 64 :=
.mark loopBody377_86

def output377 : Nat × List Nat × HolLoopProg 64 :=
  (441, [0, 1, 2, 3], loopBody377_87)
end InitECandidate.Proofs.FrontendStages.Loop
