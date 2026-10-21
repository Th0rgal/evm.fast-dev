import InitECandidate.Proofs.FrontendStages.Loop.Translate433
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody449_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody449_1 : HolLoopProg 64 :=
.mark loopBody449_0

def loopBody449_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody449_3 : HolLoopProg 64 :=
.mark loopBody449_2

def loopBody449_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody449_3, loopBody449_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody449_5 : HolLoopProg 64 :=
.mark loopBody449_4

def loopBody449_6 : HolLoopProg 64 :=
.seq loopBody449_5 loopBody449_1

def loopBody449_7 : HolLoopProg 64 :=
.mark loopBody449_6

def loopBody449_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 3#64)

def loopBody449_9 : HolLoopProg 64 :=
.mark loopBody449_8

def loopBody449_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody449_11 : HolLoopProg 64 :=
.mark loopBody449_10

def loopBody449_12 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 466) ([6]) (some (6, loopBody449_11, loopBody449_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody449_13 : HolLoopProg 64 :=
.mark loopBody449_12

def loopBody449_14 : HolLoopProg 64 :=
.seq loopBody449_13 loopBody449_1

def loopBody449_15 : HolLoopProg 64 :=
.mark loopBody449_14

def loopBody449_16 : HolLoopProg 64 :=
.seq loopBody449_9 loopBody449_15

def loopBody449_17 : HolLoopProg 64 :=
.mark loopBody449_16

def loopBody449_18 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_17

def loopBody449_19 : HolLoopProg 64 :=
.mark loopBody449_18

def loopBody449_20 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_19

def loopBody449_21 : HolLoopProg 64 :=
.mark loopBody449_20

def loopBody449_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 18446744073709551615#64])

def loopBody449_23 : HolLoopProg 64 :=
.mark loopBody449_22

def loopBody449_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 18446744073709551615#64])

def loopBody449_25 : HolLoopProg 64 :=
.mark loopBody449_24

def loopBody449_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 18446744073709551615#64])

def loopBody449_27 : HolLoopProg 64 :=
.mark loopBody449_26

def loopBody449_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.xor
    [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 18446744073709551615#64])

def loopBody449_29 : HolLoopProg 64 :=
.mark loopBody449_28

def loopBody449_30 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 472) ([6, 7, 8, 9]) (some (6, loopBody449_11, loopBody449_1, (Flapjack.Spt.ln)))

def loopBody449_31 : HolLoopProg 64 :=
.mark loopBody449_30

def loopBody449_32 : HolLoopProg 64 :=
.seq loopBody449_31 loopBody449_1

def loopBody449_33 : HolLoopProg 64 :=
.mark loopBody449_32

def loopBody449_34 : HolLoopProg 64 :=
.seq loopBody449_29 loopBody449_33

def loopBody449_35 : HolLoopProg 64 :=
.mark loopBody449_34

def loopBody449_36 : HolLoopProg 64 :=
.seq loopBody449_27 loopBody449_35

def loopBody449_37 : HolLoopProg 64 :=
.mark loopBody449_36

def loopBody449_38 : HolLoopProg 64 :=
.seq loopBody449_25 loopBody449_37

def loopBody449_39 : HolLoopProg 64 :=
.mark loopBody449_38

def loopBody449_40 : HolLoopProg 64 :=
.seq loopBody449_23 loopBody449_39

def loopBody449_41 : HolLoopProg 64 :=
.mark loopBody449_40

def loopBody449_42 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_41

def loopBody449_43 : HolLoopProg 64 :=
.mark loopBody449_42

def loopBody449_44 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_43

def loopBody449_45 : HolLoopProg 64 :=
.mark loopBody449_44

def loopBody449_46 : HolLoopProg 64 :=
.seq loopBody449_21 loopBody449_45

def loopBody449_47 : HolLoopProg 64 :=
.mark loopBody449_46

def loopBody449_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody449_49 : HolLoopProg 64 :=
.mark loopBody449_48

def loopBody449_50 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.ln)) (some 486) ([6]) (some (6, loopBody449_11, loopBody449_1, (Flapjack.Spt.ln)))

def loopBody449_51 : HolLoopProg 64 :=
.mark loopBody449_50

def loopBody449_52 : HolLoopProg 64 :=
.seq loopBody449_51 loopBody449_1

def loopBody449_53 : HolLoopProg 64 :=
.mark loopBody449_52

def loopBody449_54 : HolLoopProg 64 :=
.seq loopBody449_49 loopBody449_53

def loopBody449_55 : HolLoopProg 64 :=
.mark loopBody449_54

def loopBody449_56 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_55

def loopBody449_57 : HolLoopProg 64 :=
.mark loopBody449_56

def loopBody449_58 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_57

def loopBody449_59 : HolLoopProg 64 :=
.mark loopBody449_58

def loopBody449_60 : HolLoopProg 64 :=
.seq loopBody449_47 loopBody449_59

def loopBody449_61 : HolLoopProg 64 :=
.mark loopBody449_60

def loopBody449_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody449_63 : HolLoopProg 64 :=
.mark loopBody449_62

def loopBody449_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody449_65 : HolLoopProg 64 :=
.mark loopBody449_64

def loopBody449_66 : HolLoopProg 64 :=
.seq loopBody449_65 loopBody449_1

def loopBody449_67 : HolLoopProg 64 :=
.mark loopBody449_66

def loopBody449_68 : HolLoopProg 64 :=
.seq loopBody449_63 loopBody449_67

def loopBody449_69 : HolLoopProg 64 :=
.mark loopBody449_68

def loopBody449_70 : HolLoopProg 64 :=
.seq loopBody449_61 loopBody449_69

def loopBody449_71 : HolLoopProg 64 :=
.mark loopBody449_70

def loopBody449_72 : HolLoopProg 64 :=
.seq loopBody449_7 loopBody449_71

def loopBody449_73 : HolLoopProg 64 :=
.mark loopBody449_72

def loopBody449_74 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_73

def loopBody449_75 : HolLoopProg 64 :=
.mark loopBody449_74

def loopBody449_76 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_75

def loopBody449_77 : HolLoopProg 64 :=
.mark loopBody449_76

def loopBody449_78 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_77

def loopBody449_79 : HolLoopProg 64 :=
.mark loopBody449_78

def loopBody449_80 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_79

def loopBody449_81 : HolLoopProg 64 :=
.mark loopBody449_80

def loopBody449_82 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_81

def loopBody449_83 : HolLoopProg 64 :=
.mark loopBody449_82

def loopBody449_84 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_83

def loopBody449_85 : HolLoopProg 64 :=
.mark loopBody449_84

def loopBody449_86 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_85

def loopBody449_87 : HolLoopProg 64 :=
.mark loopBody449_86

def loopBody449_88 : HolLoopProg 64 :=
.seq loopBody449_1 loopBody449_87

def loopBody449_89 : HolLoopProg 64 :=
.mark loopBody449_88

def output449 : Nat × List Nat × HolLoopProg 64 :=
  (513, [], loopBody449_89)
end InitECandidate.Proofs.FrontendStages.Loop
