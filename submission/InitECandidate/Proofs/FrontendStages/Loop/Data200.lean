import InitECandidate.Proofs.FrontendStages.Loop.Translate184
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody200_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody200_1 : HolLoopProg 64 :=
.mark loopBody200_0

def loopBody200_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody200_3 : HolLoopProg 64 :=
.mark loopBody200_2

def loopBody200_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody200_5 : HolLoopProg 64 :=
.mark loopBody200_4

def loopBody200_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 32#64)

def loopBody200_7 : HolLoopProg 64 :=
.mark loopBody200_6

def loopBody200_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody200_9 : HolLoopProg 64 :=
.mark loopBody200_8

def loopBody200_10 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([6, 7, 8]) (some (6, loopBody200_9, loopBody200_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody200_11 : HolLoopProg 64 :=
.mark loopBody200_10

def loopBody200_12 : HolLoopProg 64 :=
.seq loopBody200_11 loopBody200_1

def loopBody200_13 : HolLoopProg 64 :=
.mark loopBody200_12

def loopBody200_14 : HolLoopProg 64 :=
.seq loopBody200_7 loopBody200_13

def loopBody200_15 : HolLoopProg 64 :=
.mark loopBody200_14

def loopBody200_16 : HolLoopProg 64 :=
.seq loopBody200_5 loopBody200_15

def loopBody200_17 : HolLoopProg 64 :=
.mark loopBody200_16

def loopBody200_18 : HolLoopProg 64 :=
.seq loopBody200_3 loopBody200_17

def loopBody200_19 : HolLoopProg 64 :=
.mark loopBody200_18

def loopBody200_20 : HolLoopProg 64 :=
.seq loopBody200_1 loopBody200_19

def loopBody200_21 : HolLoopProg 64 :=
.mark loopBody200_20

def loopBody200_22 : HolLoopProg 64 :=
.seq loopBody200_1 loopBody200_21

def loopBody200_23 : HolLoopProg 64 :=
.mark loopBody200_22

def loopBody200_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 32#64])

def loopBody200_25 : HolLoopProg 64 :=
.mark loopBody200_24

def loopBody200_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody200_27 : HolLoopProg 64 :=
.mark loopBody200_26

def loopBody200_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 5 6

def loopBody200_29 : HolLoopProg 64 :=
.mark loopBody200_28

def loopBody200_30 : HolLoopProg 64 :=
.seq loopBody200_29 loopBody200_1

def loopBody200_31 : HolLoopProg 64 :=
.mark loopBody200_30

def loopBody200_32 : HolLoopProg 64 :=
.seq loopBody200_27 loopBody200_31

def loopBody200_33 : HolLoopProg 64 :=
.mark loopBody200_32

def loopBody200_34 : HolLoopProg 64 :=
.seq loopBody200_25 loopBody200_33

def loopBody200_35 : HolLoopProg 64 :=
.mark loopBody200_34

def loopBody200_36 : HolLoopProg 64 :=
.seq loopBody200_23 loopBody200_35

def loopBody200_37 : HolLoopProg 64 :=
.mark loopBody200_36

def loopBody200_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 33#64])

def loopBody200_39 : HolLoopProg 64 :=
.mark loopBody200_38

def loopBody200_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody200_41 : HolLoopProg 64 :=
.mark loopBody200_40

def loopBody200_42 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)) (some 87) ([6, 7]) (some (6, loopBody200_9, loopBody200_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))

def loopBody200_43 : HolLoopProg 64 :=
.mark loopBody200_42

def loopBody200_44 : HolLoopProg 64 :=
.seq loopBody200_43 loopBody200_1

def loopBody200_45 : HolLoopProg 64 :=
.mark loopBody200_44

def loopBody200_46 : HolLoopProg 64 :=
.seq loopBody200_41 loopBody200_45

def loopBody200_47 : HolLoopProg 64 :=
.mark loopBody200_46

def loopBody200_48 : HolLoopProg 64 :=
.seq loopBody200_39 loopBody200_47

def loopBody200_49 : HolLoopProg 64 :=
.mark loopBody200_48

def loopBody200_50 : HolLoopProg 64 :=
.seq loopBody200_1 loopBody200_49

def loopBody200_51 : HolLoopProg 64 :=
.mark loopBody200_50

def loopBody200_52 : HolLoopProg 64 :=
.seq loopBody200_1 loopBody200_51

def loopBody200_53 : HolLoopProg 64 :=
.mark loopBody200_52

def loopBody200_54 : HolLoopProg 64 :=
.seq loopBody200_37 loopBody200_53

def loopBody200_55 : HolLoopProg 64 :=
.mark loopBody200_54

def loopBody200_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 41#64])

def loopBody200_57 : HolLoopProg 64 :=
.mark loopBody200_56

def loopBody200_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 255#64])

def loopBody200_59 : HolLoopProg 64 :=
.mark loopBody200_58

def loopBody200_60 : HolLoopProg 64 :=
.seq loopBody200_59 loopBody200_31

def loopBody200_61 : HolLoopProg 64 :=
.mark loopBody200_60

def loopBody200_62 : HolLoopProg 64 :=
.seq loopBody200_57 loopBody200_61

def loopBody200_63 : HolLoopProg 64 :=
.mark loopBody200_62

def loopBody200_64 : HolLoopProg 64 :=
.seq loopBody200_55 loopBody200_63

def loopBody200_65 : HolLoopProg 64 :=
.mark loopBody200_64

def loopBody200_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 42#64])

def loopBody200_67 : HolLoopProg 64 :=
.mark loopBody200_66

def loopBody200_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 8#64))

def loopBody200_69 : HolLoopProg 64 :=
.mark loopBody200_68

def loopBody200_70 : HolLoopProg 64 :=
.seq loopBody200_69 loopBody200_31

def loopBody200_71 : HolLoopProg 64 :=
.mark loopBody200_70

def loopBody200_72 : HolLoopProg 64 :=
.seq loopBody200_67 loopBody200_71

def loopBody200_73 : HolLoopProg 64 :=
.mark loopBody200_72

def loopBody200_74 : HolLoopProg 64 :=
.seq loopBody200_65 loopBody200_73

def loopBody200_75 : HolLoopProg 64 :=
.mark loopBody200_74

def loopBody200_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 43#64)

def loopBody200_77 : HolLoopProg 64 :=
.mark loopBody200_76

def loopBody200_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody200_79 : HolLoopProg 64 :=
.mark loopBody200_78

def loopBody200_80 : HolLoopProg 64 :=
.seq loopBody200_79 loopBody200_1

def loopBody200_81 : HolLoopProg 64 :=
.mark loopBody200_80

def loopBody200_82 : HolLoopProg 64 :=
.seq loopBody200_77 loopBody200_81

def loopBody200_83 : HolLoopProg 64 :=
.mark loopBody200_82

def loopBody200_84 : HolLoopProg 64 :=
.seq loopBody200_75 loopBody200_83

def loopBody200_85 : HolLoopProg 64 :=
.mark loopBody200_84

def output200 : Nat × List Nat × HolLoopProg 64 :=
  (264, [0, 1, 2, 3, 4], loopBody200_85)
end InitECandidate.Proofs.FrontendStages.Loop
