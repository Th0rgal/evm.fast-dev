import InitECandidate.Proofs.FrontendStages.Loop.Translate697
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody713_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody713_1 : HolLoopProg 64 :=
.mark loopBody713_0

def loopBody713_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody713_3 : HolLoopProg 64 :=
.mark loopBody713_2

def loopBody713_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody713_5 : HolLoopProg 64 :=
.mark loopBody713_4

def loopBody713_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody713_7 : HolLoopProg 64 :=
.mark loopBody713_6

def loopBody713_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody713_5 loopBody713_7 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody713_9 : HolLoopProg 64 :=
.mark loopBody713_8

def loopBody713_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody713_11 : HolLoopProg 64 :=
.mark loopBody713_10

def loopBody713_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody713_13 : HolLoopProg 64 :=
.mark loopBody713_12

def loopBody713_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody713_15 : HolLoopProg 64 :=
.mark loopBody713_14

def loopBody713_16 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 725) ([3, 4]) (some (3, loopBody713_15, loopBody713_13, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody713_17 : HolLoopProg 64 :=
.mark loopBody713_16

def loopBody713_18 : HolLoopProg 64 :=
.seq loopBody713_17 loopBody713_13

def loopBody713_19 : HolLoopProg 64 :=
.mark loopBody713_18

def loopBody713_20 : HolLoopProg 64 :=
.seq loopBody713_3 loopBody713_19

def loopBody713_21 : HolLoopProg 64 :=
.mark loopBody713_20

def loopBody713_22 : HolLoopProg 64 :=
.seq loopBody713_1 loopBody713_21

def loopBody713_23 : HolLoopProg 64 :=
.mark loopBody713_22

def loopBody713_24 : HolLoopProg 64 :=
.seq loopBody713_13 loopBody713_23

def loopBody713_25 : HolLoopProg 64 :=
.mark loopBody713_24

def loopBody713_26 : HolLoopProg 64 :=
.seq loopBody713_13 loopBody713_25

def loopBody713_27 : HolLoopProg 64 :=
.mark loopBody713_26

def loopBody713_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody713_29 : HolLoopProg 64 :=
.mark loopBody713_28

def loopBody713_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 192#64])

def loopBody713_31 : HolLoopProg 64 :=
.mark loopBody713_30

def loopBody713_32 : HolLoopProg 64 :=
.seq loopBody713_31 loopBody713_19

def loopBody713_33 : HolLoopProg 64 :=
.mark loopBody713_32

def loopBody713_34 : HolLoopProg 64 :=
.seq loopBody713_29 loopBody713_33

def loopBody713_35 : HolLoopProg 64 :=
.mark loopBody713_34

def loopBody713_36 : HolLoopProg 64 :=
.seq loopBody713_13 loopBody713_35

def loopBody713_37 : HolLoopProg 64 :=
.mark loopBody713_36

def loopBody713_38 : HolLoopProg 64 :=
.seq loopBody713_13 loopBody713_37

def loopBody713_39 : HolLoopProg 64 :=
.mark loopBody713_38

def loopBody713_40 : HolLoopProg 64 :=
.seq loopBody713_27 loopBody713_39

def loopBody713_41 : HolLoopProg 64 :=
.mark loopBody713_40

def loopBody713_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody713_41 loopBody713_13 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody713_43 : HolLoopProg 64 :=
.mark loopBody713_42

def loopBody713_44 : HolLoopProg 64 :=
.seq loopBody713_43 loopBody713_13

def loopBody713_45 : HolLoopProg 64 :=
.mark loopBody713_44

def loopBody713_46 : HolLoopProg 64 :=
.seq loopBody713_11 loopBody713_45

def loopBody713_47 : HolLoopProg 64 :=
.mark loopBody713_46

def loopBody713_48 : HolLoopProg 64 :=
.seq loopBody713_9 loopBody713_47

def loopBody713_49 : HolLoopProg 64 :=
.mark loopBody713_48

def loopBody713_50 : HolLoopProg 64 :=
.seq loopBody713_3 loopBody713_49

def loopBody713_51 : HolLoopProg 64 :=
.mark loopBody713_50

def loopBody713_52 : HolLoopProg 64 :=
.seq loopBody713_1 loopBody713_51

def loopBody713_53 : HolLoopProg 64 :=
.mark loopBody713_52

def loopBody713_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody713_55 : HolLoopProg 64 :=
.mark loopBody713_54

def loopBody713_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64])

def loopBody713_57 : HolLoopProg 64 :=
.mark loopBody713_56

def loopBody713_58 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 732) ([3, 4]) (some (3, loopBody713_15, loopBody713_13, (Flapjack.Spt.ln)))

def loopBody713_59 : HolLoopProg 64 :=
.mark loopBody713_58

def loopBody713_60 : HolLoopProg 64 :=
.seq loopBody713_59 loopBody713_13

def loopBody713_61 : HolLoopProg 64 :=
.mark loopBody713_60

def loopBody713_62 : HolLoopProg 64 :=
.seq loopBody713_57 loopBody713_61

def loopBody713_63 : HolLoopProg 64 :=
.mark loopBody713_62

def loopBody713_64 : HolLoopProg 64 :=
.seq loopBody713_55 loopBody713_63

def loopBody713_65 : HolLoopProg 64 :=
.mark loopBody713_64

def loopBody713_66 : HolLoopProg 64 :=
.seq loopBody713_13 loopBody713_65

def loopBody713_67 : HolLoopProg 64 :=
.mark loopBody713_66

def loopBody713_68 : HolLoopProg 64 :=
.seq loopBody713_13 loopBody713_67

def loopBody713_69 : HolLoopProg 64 :=
.mark loopBody713_68

def loopBody713_70 : HolLoopProg 64 :=
.seq loopBody713_53 loopBody713_69

def loopBody713_71 : HolLoopProg 64 :=
.mark loopBody713_70

def loopBody713_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody713_73 : HolLoopProg 64 :=
.mark loopBody713_72

def loopBody713_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody713_75 : HolLoopProg 64 :=
.mark loopBody713_74

def loopBody713_76 : HolLoopProg 64 :=
.seq loopBody713_75 loopBody713_13

def loopBody713_77 : HolLoopProg 64 :=
.mark loopBody713_76

def loopBody713_78 : HolLoopProg 64 :=
.seq loopBody713_73 loopBody713_77

def loopBody713_79 : HolLoopProg 64 :=
.mark loopBody713_78

def loopBody713_80 : HolLoopProg 64 :=
.seq loopBody713_71 loopBody713_79

def loopBody713_81 : HolLoopProg 64 :=
.mark loopBody713_80

def output713 : Nat × List Nat × HolLoopProg 64 :=
  (777, [0, 1], loopBody713_81)
end InitECandidate.Proofs.FrontendStages.Loop
