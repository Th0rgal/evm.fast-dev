import InitECandidate.Proofs.FrontendStages.Loop.Translate789
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody805_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody805_1 : HolLoopProg 64 :=
.mark loopBody805_0

def loopBody805_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody805_3 : HolLoopProg 64 :=
.mark loopBody805_2

def loopBody805_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody805_5 : HolLoopProg 64 :=
.mark loopBody805_4

def loopBody805_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody805_7 : HolLoopProg 64 :=
.mark loopBody805_6

def loopBody805_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody805_9 : HolLoopProg 64 :=
.mark loopBody805_8

def loopBody805_10 : HolLoopProg 64 :=
.seq loopBody805_9 loopBody805_1

def loopBody805_11 : HolLoopProg 64 :=
.mark loopBody805_10

def loopBody805_12 : HolLoopProg 64 :=
.seq loopBody805_11 loopBody805_1

def loopBody805_13 : HolLoopProg 64 :=
.mark loopBody805_12

def loopBody805_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody805_15 : HolLoopProg 64 :=
.mark loopBody805_14

def loopBody805_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.shMem Flapjack.WordMemOp.store8 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 2688614400#64, Flapjack.HolLoopExp.const 70#64])

def loopBody805_17 : HolLoopProg 64 :=
.mark loopBody805_16

def loopBody805_18 : HolLoopProg 64 :=
.seq loopBody805_17 loopBody805_1

def loopBody805_19 : HolLoopProg 64 :=
.mark loopBody805_18

def loopBody805_20 : HolLoopProg 64 :=
.seq loopBody805_15 loopBody805_19

def loopBody805_21 : HolLoopProg 64 :=
.mark loopBody805_20

def loopBody805_22 : HolLoopProg 64 :=
.seq loopBody805_1 loopBody805_21

def loopBody805_23 : HolLoopProg 64 :=
.mark loopBody805_22

def loopBody805_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 4#64)

def loopBody805_25 : HolLoopProg 64 :=
.mark loopBody805_24

def loopBody805_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody805_27 : HolLoopProg 64 :=
.mark loopBody805_26

def loopBody805_28 : HolLoopProg 64 :=
.seq loopBody805_27 loopBody805_1

def loopBody805_29 : HolLoopProg 64 :=
.mark loopBody805_28

def loopBody805_30 : HolLoopProg 64 :=
.seq loopBody805_29 loopBody805_1

def loopBody805_31 : HolLoopProg 64 :=
.mark loopBody805_30

def loopBody805_32 : HolLoopProg 64 :=
.seq loopBody805_25 loopBody805_31

def loopBody805_33 : HolLoopProg 64 :=
.mark loopBody805_32

def loopBody805_34 : HolLoopProg 64 :=
.seq loopBody805_1 loopBody805_33

def loopBody805_35 : HolLoopProg 64 :=
.mark loopBody805_34

def loopBody805_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 9#64)

def loopBody805_37 : HolLoopProg 64 :=
.mark loopBody805_36

def loopBody805_38 : HolLoopProg 64 :=
.seq loopBody805_37 loopBody805_5

def loopBody805_39 : HolLoopProg 64 :=
.mark loopBody805_38

def loopBody805_40 : HolLoopProg 64 :=
.seq loopBody805_35 loopBody805_39

def loopBody805_41 : HolLoopProg 64 :=
.mark loopBody805_40

def loopBody805_42 : HolLoopProg 64 :=
.seq loopBody805_23 loopBody805_41

def loopBody805_43 : HolLoopProg 64 :=
.mark loopBody805_42

def loopBody805_44 : HolLoopProg 64 :=
.seq loopBody805_13 loopBody805_43

def loopBody805_45 : HolLoopProg 64 :=
.mark loopBody805_44

def loopBody805_46 : HolLoopProg 64 :=
.seq loopBody805_7 loopBody805_45

def loopBody805_47 : HolLoopProg 64 :=
.mark loopBody805_46

def loopBody805_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.imm 5#64) loopBody805_5 loopBody805_47 (Flapjack.Spt.ln)

def loopBody805_49 : HolLoopProg 64 :=
.mark loopBody805_48

def loopBody805_50 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 868) ([3]) (some (3, loopBody805_49, loopBody805_1, (Flapjack.Spt.ln)))

def loopBody805_51 : HolLoopProg 64 :=
.mark loopBody805_50

def loopBody805_52 : HolLoopProg 64 :=
.seq loopBody805_51 loopBody805_1

def loopBody805_53 : HolLoopProg 64 :=
.mark loopBody805_52

def loopBody805_54 : HolLoopProg 64 :=
.seq loopBody805_3 loopBody805_53

def loopBody805_55 : HolLoopProg 64 :=
.mark loopBody805_54

def loopBody805_56 : HolLoopProg 64 :=
.seq loopBody805_1 loopBody805_55

def loopBody805_57 : HolLoopProg 64 :=
.mark loopBody805_56

def loopBody805_58 : HolLoopProg 64 :=
.seq loopBody805_1 loopBody805_57

def loopBody805_59 : HolLoopProg 64 :=
.mark loopBody805_58

def loopBody805_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody805_61 : HolLoopProg 64 :=
.mark loopBody805_60

def loopBody805_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody805_63 : HolLoopProg 64 :=
.mark loopBody805_62

def loopBody805_64 : HolLoopProg 64 :=
.seq loopBody805_63 loopBody805_1

def loopBody805_65 : HolLoopProg 64 :=
.mark loopBody805_64

def loopBody805_66 : HolLoopProg 64 :=
.seq loopBody805_61 loopBody805_65

def loopBody805_67 : HolLoopProg 64 :=
.mark loopBody805_66

def loopBody805_68 : HolLoopProg 64 :=
.seq loopBody805_59 loopBody805_67

def loopBody805_69 : HolLoopProg 64 :=
.mark loopBody805_68

def loopBody805_70 : HolLoopProg 64 :=
.seq loopBody805_1 loopBody805_69

def loopBody805_71 : HolLoopProg 64 :=
.mark loopBody805_70

def loopBody805_72 : HolLoopProg 64 :=
.seq loopBody805_1 loopBody805_71

def loopBody805_73 : HolLoopProg 64 :=
.mark loopBody805_72

def output805 : Nat × List Nat × HolLoopProg 64 :=
  (869, [0], loopBody805_73)
end InitECandidate.Proofs.FrontendStages.Loop
