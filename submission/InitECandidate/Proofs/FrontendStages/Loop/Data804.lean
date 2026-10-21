import InitECandidate.Proofs.FrontendStages.Loop.Translate788
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody804_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody804_1 : HolLoopProg 64 :=
.mark loopBody804_0

def loopBody804_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody804_3 : HolLoopProg 64 :=
.mark loopBody804_2

def loopBody804_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody804_5 : HolLoopProg 64 :=
.mark loopBody804_4

def loopBody804_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody804_7 : HolLoopProg 64 :=
.mark loopBody804_6

def loopBody804_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody804_9 : HolLoopProg 64 :=
.mark loopBody804_8

def loopBody804_10 : HolLoopProg 64 :=
.seq loopBody804_9 loopBody804_1

def loopBody804_11 : HolLoopProg 64 :=
.mark loopBody804_10

def loopBody804_12 : HolLoopProg 64 :=
.seq loopBody804_11 loopBody804_1

def loopBody804_13 : HolLoopProg 64 :=
.mark loopBody804_12

def loopBody804_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody804_15 : HolLoopProg 64 :=
.mark loopBody804_14

def loopBody804_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.shMem Flapjack.WordMemOp.store8 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 2688614400#64, Flapjack.HolLoopExp.const 70#64])

def loopBody804_17 : HolLoopProg 64 :=
.mark loopBody804_16

def loopBody804_18 : HolLoopProg 64 :=
.seq loopBody804_17 loopBody804_1

def loopBody804_19 : HolLoopProg 64 :=
.mark loopBody804_18

def loopBody804_20 : HolLoopProg 64 :=
.seq loopBody804_15 loopBody804_19

def loopBody804_21 : HolLoopProg 64 :=
.mark loopBody804_20

def loopBody804_22 : HolLoopProg 64 :=
.seq loopBody804_1 loopBody804_21

def loopBody804_23 : HolLoopProg 64 :=
.mark loopBody804_22

def loopBody804_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 3#64)

def loopBody804_25 : HolLoopProg 64 :=
.mark loopBody804_24

def loopBody804_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody804_27 : HolLoopProg 64 :=
.mark loopBody804_26

def loopBody804_28 : HolLoopProg 64 :=
.seq loopBody804_27 loopBody804_1

def loopBody804_29 : HolLoopProg 64 :=
.mark loopBody804_28

def loopBody804_30 : HolLoopProg 64 :=
.seq loopBody804_29 loopBody804_1

def loopBody804_31 : HolLoopProg 64 :=
.mark loopBody804_30

def loopBody804_32 : HolLoopProg 64 :=
.seq loopBody804_25 loopBody804_31

def loopBody804_33 : HolLoopProg 64 :=
.mark loopBody804_32

def loopBody804_34 : HolLoopProg 64 :=
.seq loopBody804_1 loopBody804_33

def loopBody804_35 : HolLoopProg 64 :=
.mark loopBody804_34

def loopBody804_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 9#64)

def loopBody804_37 : HolLoopProg 64 :=
.mark loopBody804_36

def loopBody804_38 : HolLoopProg 64 :=
.seq loopBody804_37 loopBody804_5

def loopBody804_39 : HolLoopProg 64 :=
.mark loopBody804_38

def loopBody804_40 : HolLoopProg 64 :=
.seq loopBody804_35 loopBody804_39

def loopBody804_41 : HolLoopProg 64 :=
.mark loopBody804_40

def loopBody804_42 : HolLoopProg 64 :=
.seq loopBody804_23 loopBody804_41

def loopBody804_43 : HolLoopProg 64 :=
.mark loopBody804_42

def loopBody804_44 : HolLoopProg 64 :=
.seq loopBody804_13 loopBody804_43

def loopBody804_45 : HolLoopProg 64 :=
.mark loopBody804_44

def loopBody804_46 : HolLoopProg 64 :=
.seq loopBody804_7 loopBody804_45

def loopBody804_47 : HolLoopProg 64 :=
.mark loopBody804_46

def loopBody804_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.imm 1#64) loopBody804_5 loopBody804_47 (Flapjack.Spt.ln)

def loopBody804_49 : HolLoopProg 64 :=
.mark loopBody804_48

def loopBody804_50 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 867) ([3]) (some (3, loopBody804_49, loopBody804_1, (Flapjack.Spt.ln)))

def loopBody804_51 : HolLoopProg 64 :=
.mark loopBody804_50

def loopBody804_52 : HolLoopProg 64 :=
.seq loopBody804_51 loopBody804_1

def loopBody804_53 : HolLoopProg 64 :=
.mark loopBody804_52

def loopBody804_54 : HolLoopProg 64 :=
.seq loopBody804_3 loopBody804_53

def loopBody804_55 : HolLoopProg 64 :=
.mark loopBody804_54

def loopBody804_56 : HolLoopProg 64 :=
.seq loopBody804_1 loopBody804_55

def loopBody804_57 : HolLoopProg 64 :=
.mark loopBody804_56

def loopBody804_58 : HolLoopProg 64 :=
.seq loopBody804_1 loopBody804_57

def loopBody804_59 : HolLoopProg 64 :=
.mark loopBody804_58

def loopBody804_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody804_61 : HolLoopProg 64 :=
.mark loopBody804_60

def loopBody804_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody804_63 : HolLoopProg 64 :=
.mark loopBody804_62

def loopBody804_64 : HolLoopProg 64 :=
.seq loopBody804_63 loopBody804_1

def loopBody804_65 : HolLoopProg 64 :=
.mark loopBody804_64

def loopBody804_66 : HolLoopProg 64 :=
.seq loopBody804_61 loopBody804_65

def loopBody804_67 : HolLoopProg 64 :=
.mark loopBody804_66

def loopBody804_68 : HolLoopProg 64 :=
.seq loopBody804_59 loopBody804_67

def loopBody804_69 : HolLoopProg 64 :=
.mark loopBody804_68

def loopBody804_70 : HolLoopProg 64 :=
.seq loopBody804_1 loopBody804_69

def loopBody804_71 : HolLoopProg 64 :=
.mark loopBody804_70

def loopBody804_72 : HolLoopProg 64 :=
.seq loopBody804_1 loopBody804_71

def loopBody804_73 : HolLoopProg 64 :=
.mark loopBody804_72

def output804 : Nat × List Nat × HolLoopProg 64 :=
  (868, [0], loopBody804_73)
end InitECandidate.Proofs.FrontendStages.Loop
