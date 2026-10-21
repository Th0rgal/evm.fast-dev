import InitECandidate.Proofs.FrontendStages.Loop.Translate787
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody803_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody803_1 : HolLoopProg 64 :=
.mark loopBody803_0

def loopBody803_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody803_3 : HolLoopProg 64 :=
.mark loopBody803_2

def loopBody803_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody803_5 : HolLoopProg 64 :=
.mark loopBody803_4

def loopBody803_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody803_7 : HolLoopProg 64 :=
.mark loopBody803_6

def loopBody803_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody803_9 : HolLoopProg 64 :=
.mark loopBody803_8

def loopBody803_10 : HolLoopProg 64 :=
.seq loopBody803_9 loopBody803_1

def loopBody803_11 : HolLoopProg 64 :=
.mark loopBody803_10

def loopBody803_12 : HolLoopProg 64 :=
.seq loopBody803_11 loopBody803_1

def loopBody803_13 : HolLoopProg 64 :=
.mark loopBody803_12

def loopBody803_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody803_15 : HolLoopProg 64 :=
.mark loopBody803_14

def loopBody803_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.shMem Flapjack.WordMemOp.store8 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 2688614400#64, Flapjack.HolLoopExp.const 70#64])

def loopBody803_17 : HolLoopProg 64 :=
.mark loopBody803_16

def loopBody803_18 : HolLoopProg 64 :=
.seq loopBody803_17 loopBody803_1

def loopBody803_19 : HolLoopProg 64 :=
.mark loopBody803_18

def loopBody803_20 : HolLoopProg 64 :=
.seq loopBody803_15 loopBody803_19

def loopBody803_21 : HolLoopProg 64 :=
.mark loopBody803_20

def loopBody803_22 : HolLoopProg 64 :=
.seq loopBody803_1 loopBody803_21

def loopBody803_23 : HolLoopProg 64 :=
.mark loopBody803_22

def loopBody803_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 2#64)

def loopBody803_25 : HolLoopProg 64 :=
.mark loopBody803_24

def loopBody803_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 3)

def loopBody803_27 : HolLoopProg 64 :=
.mark loopBody803_26

def loopBody803_28 : HolLoopProg 64 :=
.seq loopBody803_27 loopBody803_1

def loopBody803_29 : HolLoopProg 64 :=
.mark loopBody803_28

def loopBody803_30 : HolLoopProg 64 :=
.seq loopBody803_29 loopBody803_1

def loopBody803_31 : HolLoopProg 64 :=
.mark loopBody803_30

def loopBody803_32 : HolLoopProg 64 :=
.seq loopBody803_25 loopBody803_31

def loopBody803_33 : HolLoopProg 64 :=
.mark loopBody803_32

def loopBody803_34 : HolLoopProg 64 :=
.seq loopBody803_1 loopBody803_33

def loopBody803_35 : HolLoopProg 64 :=
.mark loopBody803_34

def loopBody803_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 9#64)

def loopBody803_37 : HolLoopProg 64 :=
.mark loopBody803_36

def loopBody803_38 : HolLoopProg 64 :=
.seq loopBody803_37 loopBody803_5

def loopBody803_39 : HolLoopProg 64 :=
.mark loopBody803_38

def loopBody803_40 : HolLoopProg 64 :=
.seq loopBody803_35 loopBody803_39

def loopBody803_41 : HolLoopProg 64 :=
.mark loopBody803_40

def loopBody803_42 : HolLoopProg 64 :=
.seq loopBody803_23 loopBody803_41

def loopBody803_43 : HolLoopProg 64 :=
.mark loopBody803_42

def loopBody803_44 : HolLoopProg 64 :=
.seq loopBody803_13 loopBody803_43

def loopBody803_45 : HolLoopProg 64 :=
.mark loopBody803_44

def loopBody803_46 : HolLoopProg 64 :=
.seq loopBody803_7 loopBody803_45

def loopBody803_47 : HolLoopProg 64 :=
.mark loopBody803_46

def loopBody803_48 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.imm 3#64) loopBody803_5 loopBody803_47 (Flapjack.Spt.ln)

def loopBody803_49 : HolLoopProg 64 :=
.mark loopBody803_48

def loopBody803_50 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 866) ([3]) (some (3, loopBody803_49, loopBody803_1, (Flapjack.Spt.ln)))

def loopBody803_51 : HolLoopProg 64 :=
.mark loopBody803_50

def loopBody803_52 : HolLoopProg 64 :=
.seq loopBody803_51 loopBody803_1

def loopBody803_53 : HolLoopProg 64 :=
.mark loopBody803_52

def loopBody803_54 : HolLoopProg 64 :=
.seq loopBody803_3 loopBody803_53

def loopBody803_55 : HolLoopProg 64 :=
.mark loopBody803_54

def loopBody803_56 : HolLoopProg 64 :=
.seq loopBody803_1 loopBody803_55

def loopBody803_57 : HolLoopProg 64 :=
.mark loopBody803_56

def loopBody803_58 : HolLoopProg 64 :=
.seq loopBody803_1 loopBody803_57

def loopBody803_59 : HolLoopProg 64 :=
.mark loopBody803_58

def loopBody803_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody803_61 : HolLoopProg 64 :=
.mark loopBody803_60

def loopBody803_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody803_63 : HolLoopProg 64 :=
.mark loopBody803_62

def loopBody803_64 : HolLoopProg 64 :=
.seq loopBody803_63 loopBody803_1

def loopBody803_65 : HolLoopProg 64 :=
.mark loopBody803_64

def loopBody803_66 : HolLoopProg 64 :=
.seq loopBody803_61 loopBody803_65

def loopBody803_67 : HolLoopProg 64 :=
.mark loopBody803_66

def loopBody803_68 : HolLoopProg 64 :=
.seq loopBody803_59 loopBody803_67

def loopBody803_69 : HolLoopProg 64 :=
.mark loopBody803_68

def loopBody803_70 : HolLoopProg 64 :=
.seq loopBody803_1 loopBody803_69

def loopBody803_71 : HolLoopProg 64 :=
.mark loopBody803_70

def loopBody803_72 : HolLoopProg 64 :=
.seq loopBody803_1 loopBody803_71

def loopBody803_73 : HolLoopProg 64 :=
.mark loopBody803_72

def output803 : Nat × List Nat × HolLoopProg 64 :=
  (867, [0], loopBody803_73)
end InitECandidate.Proofs.FrontendStages.Loop
