import InitECandidate.Proofs.FrontendStages.Loop.Translate380
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody396_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody396_1 : HolLoopProg 64 :=
.mark loopBody396_0

def loopBody396_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 31#64])

def loopBody396_3 : HolLoopProg 64 :=
.mark loopBody396_2

def loopBody396_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody396_5 : HolLoopProg 64 :=
.mark loopBody396_4

def loopBody396_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody396_7 : HolLoopProg 64 :=
.mark loopBody396_6

def loopBody396_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody396_9 : HolLoopProg 64 :=
.mark loopBody396_8

def loopBody396_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody396_11 : HolLoopProg 64 :=
.mark loopBody396_10

def loopBody396_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody396_9 loopBody396_11 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody396_13 : HolLoopProg 64 :=
.mark loopBody396_12

def loopBody396_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody396_15 : HolLoopProg 64 :=
.mark loopBody396_14

def loopBody396_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody396_17 : HolLoopProg 64 :=
.mark loopBody396_16

def loopBody396_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody396_19 : HolLoopProg 64 :=
.mark loopBody396_18

def loopBody396_20 : HolLoopProg 64 :=
.seq loopBody396_19 loopBody396_1

def loopBody396_21 : HolLoopProg 64 :=
.mark loopBody396_20

def loopBody396_22 : HolLoopProg 64 :=
.seq loopBody396_17 loopBody396_21

def loopBody396_23 : HolLoopProg 64 :=
.mark loopBody396_22

def loopBody396_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody396_23 loopBody396_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody396_25 : HolLoopProg 64 :=
.mark loopBody396_24

def loopBody396_26 : HolLoopProg 64 :=
.seq loopBody396_25 loopBody396_1

def loopBody396_27 : HolLoopProg 64 :=
.mark loopBody396_26

def loopBody396_28 : HolLoopProg 64 :=
.seq loopBody396_15 loopBody396_27

def loopBody396_29 : HolLoopProg 64 :=
.mark loopBody396_28

def loopBody396_30 : HolLoopProg 64 :=
.seq loopBody396_13 loopBody396_29

def loopBody396_31 : HolLoopProg 64 :=
.mark loopBody396_30

def loopBody396_32 : HolLoopProg 64 :=
.seq loopBody396_7 loopBody396_31

def loopBody396_33 : HolLoopProg 64 :=
.mark loopBody396_32

def loopBody396_34 : HolLoopProg 64 :=
.seq loopBody396_5 loopBody396_33

def loopBody396_35 : HolLoopProg 64 :=
.mark loopBody396_34

def loopBody396_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody396_37 : HolLoopProg 64 :=
.mark loopBody396_36

def loopBody396_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 32#64, Flapjack.HolLoopExp.var 1])

def loopBody396_39 : HolLoopProg 64 :=
.mark loopBody396_38

def loopBody396_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody396_41 : HolLoopProg 64 :=
.mark loopBody396_40

def loopBody396_42 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 459) ([3, 4]) (some (3, loopBody396_41, loopBody396_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody396_43 : HolLoopProg 64 :=
.mark loopBody396_42

def loopBody396_44 : HolLoopProg 64 :=
.seq loopBody396_43 loopBody396_1

def loopBody396_45 : HolLoopProg 64 :=
.mark loopBody396_44

def loopBody396_46 : HolLoopProg 64 :=
.seq loopBody396_39 loopBody396_45

def loopBody396_47 : HolLoopProg 64 :=
.mark loopBody396_46

def loopBody396_48 : HolLoopProg 64 :=
.seq loopBody396_37 loopBody396_47

def loopBody396_49 : HolLoopProg 64 :=
.mark loopBody396_48

def loopBody396_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody396_51 : HolLoopProg 64 :=
.mark loopBody396_50

def loopBody396_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody396_53 : HolLoopProg 64 :=
.mark loopBody396_52

def loopBody396_54 : HolLoopProg 64 :=
.seq loopBody396_53 loopBody396_1

def loopBody396_55 : HolLoopProg 64 :=
.mark loopBody396_54

def loopBody396_56 : HolLoopProg 64 :=
.seq loopBody396_51 loopBody396_55

def loopBody396_57 : HolLoopProg 64 :=
.mark loopBody396_56

def loopBody396_58 : HolLoopProg 64 :=
.seq loopBody396_49 loopBody396_57

def loopBody396_59 : HolLoopProg 64 :=
.mark loopBody396_58

def loopBody396_60 : HolLoopProg 64 :=
.seq loopBody396_1 loopBody396_59

def loopBody396_61 : HolLoopProg 64 :=
.mark loopBody396_60

def loopBody396_62 : HolLoopProg 64 :=
.seq loopBody396_1 loopBody396_61

def loopBody396_63 : HolLoopProg 64 :=
.mark loopBody396_62

def loopBody396_64 : HolLoopProg 64 :=
.seq loopBody396_35 loopBody396_63

def loopBody396_65 : HolLoopProg 64 :=
.mark loopBody396_64

def loopBody396_66 : HolLoopProg 64 :=
.seq loopBody396_3 loopBody396_65

def loopBody396_67 : HolLoopProg 64 :=
.mark loopBody396_66

def loopBody396_68 : HolLoopProg 64 :=
.seq loopBody396_1 loopBody396_67

def loopBody396_69 : HolLoopProg 64 :=
.mark loopBody396_68

def output396 : Nat × List Nat × HolLoopProg 64 :=
  (460, [0], loopBody396_69)
end InitECandidate.Proofs.FrontendStages.Loop
