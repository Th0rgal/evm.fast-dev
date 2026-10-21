import InitECandidate.Proofs.FrontendStages.Loop.Translate275
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody291_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody291_1 : HolLoopProg 64 :=
.mark loopBody291_0

def loopBody291_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody291_3 : HolLoopProg 64 :=
.mark loopBody291_2

def loopBody291_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody291_5 : HolLoopProg 64 :=
.mark loopBody291_4

def loopBody291_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody291_7 : HolLoopProg 64 :=
.mark loopBody291_6

def loopBody291_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody291_5 loopBody291_7 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody291_9 : HolLoopProg 64 :=
.mark loopBody291_8

def loopBody291_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody291_11 : HolLoopProg 64 :=
.mark loopBody291_10

def loopBody291_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody291_13 : HolLoopProg 64 :=
.mark loopBody291_12

def loopBody291_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 128#64)

def loopBody291_15 : HolLoopProg 64 :=
.mark loopBody291_14

def loopBody291_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.storeByte 2 3

def loopBody291_17 : HolLoopProg 64 :=
.mark loopBody291_16

def loopBody291_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody291_19 : HolLoopProg 64 :=
.mark loopBody291_18

def loopBody291_20 : HolLoopProg 64 :=
.seq loopBody291_17 loopBody291_19

def loopBody291_21 : HolLoopProg 64 :=
.mark loopBody291_20

def loopBody291_22 : HolLoopProg 64 :=
.seq loopBody291_15 loopBody291_21

def loopBody291_23 : HolLoopProg 64 :=
.mark loopBody291_22

def loopBody291_24 : HolLoopProg 64 :=
.seq loopBody291_13 loopBody291_23

def loopBody291_25 : HolLoopProg 64 :=
.mark loopBody291_24

def loopBody291_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody291_27 : HolLoopProg 64 :=
.mark loopBody291_26

def loopBody291_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody291_29 : HolLoopProg 64 :=
.mark loopBody291_28

def loopBody291_30 : HolLoopProg 64 :=
.seq loopBody291_29 loopBody291_19

def loopBody291_31 : HolLoopProg 64 :=
.mark loopBody291_30

def loopBody291_32 : HolLoopProg 64 :=
.seq loopBody291_27 loopBody291_31

def loopBody291_33 : HolLoopProg 64 :=
.mark loopBody291_32

def loopBody291_34 : HolLoopProg 64 :=
.seq loopBody291_25 loopBody291_33

def loopBody291_35 : HolLoopProg 64 :=
.mark loopBody291_34

def loopBody291_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody291_35 loopBody291_19 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody291_37 : HolLoopProg 64 :=
.mark loopBody291_36

def loopBody291_38 : HolLoopProg 64 :=
.seq loopBody291_37 loopBody291_19

def loopBody291_39 : HolLoopProg 64 :=
.mark loopBody291_38

def loopBody291_40 : HolLoopProg 64 :=
.seq loopBody291_11 loopBody291_39

def loopBody291_41 : HolLoopProg 64 :=
.mark loopBody291_40

def loopBody291_42 : HolLoopProg 64 :=
.seq loopBody291_9 loopBody291_41

def loopBody291_43 : HolLoopProg 64 :=
.mark loopBody291_42

def loopBody291_44 : HolLoopProg 64 :=
.seq loopBody291_3 loopBody291_43

def loopBody291_45 : HolLoopProg 64 :=
.mark loopBody291_44

def loopBody291_46 : HolLoopProg 64 :=
.seq loopBody291_1 loopBody291_45

def loopBody291_47 : HolLoopProg 64 :=
.mark loopBody291_46

def loopBody291_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 20#64)

def loopBody291_49 : HolLoopProg 64 :=
.mark loopBody291_48

def loopBody291_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 176) [2, 3, 4] none

def loopBody291_51 : HolLoopProg 64 :=
.mark loopBody291_50

def loopBody291_52 : HolLoopProg 64 :=
.seq loopBody291_51 loopBody291_19

def loopBody291_53 : HolLoopProg 64 :=
.mark loopBody291_52

def loopBody291_54 : HolLoopProg 64 :=
.seq loopBody291_49 loopBody291_53

def loopBody291_55 : HolLoopProg 64 :=
.mark loopBody291_54

def loopBody291_56 : HolLoopProg 64 :=
.seq loopBody291_1 loopBody291_55

def loopBody291_57 : HolLoopProg 64 :=
.mark loopBody291_56

def loopBody291_58 : HolLoopProg 64 :=
.seq loopBody291_13 loopBody291_57

def loopBody291_59 : HolLoopProg 64 :=
.mark loopBody291_58

def loopBody291_60 : HolLoopProg 64 :=
.seq loopBody291_47 loopBody291_59

def loopBody291_61 : HolLoopProg 64 :=
.mark loopBody291_60

def output291 : Nat × List Nat × HolLoopProg 64 :=
  (355, [0, 1], loopBody291_61)
end InitECandidate.Proofs.FrontendStages.Loop
