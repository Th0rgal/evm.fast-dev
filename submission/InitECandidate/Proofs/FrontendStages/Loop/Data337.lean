import InitECandidate.Proofs.FrontendStages.Loop.Translate321
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody337_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody337_1 : HolLoopProg 64 :=
.mark loopBody337_0

def loopBody337_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody337_3 : HolLoopProg 64 :=
.mark loopBody337_2

def loopBody337_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody337_5 : HolLoopProg 64 :=
.mark loopBody337_4

def loopBody337_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 400) ([2]) (some (2, loopBody337_5, loopBody337_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody337_7 : HolLoopProg 64 :=
.mark loopBody337_6

def loopBody337_8 : HolLoopProg 64 :=
.seq loopBody337_7 loopBody337_1

def loopBody337_9 : HolLoopProg 64 :=
.mark loopBody337_8

def loopBody337_10 : HolLoopProg 64 :=
.seq loopBody337_3 loopBody337_9

def loopBody337_11 : HolLoopProg 64 :=
.mark loopBody337_10

def loopBody337_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody337_13 : HolLoopProg 64 :=
.mark loopBody337_12

def loopBody337_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody337_15 : HolLoopProg 64 :=
.mark loopBody337_14

def loopBody337_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody337_17 : HolLoopProg 64 :=
.mark loopBody337_16

def loopBody337_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody337_19 : HolLoopProg 64 :=
.mark loopBody337_18

def loopBody337_20 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody337_17 loopBody337_19 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody337_21 : HolLoopProg 64 :=
.mark loopBody337_20

def loopBody337_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody337_23 : HolLoopProg 64 :=
.mark loopBody337_22

def loopBody337_24 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 390) ([]) (some (2, loopBody337_5, loopBody337_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody337_25 : HolLoopProg 64 :=
.mark loopBody337_24

def loopBody337_26 : HolLoopProg 64 :=
.seq loopBody337_25 loopBody337_1

def loopBody337_27 : HolLoopProg 64 :=
.mark loopBody337_26

def loopBody337_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody337_27 loopBody337_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))

def loopBody337_29 : HolLoopProg 64 :=
.mark loopBody337_28

def loopBody337_30 : HolLoopProg 64 :=
.seq loopBody337_29 loopBody337_1

def loopBody337_31 : HolLoopProg 64 :=
.mark loopBody337_30

def loopBody337_32 : HolLoopProg 64 :=
.seq loopBody337_23 loopBody337_31

def loopBody337_33 : HolLoopProg 64 :=
.mark loopBody337_32

def loopBody337_34 : HolLoopProg 64 :=
.seq loopBody337_21 loopBody337_33

def loopBody337_35 : HolLoopProg 64 :=
.mark loopBody337_34

def loopBody337_36 : HolLoopProg 64 :=
.seq loopBody337_15 loopBody337_35

def loopBody337_37 : HolLoopProg 64 :=
.mark loopBody337_36

def loopBody337_38 : HolLoopProg 64 :=
.seq loopBody337_13 loopBody337_37

def loopBody337_39 : HolLoopProg 64 :=
.mark loopBody337_38

def loopBody337_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody337_41 : HolLoopProg 64 :=
.mark loopBody337_40

def loopBody337_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody337_43 : HolLoopProg 64 :=
.mark loopBody337_42

def loopBody337_44 : HolLoopProg 64 :=
.seq loopBody337_43 loopBody337_1

def loopBody337_45 : HolLoopProg 64 :=
.mark loopBody337_44

def loopBody337_46 : HolLoopProg 64 :=
.seq loopBody337_41 loopBody337_45

def loopBody337_47 : HolLoopProg 64 :=
.mark loopBody337_46

def loopBody337_48 : HolLoopProg 64 :=
.seq loopBody337_39 loopBody337_47

def loopBody337_49 : HolLoopProg 64 :=
.mark loopBody337_48

def loopBody337_50 : HolLoopProg 64 :=
.seq loopBody337_11 loopBody337_49

def loopBody337_51 : HolLoopProg 64 :=
.mark loopBody337_50

def loopBody337_52 : HolLoopProg 64 :=
.seq loopBody337_1 loopBody337_51

def loopBody337_53 : HolLoopProg 64 :=
.mark loopBody337_52

def loopBody337_54 : HolLoopProg 64 :=
.seq loopBody337_1 loopBody337_53

def loopBody337_55 : HolLoopProg 64 :=
.mark loopBody337_54

def output337 : Nat × List Nat × HolLoopProg 64 :=
  (401, [0], loopBody337_55)
end InitECandidate.Proofs.FrontendStages.Loop
