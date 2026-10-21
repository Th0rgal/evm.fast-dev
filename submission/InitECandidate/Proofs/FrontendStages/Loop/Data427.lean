import InitECandidate.Proofs.FrontendStages.Loop.Translate411
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody427_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody427_1 : HolLoopProg 64 :=
.mark loopBody427_0

def loopBody427_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody427_3 : HolLoopProg 64 :=
.mark loopBody427_2

def loopBody427_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody427_5 : HolLoopProg 64 :=
.mark loopBody427_4

def loopBody427_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 489) ([2]) (some (2, loopBody427_5, loopBody427_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody427_7 : HolLoopProg 64 :=
.mark loopBody427_6

def loopBody427_8 : HolLoopProg 64 :=
.seq loopBody427_7 loopBody427_1

def loopBody427_9 : HolLoopProg 64 :=
.mark loopBody427_8

def loopBody427_10 : HolLoopProg 64 :=
.seq loopBody427_3 loopBody427_9

def loopBody427_11 : HolLoopProg 64 :=
.mark loopBody427_10

def loopBody427_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody427_13 : HolLoopProg 64 :=
.mark loopBody427_12

def loopBody427_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody427_15 : HolLoopProg 64 :=
.mark loopBody427_14

def loopBody427_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody427_17 : HolLoopProg 64 :=
.mark loopBody427_16

def loopBody427_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody427_19 : HolLoopProg 64 :=
.mark loopBody427_18

def loopBody427_20 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 3 (Flapjack.RegImm.reg 4) loopBody427_17 loopBody427_19 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody427_21 : HolLoopProg 64 :=
.mark loopBody427_20

def loopBody427_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody427_23 : HolLoopProg 64 :=
.mark loopBody427_22

def loopBody427_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 100#64)

def loopBody427_25 : HolLoopProg 64 :=
.mark loopBody427_24

def loopBody427_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody427_27 : HolLoopProg 64 :=
.mark loopBody427_26

def loopBody427_28 : HolLoopProg 64 :=
.seq loopBody427_27 loopBody427_1

def loopBody427_29 : HolLoopProg 64 :=
.mark loopBody427_28

def loopBody427_30 : HolLoopProg 64 :=
.seq loopBody427_25 loopBody427_29

def loopBody427_31 : HolLoopProg 64 :=
.mark loopBody427_30

def loopBody427_32 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody427_31 loopBody427_1 (Flapjack.Spt.ln)

def loopBody427_33 : HolLoopProg 64 :=
.mark loopBody427_32

def loopBody427_34 : HolLoopProg 64 :=
.seq loopBody427_33 loopBody427_1

def loopBody427_35 : HolLoopProg 64 :=
.mark loopBody427_34

def loopBody427_36 : HolLoopProg 64 :=
.seq loopBody427_23 loopBody427_35

def loopBody427_37 : HolLoopProg 64 :=
.mark loopBody427_36

def loopBody427_38 : HolLoopProg 64 :=
.seq loopBody427_21 loopBody427_37

def loopBody427_39 : HolLoopProg 64 :=
.mark loopBody427_38

def loopBody427_40 : HolLoopProg 64 :=
.seq loopBody427_15 loopBody427_39

def loopBody427_41 : HolLoopProg 64 :=
.mark loopBody427_40

def loopBody427_42 : HolLoopProg 64 :=
.seq loopBody427_13 loopBody427_41

def loopBody427_43 : HolLoopProg 64 :=
.mark loopBody427_42

def loopBody427_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 3000#64)

def loopBody427_45 : HolLoopProg 64 :=
.mark loopBody427_44

def loopBody427_46 : HolLoopProg 64 :=
.seq loopBody427_45 loopBody427_29

def loopBody427_47 : HolLoopProg 64 :=
.mark loopBody427_46

def loopBody427_48 : HolLoopProg 64 :=
.seq loopBody427_43 loopBody427_47

def loopBody427_49 : HolLoopProg 64 :=
.mark loopBody427_48

def loopBody427_50 : HolLoopProg 64 :=
.seq loopBody427_11 loopBody427_49

def loopBody427_51 : HolLoopProg 64 :=
.mark loopBody427_50

def loopBody427_52 : HolLoopProg 64 :=
.seq loopBody427_1 loopBody427_51

def loopBody427_53 : HolLoopProg 64 :=
.mark loopBody427_52

def loopBody427_54 : HolLoopProg 64 :=
.seq loopBody427_1 loopBody427_53

def loopBody427_55 : HolLoopProg 64 :=
.mark loopBody427_54

def output427 : Nat × List Nat × HolLoopProg 64 :=
  (491, [0], loopBody427_55)
end InitECandidate.Proofs.FrontendStages.Loop
