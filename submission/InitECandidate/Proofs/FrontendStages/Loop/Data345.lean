import InitECandidate.Proofs.FrontendStages.Loop.Translate329
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody345_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody345_1 : HolLoopProg 64 :=
.mark loopBody345_0

def loopBody345_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody345_3 : HolLoopProg 64 :=
.mark loopBody345_2

def loopBody345_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody345_5 : HolLoopProg 64 :=
.mark loopBody345_4

def loopBody345_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 402) ([2]) (some (2, loopBody345_5, loopBody345_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody345_7 : HolLoopProg 64 :=
.mark loopBody345_6

def loopBody345_8 : HolLoopProg 64 :=
.seq loopBody345_7 loopBody345_1

def loopBody345_9 : HolLoopProg 64 :=
.mark loopBody345_8

def loopBody345_10 : HolLoopProg 64 :=
.seq loopBody345_3 loopBody345_9

def loopBody345_11 : HolLoopProg 64 :=
.mark loopBody345_10

def loopBody345_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody345_13 : HolLoopProg 64 :=
.mark loopBody345_12

def loopBody345_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody345_15 : HolLoopProg 64 :=
.mark loopBody345_14

def loopBody345_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody345_17 : HolLoopProg 64 :=
.mark loopBody345_16

def loopBody345_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody345_19 : HolLoopProg 64 :=
.mark loopBody345_18

def loopBody345_20 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 3 (Flapjack.RegImm.reg 4) loopBody345_17 loopBody345_19 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody345_21 : HolLoopProg 64 :=
.mark loopBody345_20

def loopBody345_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody345_23 : HolLoopProg 64 :=
.mark loopBody345_22

def loopBody345_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody345_25 : HolLoopProg 64 :=
.mark loopBody345_24

def loopBody345_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody345_27 : HolLoopProg 64 :=
.mark loopBody345_26

def loopBody345_28 : HolLoopProg 64 :=
.seq loopBody345_27 loopBody345_1

def loopBody345_29 : HolLoopProg 64 :=
.mark loopBody345_28

def loopBody345_30 : HolLoopProg 64 :=
.seq loopBody345_25 loopBody345_29

def loopBody345_31 : HolLoopProg 64 :=
.mark loopBody345_30

def loopBody345_32 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.imm 0#64) loopBody345_31 loopBody345_1 (Flapjack.Spt.ln)

def loopBody345_33 : HolLoopProg 64 :=
.mark loopBody345_32

def loopBody345_34 : HolLoopProg 64 :=
.seq loopBody345_33 loopBody345_1

def loopBody345_35 : HolLoopProg 64 :=
.mark loopBody345_34

def loopBody345_36 : HolLoopProg 64 :=
.seq loopBody345_23 loopBody345_35

def loopBody345_37 : HolLoopProg 64 :=
.mark loopBody345_36

def loopBody345_38 : HolLoopProg 64 :=
.seq loopBody345_21 loopBody345_37

def loopBody345_39 : HolLoopProg 64 :=
.mark loopBody345_38

def loopBody345_40 : HolLoopProg 64 :=
.seq loopBody345_15 loopBody345_39

def loopBody345_41 : HolLoopProg 64 :=
.mark loopBody345_40

def loopBody345_42 : HolLoopProg 64 :=
.seq loopBody345_13 loopBody345_41

def loopBody345_43 : HolLoopProg 64 :=
.mark loopBody345_42

def loopBody345_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody345_45 : HolLoopProg 64 :=
.mark loopBody345_44

def loopBody345_46 : HolLoopProg 64 :=
.seq loopBody345_45 loopBody345_29

def loopBody345_47 : HolLoopProg 64 :=
.mark loopBody345_46

def loopBody345_48 : HolLoopProg 64 :=
.seq loopBody345_43 loopBody345_47

def loopBody345_49 : HolLoopProg 64 :=
.mark loopBody345_48

def loopBody345_50 : HolLoopProg 64 :=
.seq loopBody345_11 loopBody345_49

def loopBody345_51 : HolLoopProg 64 :=
.mark loopBody345_50

def loopBody345_52 : HolLoopProg 64 :=
.seq loopBody345_1 loopBody345_51

def loopBody345_53 : HolLoopProg 64 :=
.mark loopBody345_52

def loopBody345_54 : HolLoopProg 64 :=
.seq loopBody345_1 loopBody345_53

def loopBody345_55 : HolLoopProg 64 :=
.mark loopBody345_54

def output345 : Nat × List Nat × HolLoopProg 64 :=
  (409, [0], loopBody345_55)
end InitECandidate.Proofs.FrontendStages.Loop
