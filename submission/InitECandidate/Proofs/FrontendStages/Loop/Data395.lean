import InitECandidate.Proofs.FrontendStages.Loop.Translate379
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody395_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody395_1 : HolLoopProg 64 :=
.mark loopBody395_0

def loopBody395_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 1])

def loopBody395_3 : HolLoopProg 64 :=
.mark loopBody395_2

def loopBody395_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody395_5 : HolLoopProg 64 :=
.mark loopBody395_4

def loopBody395_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody395_7 : HolLoopProg 64 :=
.mark loopBody395_6

def loopBody395_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody395_9 : HolLoopProg 64 :=
.mark loopBody395_8

def loopBody395_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody395_11 : HolLoopProg 64 :=
.mark loopBody395_10

def loopBody395_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.RegImm.reg 5) loopBody395_9 loopBody395_11 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody395_13 : HolLoopProg 64 :=
.mark loopBody395_12

def loopBody395_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody395_15 : HolLoopProg 64 :=
.mark loopBody395_14

def loopBody395_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 18446744073709551615#64)

def loopBody395_17 : HolLoopProg 64 :=
.mark loopBody395_16

def loopBody395_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody395_19 : HolLoopProg 64 :=
.mark loopBody395_18

def loopBody395_20 : HolLoopProg 64 :=
.seq loopBody395_19 loopBody395_1

def loopBody395_21 : HolLoopProg 64 :=
.mark loopBody395_20

def loopBody395_22 : HolLoopProg 64 :=
.seq loopBody395_17 loopBody395_21

def loopBody395_23 : HolLoopProg 64 :=
.mark loopBody395_22

def loopBody395_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody395_23 loopBody395_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody395_25 : HolLoopProg 64 :=
.mark loopBody395_24

def loopBody395_26 : HolLoopProg 64 :=
.seq loopBody395_25 loopBody395_1

def loopBody395_27 : HolLoopProg 64 :=
.mark loopBody395_26

def loopBody395_28 : HolLoopProg 64 :=
.seq loopBody395_15 loopBody395_27

def loopBody395_29 : HolLoopProg 64 :=
.mark loopBody395_28

def loopBody395_30 : HolLoopProg 64 :=
.seq loopBody395_13 loopBody395_29

def loopBody395_31 : HolLoopProg 64 :=
.mark loopBody395_30

def loopBody395_32 : HolLoopProg 64 :=
.seq loopBody395_7 loopBody395_31

def loopBody395_33 : HolLoopProg 64 :=
.mark loopBody395_32

def loopBody395_34 : HolLoopProg 64 :=
.seq loopBody395_5 loopBody395_33

def loopBody395_35 : HolLoopProg 64 :=
.mark loopBody395_34

def loopBody395_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody395_37 : HolLoopProg 64 :=
.mark loopBody395_36

def loopBody395_38 : HolLoopProg 64 :=
.seq loopBody395_37 loopBody395_21

def loopBody395_39 : HolLoopProg 64 :=
.mark loopBody395_38

def loopBody395_40 : HolLoopProg 64 :=
.seq loopBody395_35 loopBody395_39

def loopBody395_41 : HolLoopProg 64 :=
.mark loopBody395_40

def loopBody395_42 : HolLoopProg 64 :=
.seq loopBody395_3 loopBody395_41

def loopBody395_43 : HolLoopProg 64 :=
.mark loopBody395_42

def loopBody395_44 : HolLoopProg 64 :=
.seq loopBody395_1 loopBody395_43

def loopBody395_45 : HolLoopProg 64 :=
.mark loopBody395_44

def output395 : Nat × List Nat × HolLoopProg 64 :=
  (459, [0, 1], loopBody395_45)
end InitECandidate.Proofs.FrontendStages.Loop
