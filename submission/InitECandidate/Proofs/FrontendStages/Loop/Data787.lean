import InitECandidate.Proofs.FrontendStages.Loop.Translate771
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody787_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody787_1 : HolLoopProg 64 :=
.mark loopBody787_0

def loopBody787_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 3#64)

def loopBody787_3 : HolLoopProg 64 :=
.mark loopBody787_2

def loopBody787_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody787_5 : HolLoopProg 64 :=
.mark loopBody787_4

def loopBody787_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody787_7 : HolLoopProg 64 :=
.mark loopBody787_6

def loopBody787_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.RegImm.reg 3) loopBody787_5 loopBody787_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody787_9 : HolLoopProg 64 :=
.mark loopBody787_8

def loopBody787_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody787_11 : HolLoopProg 64 :=
.mark loopBody787_10

def loopBody787_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1#64)

def loopBody787_13 : HolLoopProg 64 :=
.mark loopBody787_12

def loopBody787_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody787_15 : HolLoopProg 64 :=
.mark loopBody787_14

def loopBody787_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody787_17 : HolLoopProg 64 :=
.mark loopBody787_16

def loopBody787_18 : HolLoopProg 64 :=
.seq loopBody787_15 loopBody787_17

def loopBody787_19 : HolLoopProg 64 :=
.mark loopBody787_18

def loopBody787_20 : HolLoopProg 64 :=
.seq loopBody787_13 loopBody787_19

def loopBody787_21 : HolLoopProg 64 :=
.mark loopBody787_20

def loopBody787_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody787_21 loopBody787_17 (Flapjack.Spt.ln)

def loopBody787_23 : HolLoopProg 64 :=
.mark loopBody787_22

def loopBody787_24 : HolLoopProg 64 :=
.seq loopBody787_23 loopBody787_17

def loopBody787_25 : HolLoopProg 64 :=
.mark loopBody787_24

def loopBody787_26 : HolLoopProg 64 :=
.seq loopBody787_11 loopBody787_25

def loopBody787_27 : HolLoopProg 64 :=
.mark loopBody787_26

def loopBody787_28 : HolLoopProg 64 :=
.seq loopBody787_9 loopBody787_27

def loopBody787_29 : HolLoopProg 64 :=
.mark loopBody787_28

def loopBody787_30 : HolLoopProg 64 :=
.seq loopBody787_3 loopBody787_29

def loopBody787_31 : HolLoopProg 64 :=
.mark loopBody787_30

def loopBody787_32 : HolLoopProg 64 :=
.seq loopBody787_1 loopBody787_31

def loopBody787_33 : HolLoopProg 64 :=
.mark loopBody787_32

def loopBody787_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody787_35 : HolLoopProg 64 :=
.mark loopBody787_34

def loopBody787_36 : HolLoopProg 64 :=
.seq loopBody787_35 loopBody787_19

def loopBody787_37 : HolLoopProg 64 :=
.mark loopBody787_36

def loopBody787_38 : HolLoopProg 64 :=
.seq loopBody787_33 loopBody787_37

def loopBody787_39 : HolLoopProg 64 :=
.mark loopBody787_38

def output787 : Nat × List Nat × HolLoopProg 64 :=
  (851, [0], loopBody787_39)
end InitECandidate.Proofs.FrontendStages.Loop
