import InitECandidate.Proofs.FrontendStages.Loop.Translate772
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody788_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody788_1 : HolLoopProg 64 :=
.mark loopBody788_0

def loopBody788_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 4#64)

def loopBody788_3 : HolLoopProg 64 :=
.mark loopBody788_2

def loopBody788_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody788_5 : HolLoopProg 64 :=
.mark loopBody788_4

def loopBody788_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody788_7 : HolLoopProg 64 :=
.mark loopBody788_6

def loopBody788_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.RegImm.reg 3) loopBody788_5 loopBody788_7 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody788_9 : HolLoopProg 64 :=
.mark loopBody788_8

def loopBody788_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody788_11 : HolLoopProg 64 :=
.mark loopBody788_10

def loopBody788_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 1#64)

def loopBody788_13 : HolLoopProg 64 :=
.mark loopBody788_12

def loopBody788_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody788_15 : HolLoopProg 64 :=
.mark loopBody788_14

def loopBody788_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody788_17 : HolLoopProg 64 :=
.mark loopBody788_16

def loopBody788_18 : HolLoopProg 64 :=
.seq loopBody788_15 loopBody788_17

def loopBody788_19 : HolLoopProg 64 :=
.mark loopBody788_18

def loopBody788_20 : HolLoopProg 64 :=
.seq loopBody788_13 loopBody788_19

def loopBody788_21 : HolLoopProg 64 :=
.mark loopBody788_20

def loopBody788_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody788_21 loopBody788_17 (Flapjack.Spt.ln)

def loopBody788_23 : HolLoopProg 64 :=
.mark loopBody788_22

def loopBody788_24 : HolLoopProg 64 :=
.seq loopBody788_23 loopBody788_17

def loopBody788_25 : HolLoopProg 64 :=
.mark loopBody788_24

def loopBody788_26 : HolLoopProg 64 :=
.seq loopBody788_11 loopBody788_25

def loopBody788_27 : HolLoopProg 64 :=
.mark loopBody788_26

def loopBody788_28 : HolLoopProg 64 :=
.seq loopBody788_9 loopBody788_27

def loopBody788_29 : HolLoopProg 64 :=
.mark loopBody788_28

def loopBody788_30 : HolLoopProg 64 :=
.seq loopBody788_3 loopBody788_29

def loopBody788_31 : HolLoopProg 64 :=
.mark loopBody788_30

def loopBody788_32 : HolLoopProg 64 :=
.seq loopBody788_1 loopBody788_31

def loopBody788_33 : HolLoopProg 64 :=
.mark loopBody788_32

def loopBody788_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody788_35 : HolLoopProg 64 :=
.mark loopBody788_34

def loopBody788_36 : HolLoopProg 64 :=
.seq loopBody788_35 loopBody788_19

def loopBody788_37 : HolLoopProg 64 :=
.mark loopBody788_36

def loopBody788_38 : HolLoopProg 64 :=
.seq loopBody788_33 loopBody788_37

def loopBody788_39 : HolLoopProg 64 :=
.mark loopBody788_38

def output788 : Nat × List Nat × HolLoopProg 64 :=
  (852, [0], loopBody788_39)
end InitECandidate.Proofs.FrontendStages.Loop
