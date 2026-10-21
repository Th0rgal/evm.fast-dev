import InitECandidate.Proofs.FrontendStages.Loop.Translate621
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody637_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3,
      Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 5])

def loopBody637_1 : HolLoopProg 64 :=
.mark loopBody637_0

def loopBody637_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody637_3 : HolLoopProg 64 :=
.mark loopBody637_2

def loopBody637_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody637_5 : HolLoopProg 64 :=
.mark loopBody637_4

def loopBody637_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody637_7 : HolLoopProg 64 :=
.mark loopBody637_6

def loopBody637_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 7 (Flapjack.RegImm.reg 8) loopBody637_5 loopBody637_7 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody637_9 : HolLoopProg 64 :=
.mark loopBody637_8

def loopBody637_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody637_11 : HolLoopProg 64 :=
.mark loopBody637_10

def loopBody637_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody637_13 : HolLoopProg 64 :=
.mark loopBody637_12

def loopBody637_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody637_15 : HolLoopProg 64 :=
.mark loopBody637_14

def loopBody637_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody637_17 : HolLoopProg 64 :=
.mark loopBody637_16

def loopBody637_18 : HolLoopProg 64 :=
.seq loopBody637_15 loopBody637_17

def loopBody637_19 : HolLoopProg 64 :=
.mark loopBody637_18

def loopBody637_20 : HolLoopProg 64 :=
.seq loopBody637_13 loopBody637_19

def loopBody637_21 : HolLoopProg 64 :=
.mark loopBody637_20

def loopBody637_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody637_21 loopBody637_17 (Flapjack.Spt.ln)

def loopBody637_23 : HolLoopProg 64 :=
.mark loopBody637_22

def loopBody637_24 : HolLoopProg 64 :=
.seq loopBody637_23 loopBody637_17

def loopBody637_25 : HolLoopProg 64 :=
.mark loopBody637_24

def loopBody637_26 : HolLoopProg 64 :=
.seq loopBody637_11 loopBody637_25

def loopBody637_27 : HolLoopProg 64 :=
.mark loopBody637_26

def loopBody637_28 : HolLoopProg 64 :=
.seq loopBody637_9 loopBody637_27

def loopBody637_29 : HolLoopProg 64 :=
.mark loopBody637_28

def loopBody637_30 : HolLoopProg 64 :=
.seq loopBody637_3 loopBody637_29

def loopBody637_31 : HolLoopProg 64 :=
.mark loopBody637_30

def loopBody637_32 : HolLoopProg 64 :=
.seq loopBody637_1 loopBody637_31

def loopBody637_33 : HolLoopProg 64 :=
.mark loopBody637_32

def loopBody637_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody637_35 : HolLoopProg 64 :=
.mark loopBody637_34

def loopBody637_36 : HolLoopProg 64 :=
.seq loopBody637_35 loopBody637_19

def loopBody637_37 : HolLoopProg 64 :=
.mark loopBody637_36

def loopBody637_38 : HolLoopProg 64 :=
.seq loopBody637_33 loopBody637_37

def loopBody637_39 : HolLoopProg 64 :=
.mark loopBody637_38

def output637 : Nat × List Nat × HolLoopProg 64 :=
  (701, [0, 1, 2, 3, 4, 5], loopBody637_39)
end InitECandidate.Proofs.FrontendStages.Loop
