import InitECandidate.Proofs.FrontendStages.Loop.Translate378
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody394_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3])

def loopBody394_1 : HolLoopProg 64 :=
.mark loopBody394_0

def loopBody394_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody394_3 : HolLoopProg 64 :=
.mark loopBody394_2

def loopBody394_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody394_5 : HolLoopProg 64 :=
.mark loopBody394_4

def loopBody394_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody394_7 : HolLoopProg 64 :=
.mark loopBody394_6

def loopBody394_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.reg 6) loopBody394_5 loopBody394_7 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody394_9 : HolLoopProg 64 :=
.mark loopBody394_8

def loopBody394_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody394_11 : HolLoopProg 64 :=
.mark loopBody394_10

def loopBody394_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 18446744073709551615#64)

def loopBody394_13 : HolLoopProg 64 :=
.mark loopBody394_12

def loopBody394_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody394_15 : HolLoopProg 64 :=
.mark loopBody394_14

def loopBody394_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody394_17 : HolLoopProg 64 :=
.mark loopBody394_16

def loopBody394_18 : HolLoopProg 64 :=
.seq loopBody394_15 loopBody394_17

def loopBody394_19 : HolLoopProg 64 :=
.mark loopBody394_18

def loopBody394_20 : HolLoopProg 64 :=
.seq loopBody394_13 loopBody394_19

def loopBody394_21 : HolLoopProg 64 :=
.mark loopBody394_20

def loopBody394_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody394_21 loopBody394_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody394_23 : HolLoopProg 64 :=
.mark loopBody394_22

def loopBody394_24 : HolLoopProg 64 :=
.seq loopBody394_23 loopBody394_17

def loopBody394_25 : HolLoopProg 64 :=
.mark loopBody394_24

def loopBody394_26 : HolLoopProg 64 :=
.seq loopBody394_11 loopBody394_25

def loopBody394_27 : HolLoopProg 64 :=
.mark loopBody394_26

def loopBody394_28 : HolLoopProg 64 :=
.seq loopBody394_9 loopBody394_27

def loopBody394_29 : HolLoopProg 64 :=
.mark loopBody394_28

def loopBody394_30 : HolLoopProg 64 :=
.seq loopBody394_3 loopBody394_29

def loopBody394_31 : HolLoopProg 64 :=
.mark loopBody394_30

def loopBody394_32 : HolLoopProg 64 :=
.seq loopBody394_1 loopBody394_31

def loopBody394_33 : HolLoopProg 64 :=
.mark loopBody394_32

def loopBody394_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody394_35 : HolLoopProg 64 :=
.mark loopBody394_34

def loopBody394_36 : HolLoopProg 64 :=
.seq loopBody394_35 loopBody394_19

def loopBody394_37 : HolLoopProg 64 :=
.mark loopBody394_36

def loopBody394_38 : HolLoopProg 64 :=
.seq loopBody394_33 loopBody394_37

def loopBody394_39 : HolLoopProg 64 :=
.mark loopBody394_38

def output394 : Nat × List Nat × HolLoopProg 64 :=
  (458, [0, 1, 2, 3], loopBody394_39)
end InitECandidate.Proofs.FrontendStages.Loop
