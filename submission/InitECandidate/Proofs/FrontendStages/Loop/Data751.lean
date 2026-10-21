import InitECandidate.Proofs.FrontendStages.Loop.Translate735
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody751_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 128#64)

def loopBody751_1 : HolLoopProg 64 :=
.mark loopBody751_0

def loopBody751_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody751_3 : HolLoopProg 64 :=
.mark loopBody751_2

def loopBody751_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody751_5 : HolLoopProg 64 :=
.mark loopBody751_4

def loopBody751_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody751_7 : HolLoopProg 64 :=
.mark loopBody751_6

def loopBody751_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody751_5 loopBody751_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody751_9 : HolLoopProg 64 :=
.mark loopBody751_8

def loopBody751_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody751_11 : HolLoopProg 64 :=
.mark loopBody751_10

def loopBody751_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 519#64)

def loopBody751_13 : HolLoopProg 64 :=
.mark loopBody751_12

def loopBody751_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody751_15 : HolLoopProg 64 :=
.mark loopBody751_14

def loopBody751_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody751_17 : HolLoopProg 64 :=
.mark loopBody751_16

def loopBody751_18 : HolLoopProg 64 :=
.seq loopBody751_15 loopBody751_17

def loopBody751_19 : HolLoopProg 64 :=
.mark loopBody751_18

def loopBody751_20 : HolLoopProg 64 :=
.seq loopBody751_13 loopBody751_19

def loopBody751_21 : HolLoopProg 64 :=
.mark loopBody751_20

def loopBody751_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody751_21 loopBody751_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody751_23 : HolLoopProg 64 :=
.mark loopBody751_22

def loopBody751_24 : HolLoopProg 64 :=
.seq loopBody751_23 loopBody751_17

def loopBody751_25 : HolLoopProg 64 :=
.mark loopBody751_24

def loopBody751_26 : HolLoopProg 64 :=
.seq loopBody751_11 loopBody751_25

def loopBody751_27 : HolLoopProg 64 :=
.mark loopBody751_26

def loopBody751_28 : HolLoopProg 64 :=
.seq loopBody751_9 loopBody751_27

def loopBody751_29 : HolLoopProg 64 :=
.mark loopBody751_28

def loopBody751_30 : HolLoopProg 64 :=
.seq loopBody751_3 loopBody751_29

def loopBody751_31 : HolLoopProg 64 :=
.mark loopBody751_30

def loopBody751_32 : HolLoopProg 64 :=
.seq loopBody751_1 loopBody751_31

def loopBody751_33 : HolLoopProg 64 :=
.mark loopBody751_32

def loopBody751_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 400#64]),
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 1#64])
          (Flapjack.HolLoopExp.const 3#64)]))

def loopBody751_35 : HolLoopProg 64 :=
.mark loopBody751_34

def loopBody751_36 : HolLoopProg 64 :=
.seq loopBody751_35 loopBody751_19

def loopBody751_37 : HolLoopProg 64 :=
.mark loopBody751_36

def loopBody751_38 : HolLoopProg 64 :=
.seq loopBody751_33 loopBody751_37

def loopBody751_39 : HolLoopProg 64 :=
.mark loopBody751_38

def output751 : Nat × List Nat × HolLoopProg 64 :=
  (815, [0], loopBody751_39)
end InitECandidate.Proofs.FrontendStages.Loop
