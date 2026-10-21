import InitECandidate.Proofs.FrontendStages.Loop.Translate736
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody752_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 128#64)

def loopBody752_1 : HolLoopProg 64 :=
.mark loopBody752_0

def loopBody752_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody752_3 : HolLoopProg 64 :=
.mark loopBody752_2

def loopBody752_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody752_5 : HolLoopProg 64 :=
.mark loopBody752_4

def loopBody752_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody752_7 : HolLoopProg 64 :=
.mark loopBody752_6

def loopBody752_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 2 (Flapjack.RegImm.reg 3) loopBody752_5 loopBody752_7 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def loopBody752_9 : HolLoopProg 64 :=
.mark loopBody752_8

def loopBody752_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody752_11 : HolLoopProg 64 :=
.mark loopBody752_10

def loopBody752_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 524#64)

def loopBody752_13 : HolLoopProg 64 :=
.mark loopBody752_12

def loopBody752_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody752_15 : HolLoopProg 64 :=
.mark loopBody752_14

def loopBody752_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody752_17 : HolLoopProg 64 :=
.mark loopBody752_16

def loopBody752_18 : HolLoopProg 64 :=
.seq loopBody752_15 loopBody752_17

def loopBody752_19 : HolLoopProg 64 :=
.mark loopBody752_18

def loopBody752_20 : HolLoopProg 64 :=
.seq loopBody752_13 loopBody752_19

def loopBody752_21 : HolLoopProg 64 :=
.mark loopBody752_20

def loopBody752_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 0#64) loopBody752_21 loopBody752_17 (Flapjack.Spt.ls PUnit.unit)

def loopBody752_23 : HolLoopProg 64 :=
.mark loopBody752_22

def loopBody752_24 : HolLoopProg 64 :=
.seq loopBody752_23 loopBody752_17

def loopBody752_25 : HolLoopProg 64 :=
.mark loopBody752_24

def loopBody752_26 : HolLoopProg 64 :=
.seq loopBody752_11 loopBody752_25

def loopBody752_27 : HolLoopProg 64 :=
.mark loopBody752_26

def loopBody752_28 : HolLoopProg 64 :=
.seq loopBody752_9 loopBody752_27

def loopBody752_29 : HolLoopProg 64 :=
.mark loopBody752_28

def loopBody752_30 : HolLoopProg 64 :=
.seq loopBody752_3 loopBody752_29

def loopBody752_31 : HolLoopProg 64 :=
.mark loopBody752_30

def loopBody752_32 : HolLoopProg 64 :=
.seq loopBody752_1 loopBody752_31

def loopBody752_33 : HolLoopProg 64 :=
.mark loopBody752_32

def loopBody752_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 400#64]),
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
            [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 128#64, Flapjack.HolLoopExp.var 0],
              Flapjack.HolLoopExp.const 1#64])
          (Flapjack.HolLoopExp.const 3#64)]))

def loopBody752_35 : HolLoopProg 64 :=
.mark loopBody752_34

def loopBody752_36 : HolLoopProg 64 :=
.seq loopBody752_35 loopBody752_19

def loopBody752_37 : HolLoopProg 64 :=
.mark loopBody752_36

def loopBody752_38 : HolLoopProg 64 :=
.seq loopBody752_33 loopBody752_37

def loopBody752_39 : HolLoopProg 64 :=
.mark loopBody752_38

def output752 : Nat × List Nat × HolLoopProg 64 :=
  (816, [0], loopBody752_39)
end InitECandidate.Proofs.FrontendStages.Loop
