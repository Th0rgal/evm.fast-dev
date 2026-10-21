import InitECandidate.Proofs.FrontendStages.Loop.Translate622
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody638_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.op Flapjack.BinOp.xor [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 6],
      Flapjack.HolLoopExp.op Flapjack.BinOp.xor [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 7],
      Flapjack.HolLoopExp.op Flapjack.BinOp.xor [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 8],
      Flapjack.HolLoopExp.op Flapjack.BinOp.xor [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.var 9],
      Flapjack.HolLoopExp.op Flapjack.BinOp.xor [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 10],
      Flapjack.HolLoopExp.op Flapjack.BinOp.xor [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.var 11]])

def loopBody638_1 : HolLoopProg 64 :=
.mark loopBody638_0

def loopBody638_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody638_3 : HolLoopProg 64 :=
.mark loopBody638_2

def loopBody638_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody638_5 : HolLoopProg 64 :=
.mark loopBody638_4

def loopBody638_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody638_7 : HolLoopProg 64 :=
.mark loopBody638_6

def loopBody638_8 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 13 (Flapjack.RegImm.reg 14) loopBody638_5 loopBody638_7 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))

def loopBody638_9 : HolLoopProg 64 :=
.mark loopBody638_8

def loopBody638_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 13)

def loopBody638_11 : HolLoopProg 64 :=
.mark loopBody638_10

def loopBody638_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody638_13 : HolLoopProg 64 :=
.mark loopBody638_12

def loopBody638_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [12]

def loopBody638_15 : HolLoopProg 64 :=
.mark loopBody638_14

def loopBody638_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody638_17 : HolLoopProg 64 :=
.mark loopBody638_16

def loopBody638_18 : HolLoopProg 64 :=
.seq loopBody638_15 loopBody638_17

def loopBody638_19 : HolLoopProg 64 :=
.mark loopBody638_18

def loopBody638_20 : HolLoopProg 64 :=
.seq loopBody638_13 loopBody638_19

def loopBody638_21 : HolLoopProg 64 :=
.mark loopBody638_20

def loopBody638_22 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody638_21 loopBody638_17 (Flapjack.Spt.ln)

def loopBody638_23 : HolLoopProg 64 :=
.mark loopBody638_22

def loopBody638_24 : HolLoopProg 64 :=
.seq loopBody638_23 loopBody638_17

def loopBody638_25 : HolLoopProg 64 :=
.mark loopBody638_24

def loopBody638_26 : HolLoopProg 64 :=
.seq loopBody638_11 loopBody638_25

def loopBody638_27 : HolLoopProg 64 :=
.mark loopBody638_26

def loopBody638_28 : HolLoopProg 64 :=
.seq loopBody638_9 loopBody638_27

def loopBody638_29 : HolLoopProg 64 :=
.mark loopBody638_28

def loopBody638_30 : HolLoopProg 64 :=
.seq loopBody638_3 loopBody638_29

def loopBody638_31 : HolLoopProg 64 :=
.mark loopBody638_30

def loopBody638_32 : HolLoopProg 64 :=
.seq loopBody638_1 loopBody638_31

def loopBody638_33 : HolLoopProg 64 :=
.mark loopBody638_32

def loopBody638_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody638_35 : HolLoopProg 64 :=
.mark loopBody638_34

def loopBody638_36 : HolLoopProg 64 :=
.seq loopBody638_35 loopBody638_19

def loopBody638_37 : HolLoopProg 64 :=
.mark loopBody638_36

def loopBody638_38 : HolLoopProg 64 :=
.seq loopBody638_33 loopBody638_37

def loopBody638_39 : HolLoopProg 64 :=
.mark loopBody638_38

def output638 : Nat × List Nat × HolLoopProg 64 :=
  (702, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], loopBody638_39)
end InitECandidate.Proofs.FrontendStages.Loop
