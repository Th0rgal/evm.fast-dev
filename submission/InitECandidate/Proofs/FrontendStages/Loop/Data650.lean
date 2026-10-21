import InitECandidate.Proofs.FrontendStages.Loop.Translate634
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody650_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 0) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 63#64)])

def loopBody650_1 : HolLoopProg 64 :=
.mark loopBody650_0

def loopBody650_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 63#64)])

def loopBody650_3 : HolLoopProg 64 :=
.mark loopBody650_2

def loopBody650_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 2) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 63#64)])

def loopBody650_5 : HolLoopProg 64 :=
.mark loopBody650_4

def loopBody650_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 63#64)])

def loopBody650_7 : HolLoopProg 64 :=
.mark loopBody650_6

def loopBody650_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.or
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 1#64),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 63#64)])

def loopBody650_9 : HolLoopProg 64 :=
.mark loopBody650_8

def loopBody650_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 1#64))

def loopBody650_11 : HolLoopProg 64 :=
.mark loopBody650_10

def loopBody650_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6, 7, 8, 9, 10, 11]

def loopBody650_13 : HolLoopProg 64 :=
.mark loopBody650_12

def loopBody650_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody650_15 : HolLoopProg 64 :=
.mark loopBody650_14

def loopBody650_16 : HolLoopProg 64 :=
.seq loopBody650_13 loopBody650_15

def loopBody650_17 : HolLoopProg 64 :=
.mark loopBody650_16

def loopBody650_18 : HolLoopProg 64 :=
.seq loopBody650_11 loopBody650_17

def loopBody650_19 : HolLoopProg 64 :=
.mark loopBody650_18

def loopBody650_20 : HolLoopProg 64 :=
.seq loopBody650_9 loopBody650_19

def loopBody650_21 : HolLoopProg 64 :=
.mark loopBody650_20

def loopBody650_22 : HolLoopProg 64 :=
.seq loopBody650_7 loopBody650_21

def loopBody650_23 : HolLoopProg 64 :=
.mark loopBody650_22

def loopBody650_24 : HolLoopProg 64 :=
.seq loopBody650_5 loopBody650_23

def loopBody650_25 : HolLoopProg 64 :=
.mark loopBody650_24

def loopBody650_26 : HolLoopProg 64 :=
.seq loopBody650_3 loopBody650_25

def loopBody650_27 : HolLoopProg 64 :=
.mark loopBody650_26

def loopBody650_28 : HolLoopProg 64 :=
.seq loopBody650_1 loopBody650_27

def loopBody650_29 : HolLoopProg 64 :=
.mark loopBody650_28

def output650 : Nat × List Nat × HolLoopProg 64 :=
  (714, [0, 1, 2, 3, 4, 5], loopBody650_29)
end InitECandidate.Proofs.FrontendStages.Loop
