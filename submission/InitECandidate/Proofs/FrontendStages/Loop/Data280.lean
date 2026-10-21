import InitECandidate.Proofs.FrontendStages.Loop.Translate264
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody280_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody280_1 : HolLoopProg 64 :=
.mark loopBody280_0

def loopBody280_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody280_3 : HolLoopProg 64 :=
.mark loopBody280_2

def loopBody280_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody280_5 : HolLoopProg 64 :=
.mark loopBody280_4

def loopBody280_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody280_7 : HolLoopProg 64 :=
.mark loopBody280_6

def loopBody280_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1, 2, 3, 4]

def loopBody280_9 : HolLoopProg 64 :=
.mark loopBody280_8

def loopBody280_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody280_11 : HolLoopProg 64 :=
.mark loopBody280_10

def loopBody280_12 : HolLoopProg 64 :=
.seq loopBody280_9 loopBody280_11

def loopBody280_13 : HolLoopProg 64 :=
.mark loopBody280_12

def loopBody280_14 : HolLoopProg 64 :=
.seq loopBody280_7 loopBody280_13

def loopBody280_15 : HolLoopProg 64 :=
.mark loopBody280_14

def loopBody280_16 : HolLoopProg 64 :=
.seq loopBody280_5 loopBody280_15

def loopBody280_17 : HolLoopProg 64 :=
.mark loopBody280_16

def loopBody280_18 : HolLoopProg 64 :=
.seq loopBody280_3 loopBody280_17

def loopBody280_19 : HolLoopProg 64 :=
.mark loopBody280_18

def loopBody280_20 : HolLoopProg 64 :=
.seq loopBody280_1 loopBody280_19

def loopBody280_21 : HolLoopProg 64 :=
.mark loopBody280_20

def output280 : Nat × List Nat × HolLoopProg 64 :=
  (344, [0], loopBody280_21)
end InitECandidate.Proofs.FrontendStages.Loop
