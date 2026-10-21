import InitECandidate.Proofs.FrontendStages.Loop.Translate269
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody285_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 352#64]))

def loopBody285_1 : HolLoopProg 64 :=
.mark loopBody285_0

def loopBody285_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 352#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody285_3 : HolLoopProg 64 :=
.mark loopBody285_2

def loopBody285_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 352#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody285_5 : HolLoopProg 64 :=
.mark loopBody285_4

def loopBody285_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 352#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody285_7 : HolLoopProg 64 :=
.mark loopBody285_6

def loopBody285_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1, 2, 3, 4]

def loopBody285_9 : HolLoopProg 64 :=
.mark loopBody285_8

def loopBody285_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody285_11 : HolLoopProg 64 :=
.mark loopBody285_10

def loopBody285_12 : HolLoopProg 64 :=
.seq loopBody285_9 loopBody285_11

def loopBody285_13 : HolLoopProg 64 :=
.mark loopBody285_12

def loopBody285_14 : HolLoopProg 64 :=
.seq loopBody285_7 loopBody285_13

def loopBody285_15 : HolLoopProg 64 :=
.mark loopBody285_14

def loopBody285_16 : HolLoopProg 64 :=
.seq loopBody285_5 loopBody285_15

def loopBody285_17 : HolLoopProg 64 :=
.mark loopBody285_16

def loopBody285_18 : HolLoopProg 64 :=
.seq loopBody285_3 loopBody285_17

def loopBody285_19 : HolLoopProg 64 :=
.mark loopBody285_18

def loopBody285_20 : HolLoopProg 64 :=
.seq loopBody285_1 loopBody285_19

def loopBody285_21 : HolLoopProg 64 :=
.mark loopBody285_20

def output285 : Nat × List Nat × HolLoopProg 64 :=
  (349, [0], loopBody285_21)
end InitECandidate.Proofs.FrontendStages.Loop
