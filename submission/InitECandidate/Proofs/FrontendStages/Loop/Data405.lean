import InitECandidate.Proofs.FrontendStages.Loop.Translate389
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody405_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody405_1 : HolLoopProg 64 :=
.mark loopBody405_0

def loopBody405_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 112#64]))

def loopBody405_3 : HolLoopProg 64 :=
.mark loopBody405_2

def loopBody405_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.op Flapjack.BinOp.sub
        [Flapjack.HolLoopExp.load
            (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64]),
          Flapjack.HolLoopExp.load
            (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 72#64])],
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])])

def loopBody405_5 : HolLoopProg 64 :=
.mark loopBody405_4

def loopBody405_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody405_7 : HolLoopProg 64 :=
.mark loopBody405_6

def loopBody405_8 : HolLoopProg 64 :=
.seq loopBody405_7 loopBody405_1

def loopBody405_9 : HolLoopProg 64 :=
.mark loopBody405_8

def loopBody405_10 : HolLoopProg 64 :=
.seq loopBody405_5 loopBody405_9

def loopBody405_11 : HolLoopProg 64 :=
.mark loopBody405_10

def loopBody405_12 : HolLoopProg 64 :=
.seq loopBody405_3 loopBody405_11

def loopBody405_13 : HolLoopProg 64 :=
.mark loopBody405_12

def loopBody405_14 : HolLoopProg 64 :=
.seq loopBody405_1 loopBody405_13

def loopBody405_15 : HolLoopProg 64 :=
.mark loopBody405_14

def output405 : Nat × List Nat × HolLoopProg 64 :=
  (469, [0], loopBody405_15)
end InitECandidate.Proofs.FrontendStages.Loop
