import InitECandidate.Proofs.FrontendStages.Loop.Translate406
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody422_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody422_1 : HolLoopProg 64 :=
.mark loopBody422_0

def loopBody422_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 0#64])

def loopBody422_3 : HolLoopProg 64 :=
.mark loopBody422_2

def loopBody422_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 0#64]),
      Flapjack.HolLoopExp.var 0])

def loopBody422_5 : HolLoopProg 64 :=
.mark loopBody422_4

def loopBody422_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody422_7 : HolLoopProg 64 :=
.mark loopBody422_6

def loopBody422_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody422_9 : HolLoopProg 64 :=
.mark loopBody422_8

def loopBody422_10 : HolLoopProg 64 :=
.seq loopBody422_9 loopBody422_1

def loopBody422_11 : HolLoopProg 64 :=
.mark loopBody422_10

def loopBody422_12 : HolLoopProg 64 :=
.seq loopBody422_7 loopBody422_11

def loopBody422_13 : HolLoopProg 64 :=
.mark loopBody422_12

def loopBody422_14 : HolLoopProg 64 :=
.seq loopBody422_13 loopBody422_1

def loopBody422_15 : HolLoopProg 64 :=
.mark loopBody422_14

def loopBody422_16 : HolLoopProg 64 :=
.seq loopBody422_5 loopBody422_15

def loopBody422_17 : HolLoopProg 64 :=
.mark loopBody422_16

def loopBody422_18 : HolLoopProg 64 :=
.seq loopBody422_1 loopBody422_17

def loopBody422_19 : HolLoopProg 64 :=
.mark loopBody422_18

def loopBody422_20 : HolLoopProg 64 :=
.seq loopBody422_3 loopBody422_19

def loopBody422_21 : HolLoopProg 64 :=
.mark loopBody422_20

def loopBody422_22 : HolLoopProg 64 :=
.seq loopBody422_1 loopBody422_21

def loopBody422_23 : HolLoopProg 64 :=
.mark loopBody422_22

def loopBody422_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody422_25 : HolLoopProg 64 :=
.mark loopBody422_24

def loopBody422_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody422_27 : HolLoopProg 64 :=
.mark loopBody422_26

def loopBody422_28 : HolLoopProg 64 :=
.seq loopBody422_27 loopBody422_1

def loopBody422_29 : HolLoopProg 64 :=
.mark loopBody422_28

def loopBody422_30 : HolLoopProg 64 :=
.seq loopBody422_25 loopBody422_29

def loopBody422_31 : HolLoopProg 64 :=
.mark loopBody422_30

def loopBody422_32 : HolLoopProg 64 :=
.seq loopBody422_23 loopBody422_31

def loopBody422_33 : HolLoopProg 64 :=
.mark loopBody422_32

def output422 : Nat × List Nat × HolLoopProg 64 :=
  (486, [0], loopBody422_33)
end InitECandidate.Proofs.FrontendStages.Loop
