import InitECandidate.Proofs.FrontendStages.Loop.Translate341
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody357_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody357_1 : HolLoopProg 64 :=
.mark loopBody357_0

def loopBody357_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 184#64]),
        Flapjack.HolLoopExp.const 56#64]))

def loopBody357_3 : HolLoopProg 64 :=
.mark loopBody357_2

def loopBody357_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody357_5 : HolLoopProg 64 :=
.mark loopBody357_4

def loopBody357_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody357_7 : HolLoopProg 64 :=
.mark loopBody357_6

def loopBody357_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody357_9 : HolLoopProg 64 :=
.mark loopBody357_8

def loopBody357_10 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 192) ([2, 3, 4]) (some (2, loopBody357_9, loopBody357_1, (Flapjack.Spt.ln)))

def loopBody357_11 : HolLoopProg 64 :=
.mark loopBody357_10

def loopBody357_12 : HolLoopProg 64 :=
.seq loopBody357_11 loopBody357_1

def loopBody357_13 : HolLoopProg 64 :=
.mark loopBody357_12

def loopBody357_14 : HolLoopProg 64 :=
.seq loopBody357_7 loopBody357_13

def loopBody357_15 : HolLoopProg 64 :=
.mark loopBody357_14

def loopBody357_16 : HolLoopProg 64 :=
.seq loopBody357_5 loopBody357_15

def loopBody357_17 : HolLoopProg 64 :=
.mark loopBody357_16

def loopBody357_18 : HolLoopProg 64 :=
.seq loopBody357_3 loopBody357_17

def loopBody357_19 : HolLoopProg 64 :=
.mark loopBody357_18

def loopBody357_20 : HolLoopProg 64 :=
.seq loopBody357_1 loopBody357_19

def loopBody357_21 : HolLoopProg 64 :=
.mark loopBody357_20

def loopBody357_22 : HolLoopProg 64 :=
.seq loopBody357_1 loopBody357_21

def loopBody357_23 : HolLoopProg 64 :=
.mark loopBody357_22

def loopBody357_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody357_25 : HolLoopProg 64 :=
.mark loopBody357_24

def loopBody357_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody357_27 : HolLoopProg 64 :=
.mark loopBody357_26

def loopBody357_28 : HolLoopProg 64 :=
.seq loopBody357_27 loopBody357_1

def loopBody357_29 : HolLoopProg 64 :=
.mark loopBody357_28

def loopBody357_30 : HolLoopProg 64 :=
.seq loopBody357_25 loopBody357_29

def loopBody357_31 : HolLoopProg 64 :=
.mark loopBody357_30

def loopBody357_32 : HolLoopProg 64 :=
.seq loopBody357_23 loopBody357_31

def loopBody357_33 : HolLoopProg 64 :=
.mark loopBody357_32

def output357 : Nat × List Nat × HolLoopProg 64 :=
  (421, [0], loopBody357_33)
end InitECandidate.Proofs.FrontendStages.Loop
