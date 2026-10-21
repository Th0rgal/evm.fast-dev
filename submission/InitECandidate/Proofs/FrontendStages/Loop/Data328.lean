import InitECandidate.Proofs.FrontendStages.Loop.Translate312
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody328_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody328_1 : HolLoopProg 64 :=
.mark loopBody328_0

def loopBody328_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 176#64]),
        Flapjack.HolLoopExp.const 72#64]))

def loopBody328_3 : HolLoopProg 64 :=
.mark loopBody328_2

def loopBody328_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody328_5 : HolLoopProg 64 :=
.mark loopBody328_4

def loopBody328_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody328_7 : HolLoopProg 64 :=
.mark loopBody328_6

def loopBody328_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody328_9 : HolLoopProg 64 :=
.mark loopBody328_8

def loopBody328_10 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 192) ([2, 3, 4]) (some (2, loopBody328_9, loopBody328_1, (Flapjack.Spt.ln)))

def loopBody328_11 : HolLoopProg 64 :=
.mark loopBody328_10

def loopBody328_12 : HolLoopProg 64 :=
.seq loopBody328_11 loopBody328_1

def loopBody328_13 : HolLoopProg 64 :=
.mark loopBody328_12

def loopBody328_14 : HolLoopProg 64 :=
.seq loopBody328_7 loopBody328_13

def loopBody328_15 : HolLoopProg 64 :=
.mark loopBody328_14

def loopBody328_16 : HolLoopProg 64 :=
.seq loopBody328_5 loopBody328_15

def loopBody328_17 : HolLoopProg 64 :=
.mark loopBody328_16

def loopBody328_18 : HolLoopProg 64 :=
.seq loopBody328_3 loopBody328_17

def loopBody328_19 : HolLoopProg 64 :=
.mark loopBody328_18

def loopBody328_20 : HolLoopProg 64 :=
.seq loopBody328_1 loopBody328_19

def loopBody328_21 : HolLoopProg 64 :=
.mark loopBody328_20

def loopBody328_22 : HolLoopProg 64 :=
.seq loopBody328_1 loopBody328_21

def loopBody328_23 : HolLoopProg 64 :=
.mark loopBody328_22

def loopBody328_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody328_25 : HolLoopProg 64 :=
.mark loopBody328_24

def loopBody328_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody328_27 : HolLoopProg 64 :=
.mark loopBody328_26

def loopBody328_28 : HolLoopProg 64 :=
.seq loopBody328_27 loopBody328_1

def loopBody328_29 : HolLoopProg 64 :=
.mark loopBody328_28

def loopBody328_30 : HolLoopProg 64 :=
.seq loopBody328_25 loopBody328_29

def loopBody328_31 : HolLoopProg 64 :=
.mark loopBody328_30

def loopBody328_32 : HolLoopProg 64 :=
.seq loopBody328_23 loopBody328_31

def loopBody328_33 : HolLoopProg 64 :=
.mark loopBody328_32

def output328 : Nat × List Nat × HolLoopProg 64 :=
  (392, [0], loopBody328_33)
end InitECandidate.Proofs.FrontendStages.Loop
