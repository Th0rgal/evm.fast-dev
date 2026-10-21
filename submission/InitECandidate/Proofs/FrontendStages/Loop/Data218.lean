import InitECandidate.Proofs.FrontendStages.Loop.Translate202
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody218_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody218_1 : HolLoopProg 64 :=
.mark loopBody218_0

def loopBody218_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.var 0)

def loopBody218_3 : HolLoopProg 64 :=
.mark loopBody218_2

def loopBody218_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 1)

def loopBody218_5 : HolLoopProg 64 :=
.mark loopBody218_4

def loopBody218_6 : HolLoopProg 64 :=
.seq loopBody218_5 loopBody218_1

def loopBody218_7 : HolLoopProg 64 :=
.mark loopBody218_6

def loopBody218_8 : HolLoopProg 64 :=
.seq loopBody218_7 loopBody218_1

def loopBody218_9 : HolLoopProg 64 :=
.mark loopBody218_8

def loopBody218_10 : HolLoopProg 64 :=
.seq loopBody218_3 loopBody218_9

def loopBody218_11 : HolLoopProg 64 :=
.mark loopBody218_10

def loopBody218_12 : HolLoopProg 64 :=
.seq loopBody218_1 loopBody218_11

def loopBody218_13 : HolLoopProg 64 :=
.mark loopBody218_12

def loopBody218_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 5#64)

def loopBody218_15 : HolLoopProg 64 :=
.mark loopBody218_14

def loopBody218_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 1

def loopBody218_17 : HolLoopProg 64 :=
.mark loopBody218_16

def loopBody218_18 : HolLoopProg 64 :=
.seq loopBody218_15 loopBody218_17

def loopBody218_19 : HolLoopProg 64 :=
.mark loopBody218_18

def loopBody218_20 : HolLoopProg 64 :=
.seq loopBody218_13 loopBody218_19

def loopBody218_21 : HolLoopProg 64 :=
.mark loopBody218_20

def loopBody218_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody218_23 : HolLoopProg 64 :=
.mark loopBody218_22

def loopBody218_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody218_25 : HolLoopProg 64 :=
.mark loopBody218_24

def loopBody218_26 : HolLoopProg 64 :=
.seq loopBody218_25 loopBody218_1

def loopBody218_27 : HolLoopProg 64 :=
.mark loopBody218_26

def loopBody218_28 : HolLoopProg 64 :=
.seq loopBody218_23 loopBody218_27

def loopBody218_29 : HolLoopProg 64 :=
.mark loopBody218_28

def loopBody218_30 : HolLoopProg 64 :=
.seq loopBody218_21 loopBody218_29

def loopBody218_31 : HolLoopProg 64 :=
.mark loopBody218_30

def output218 : Nat × List Nat × HolLoopProg 64 :=
  (282, [0], loopBody218_31)
end InitECandidate.Proofs.FrontendStages.Loop
