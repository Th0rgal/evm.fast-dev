import InitECandidate.Proofs.FrontendStages.Loop.Translate671
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody687_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody687_1 : HolLoopProg 64 :=
.mark loopBody687_0

def loopBody687_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody687_3 : HolLoopProg 64 :=
.mark loopBody687_2

def loopBody687_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody687_5 : HolLoopProg 64 :=
.mark loopBody687_4

def loopBody687_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 576#64)

def loopBody687_7 : HolLoopProg 64 :=
.mark loopBody687_6

def loopBody687_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody687_9 : HolLoopProg 64 :=
.mark loopBody687_8

def loopBody687_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 77) ([3, 4, 5]) (some (3, loopBody687_9, loopBody687_1, (Flapjack.Spt.ln)))

def loopBody687_11 : HolLoopProg 64 :=
.mark loopBody687_10

def loopBody687_12 : HolLoopProg 64 :=
.seq loopBody687_11 loopBody687_1

def loopBody687_13 : HolLoopProg 64 :=
.mark loopBody687_12

def loopBody687_14 : HolLoopProg 64 :=
.seq loopBody687_7 loopBody687_13

def loopBody687_15 : HolLoopProg 64 :=
.mark loopBody687_14

def loopBody687_16 : HolLoopProg 64 :=
.seq loopBody687_5 loopBody687_15

def loopBody687_17 : HolLoopProg 64 :=
.mark loopBody687_16

def loopBody687_18 : HolLoopProg 64 :=
.seq loopBody687_3 loopBody687_17

def loopBody687_19 : HolLoopProg 64 :=
.mark loopBody687_18

def loopBody687_20 : HolLoopProg 64 :=
.seq loopBody687_1 loopBody687_19

def loopBody687_21 : HolLoopProg 64 :=
.mark loopBody687_20

def loopBody687_22 : HolLoopProg 64 :=
.seq loopBody687_1 loopBody687_21

def loopBody687_23 : HolLoopProg 64 :=
.mark loopBody687_22

def loopBody687_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody687_25 : HolLoopProg 64 :=
.mark loopBody687_24

def loopBody687_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody687_27 : HolLoopProg 64 :=
.mark loopBody687_26

def loopBody687_28 : HolLoopProg 64 :=
.seq loopBody687_27 loopBody687_1

def loopBody687_29 : HolLoopProg 64 :=
.mark loopBody687_28

def loopBody687_30 : HolLoopProg 64 :=
.seq loopBody687_25 loopBody687_29

def loopBody687_31 : HolLoopProg 64 :=
.mark loopBody687_30

def loopBody687_32 : HolLoopProg 64 :=
.seq loopBody687_23 loopBody687_31

def loopBody687_33 : HolLoopProg 64 :=
.mark loopBody687_32

def output687 : Nat × List Nat × HolLoopProg 64 :=
  (751, [0, 1], loopBody687_33)
end InitECandidate.Proofs.FrontendStages.Loop
