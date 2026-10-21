import InitECandidate.Proofs.FrontendStages.Loop.Translate663
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody679_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody679_1 : HolLoopProg 64 :=
.mark loopBody679_0

def loopBody679_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody679_3 : HolLoopProg 64 :=
.mark loopBody679_2

def loopBody679_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 288#64)

def loopBody679_5 : HolLoopProg 64 :=
.mark loopBody679_4

def loopBody679_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody679_7 : HolLoopProg 64 :=
.mark loopBody679_6

def loopBody679_8 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 78) ([2, 3]) (some (2, loopBody679_7, loopBody679_1, (Flapjack.Spt.ln)))

def loopBody679_9 : HolLoopProg 64 :=
.mark loopBody679_8

def loopBody679_10 : HolLoopProg 64 :=
.seq loopBody679_9 loopBody679_1

def loopBody679_11 : HolLoopProg 64 :=
.mark loopBody679_10

def loopBody679_12 : HolLoopProg 64 :=
.seq loopBody679_5 loopBody679_11

def loopBody679_13 : HolLoopProg 64 :=
.mark loopBody679_12

def loopBody679_14 : HolLoopProg 64 :=
.seq loopBody679_3 loopBody679_13

def loopBody679_15 : HolLoopProg 64 :=
.mark loopBody679_14

def loopBody679_16 : HolLoopProg 64 :=
.seq loopBody679_1 loopBody679_15

def loopBody679_17 : HolLoopProg 64 :=
.mark loopBody679_16

def loopBody679_18 : HolLoopProg 64 :=
.seq loopBody679_1 loopBody679_17

def loopBody679_19 : HolLoopProg 64 :=
.mark loopBody679_18

def loopBody679_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody679_21 : HolLoopProg 64 :=
.mark loopBody679_20

def loopBody679_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody679_23 : HolLoopProg 64 :=
.mark loopBody679_22

def loopBody679_24 : HolLoopProg 64 :=
.seq loopBody679_23 loopBody679_1

def loopBody679_25 : HolLoopProg 64 :=
.mark loopBody679_24

def loopBody679_26 : HolLoopProg 64 :=
.seq loopBody679_21 loopBody679_25

def loopBody679_27 : HolLoopProg 64 :=
.mark loopBody679_26

def loopBody679_28 : HolLoopProg 64 :=
.seq loopBody679_19 loopBody679_27

def loopBody679_29 : HolLoopProg 64 :=
.mark loopBody679_28

def output679 : Nat × List Nat × HolLoopProg 64 :=
  (743, [0], loopBody679_29)
end InitECandidate.Proofs.FrontendStages.Loop
