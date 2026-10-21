import InitECandidate.Proofs.FrontendStages.Loop.Translate381
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody397_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody397_1 : HolLoopProg 64 :=
.mark loopBody397_0

def loopBody397_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody397_3 : HolLoopProg 64 :=
.mark loopBody397_2

def loopBody397_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody397_5 : HolLoopProg 64 :=
.mark loopBody397_4

def loopBody397_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 460) ([2]) (some (2, loopBody397_5, loopBody397_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody397_7 : HolLoopProg 64 :=
.mark loopBody397_6

def loopBody397_8 : HolLoopProg 64 :=
.seq loopBody397_7 loopBody397_1

def loopBody397_9 : HolLoopProg 64 :=
.mark loopBody397_8

def loopBody397_10 : HolLoopProg 64 :=
.seq loopBody397_3 loopBody397_9

def loopBody397_11 : HolLoopProg 64 :=
.mark loopBody397_10

def loopBody397_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr (Flapjack.HolLoopExp.var 1) (Flapjack.HolLoopExp.const 5#64))

def loopBody397_13 : HolLoopProg 64 :=
.mark loopBody397_12

def loopBody397_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody397_15 : HolLoopProg 64 :=
.mark loopBody397_14

def loopBody397_16 : HolLoopProg 64 :=
.seq loopBody397_15 loopBody397_1

def loopBody397_17 : HolLoopProg 64 :=
.mark loopBody397_16

def loopBody397_18 : HolLoopProg 64 :=
.seq loopBody397_13 loopBody397_17

def loopBody397_19 : HolLoopProg 64 :=
.mark loopBody397_18

def loopBody397_20 : HolLoopProg 64 :=
.seq loopBody397_11 loopBody397_19

def loopBody397_21 : HolLoopProg 64 :=
.mark loopBody397_20

def loopBody397_22 : HolLoopProg 64 :=
.seq loopBody397_1 loopBody397_21

def loopBody397_23 : HolLoopProg 64 :=
.mark loopBody397_22

def loopBody397_24 : HolLoopProg 64 :=
.seq loopBody397_1 loopBody397_23

def loopBody397_25 : HolLoopProg 64 :=
.mark loopBody397_24

def output397 : Nat × List Nat × HolLoopProg 64 :=
  (461, [0], loopBody397_25)
end InitECandidate.Proofs.FrontendStages.Loop
