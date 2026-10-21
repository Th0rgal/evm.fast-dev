import InitECandidate.Proofs.FrontendStages.Loop.Translate371
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody387_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody387_1 : HolLoopProg 64 :=
.mark loopBody387_0

def loopBody387_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody387_3 : HolLoopProg 64 :=
.mark loopBody387_2

def loopBody387_4 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 450) ([]) (some (2, loopBody387_3, loopBody387_1, (Flapjack.Spt.ln)))

def loopBody387_5 : HolLoopProg 64 :=
.mark loopBody387_4

def loopBody387_6 : HolLoopProg 64 :=
.seq loopBody387_5 loopBody387_1

def loopBody387_7 : HolLoopProg 64 :=
.mark loopBody387_6

def loopBody387_8 : HolLoopProg 64 :=
.seq loopBody387_1 loopBody387_7

def loopBody387_9 : HolLoopProg 64 :=
.mark loopBody387_8

def loopBody387_10 : HolLoopProg 64 :=
.seq loopBody387_1 loopBody387_9

def loopBody387_11 : HolLoopProg 64 :=
.mark loopBody387_10

def loopBody387_12 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 429) ([]) (some (2, loopBody387_3, loopBody387_1, (Flapjack.Spt.ln)))

def loopBody387_13 : HolLoopProg 64 :=
.mark loopBody387_12

def loopBody387_14 : HolLoopProg 64 :=
.seq loopBody387_13 loopBody387_1

def loopBody387_15 : HolLoopProg 64 :=
.mark loopBody387_14

def loopBody387_16 : HolLoopProg 64 :=
.seq loopBody387_1 loopBody387_15

def loopBody387_17 : HolLoopProg 64 :=
.mark loopBody387_16

def loopBody387_18 : HolLoopProg 64 :=
.seq loopBody387_1 loopBody387_17

def loopBody387_19 : HolLoopProg 64 :=
.mark loopBody387_18

def loopBody387_20 : HolLoopProg 64 :=
.seq loopBody387_11 loopBody387_19

def loopBody387_21 : HolLoopProg 64 :=
.mark loopBody387_20

def loopBody387_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody387_23 : HolLoopProg 64 :=
.mark loopBody387_22

def loopBody387_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody387_25 : HolLoopProg 64 :=
.mark loopBody387_24

def loopBody387_26 : HolLoopProg 64 :=
.seq loopBody387_25 loopBody387_1

def loopBody387_27 : HolLoopProg 64 :=
.mark loopBody387_26

def loopBody387_28 : HolLoopProg 64 :=
.seq loopBody387_23 loopBody387_27

def loopBody387_29 : HolLoopProg 64 :=
.mark loopBody387_28

def loopBody387_30 : HolLoopProg 64 :=
.seq loopBody387_21 loopBody387_29

def loopBody387_31 : HolLoopProg 64 :=
.mark loopBody387_30

def output387 : Nat × List Nat × HolLoopProg 64 :=
  (451, [], loopBody387_31)
end InitECandidate.Proofs.FrontendStages.Loop
