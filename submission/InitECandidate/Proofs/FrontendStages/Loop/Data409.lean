import InitECandidate.Proofs.FrontendStages.Loop.Translate393
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody409_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody409_1 : HolLoopProg 64 :=
.mark loopBody409_0

def loopBody409_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody409_3 : HolLoopProg 64 :=
.mark loopBody409_2

def loopBody409_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody409_5 : HolLoopProg 64 :=
.mark loopBody409_4

def loopBody409_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody409_7 : HolLoopProg 64 :=
.mark loopBody409_6

def loopBody409_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody409_9 : HolLoopProg 64 :=
.mark loopBody409_8

def loopBody409_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody409_11 : HolLoopProg 64 :=
.mark loopBody409_10

def loopBody409_12 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 472) ([2, 3, 4, 5]) (some (2, loopBody409_11, loopBody409_1, (Flapjack.Spt.ln)))

def loopBody409_13 : HolLoopProg 64 :=
.mark loopBody409_12

def loopBody409_14 : HolLoopProg 64 :=
.seq loopBody409_13 loopBody409_1

def loopBody409_15 : HolLoopProg 64 :=
.mark loopBody409_14

def loopBody409_16 : HolLoopProg 64 :=
.seq loopBody409_9 loopBody409_15

def loopBody409_17 : HolLoopProg 64 :=
.mark loopBody409_16

def loopBody409_18 : HolLoopProg 64 :=
.seq loopBody409_7 loopBody409_17

def loopBody409_19 : HolLoopProg 64 :=
.mark loopBody409_18

def loopBody409_20 : HolLoopProg 64 :=
.seq loopBody409_5 loopBody409_19

def loopBody409_21 : HolLoopProg 64 :=
.mark loopBody409_20

def loopBody409_22 : HolLoopProg 64 :=
.seq loopBody409_3 loopBody409_21

def loopBody409_23 : HolLoopProg 64 :=
.mark loopBody409_22

def loopBody409_24 : HolLoopProg 64 :=
.seq loopBody409_1 loopBody409_23

def loopBody409_25 : HolLoopProg 64 :=
.mark loopBody409_24

def loopBody409_26 : HolLoopProg 64 :=
.seq loopBody409_1 loopBody409_25

def loopBody409_27 : HolLoopProg 64 :=
.mark loopBody409_26

def loopBody409_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody409_29 : HolLoopProg 64 :=
.mark loopBody409_28

def loopBody409_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody409_31 : HolLoopProg 64 :=
.mark loopBody409_30

def loopBody409_32 : HolLoopProg 64 :=
.seq loopBody409_31 loopBody409_1

def loopBody409_33 : HolLoopProg 64 :=
.mark loopBody409_32

def loopBody409_34 : HolLoopProg 64 :=
.seq loopBody409_29 loopBody409_33

def loopBody409_35 : HolLoopProg 64 :=
.mark loopBody409_34

def loopBody409_36 : HolLoopProg 64 :=
.seq loopBody409_27 loopBody409_35

def loopBody409_37 : HolLoopProg 64 :=
.mark loopBody409_36

def output409 : Nat × List Nat × HolLoopProg 64 :=
  (473, [0], loopBody409_37)
end InitECandidate.Proofs.FrontendStages.Loop
