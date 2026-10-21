import InitECandidate.Proofs.FrontendStages.Loop.Translate445
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody461_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody461_1 : HolLoopProg 64 :=
.mark loopBody461_0

def loopBody461_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody461_3 : HolLoopProg 64 :=
.mark loopBody461_2

def loopBody461_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody461_5 : HolLoopProg 64 :=
.mark loopBody461_4

def loopBody461_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody461_5, loopBody461_1, (Flapjack.Spt.ln)))

def loopBody461_7 : HolLoopProg 64 :=
.mark loopBody461_6

def loopBody461_8 : HolLoopProg 64 :=
.seq loopBody461_7 loopBody461_1

def loopBody461_9 : HolLoopProg 64 :=
.mark loopBody461_8

def loopBody461_10 : HolLoopProg 64 :=
.seq loopBody461_3 loopBody461_9

def loopBody461_11 : HolLoopProg 64 :=
.mark loopBody461_10

def loopBody461_12 : HolLoopProg 64 :=
.seq loopBody461_1 loopBody461_11

def loopBody461_13 : HolLoopProg 64 :=
.mark loopBody461_12

def loopBody461_14 : HolLoopProg 64 :=
.seq loopBody461_1 loopBody461_13

def loopBody461_15 : HolLoopProg 64 :=
.mark loopBody461_14

def loopBody461_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 486) ([2]) (some (2, loopBody461_5, loopBody461_1, (Flapjack.Spt.ln)))

def loopBody461_17 : HolLoopProg 64 :=
.mark loopBody461_16

def loopBody461_18 : HolLoopProg 64 :=
.seq loopBody461_17 loopBody461_1

def loopBody461_19 : HolLoopProg 64 :=
.mark loopBody461_18

def loopBody461_20 : HolLoopProg 64 :=
.seq loopBody461_3 loopBody461_19

def loopBody461_21 : HolLoopProg 64 :=
.mark loopBody461_20

def loopBody461_22 : HolLoopProg 64 :=
.seq loopBody461_1 loopBody461_21

def loopBody461_23 : HolLoopProg 64 :=
.mark loopBody461_22

def loopBody461_24 : HolLoopProg 64 :=
.seq loopBody461_1 loopBody461_23

def loopBody461_25 : HolLoopProg 64 :=
.mark loopBody461_24

def loopBody461_26 : HolLoopProg 64 :=
.seq loopBody461_15 loopBody461_25

def loopBody461_27 : HolLoopProg 64 :=
.mark loopBody461_26

def loopBody461_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody461_29 : HolLoopProg 64 :=
.mark loopBody461_28

def loopBody461_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody461_31 : HolLoopProg 64 :=
.mark loopBody461_30

def loopBody461_32 : HolLoopProg 64 :=
.seq loopBody461_31 loopBody461_1

def loopBody461_33 : HolLoopProg 64 :=
.mark loopBody461_32

def loopBody461_34 : HolLoopProg 64 :=
.seq loopBody461_29 loopBody461_33

def loopBody461_35 : HolLoopProg 64 :=
.mark loopBody461_34

def loopBody461_36 : HolLoopProg 64 :=
.seq loopBody461_27 loopBody461_35

def loopBody461_37 : HolLoopProg 64 :=
.mark loopBody461_36

def output461 : Nat × List Nat × HolLoopProg 64 :=
  (525, [], loopBody461_37)
end InitECandidate.Proofs.FrontendStages.Loop
