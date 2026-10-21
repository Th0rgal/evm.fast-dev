import InitECandidate.Proofs.FrontendStages.Loop.Translate593
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody609_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody609_1 : HolLoopProg 64 :=
.mark loopBody609_0

def loopBody609_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody609_3 : HolLoopProg 64 :=
.mark loopBody609_2

def loopBody609_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 0) (Flapjack.HolLoopExp.const 5#64))

def loopBody609_5 : HolLoopProg 64 :=
.mark loopBody609_4

def loopBody609_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 79) [3, 4, 5] none

def loopBody609_7 : HolLoopProg 64 :=
.mark loopBody609_6

def loopBody609_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody609_9 : HolLoopProg 64 :=
.mark loopBody609_8

def loopBody609_10 : HolLoopProg 64 :=
.seq loopBody609_7 loopBody609_9

def loopBody609_11 : HolLoopProg 64 :=
.mark loopBody609_10

def loopBody609_12 : HolLoopProg 64 :=
.seq loopBody609_5 loopBody609_11

def loopBody609_13 : HolLoopProg 64 :=
.mark loopBody609_12

def loopBody609_14 : HolLoopProg 64 :=
.seq loopBody609_3 loopBody609_13

def loopBody609_15 : HolLoopProg 64 :=
.mark loopBody609_14

def loopBody609_16 : HolLoopProg 64 :=
.seq loopBody609_1 loopBody609_15

def loopBody609_17 : HolLoopProg 64 :=
.mark loopBody609_16

def output609 : Nat × List Nat × HolLoopProg 64 :=
  (673, [0, 1, 2], loopBody609_17)
end InitECandidate.Proofs.FrontendStages.Loop
