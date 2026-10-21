import InitECandidate.Proofs.FrontendStages.Loop.Translate527
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody543_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody543_1 : HolLoopProg 64 :=
.mark loopBody543_0

def loopBody543_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 168#64]))

def loopBody543_3 : HolLoopProg 64 :=
.mark loopBody543_2

def loopBody543_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 264#64]))

def loopBody543_5 : HolLoopProg 64 :=
.mark loopBody543_4

def loopBody543_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody543_7 : HolLoopProg 64 :=
.mark loopBody543_6

def loopBody543_8 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 194) ([2, 3]) (some (2, loopBody543_7, loopBody543_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody543_9 : HolLoopProg 64 :=
.mark loopBody543_8

def loopBody543_10 : HolLoopProg 64 :=
.seq loopBody543_9 loopBody543_1

def loopBody543_11 : HolLoopProg 64 :=
.mark loopBody543_10

def loopBody543_12 : HolLoopProg 64 :=
.seq loopBody543_5 loopBody543_11

def loopBody543_13 : HolLoopProg 64 :=
.mark loopBody543_12

def loopBody543_14 : HolLoopProg 64 :=
.seq loopBody543_3 loopBody543_13

def loopBody543_15 : HolLoopProg 64 :=
.mark loopBody543_14

def loopBody543_16 : HolLoopProg 64 :=
.seq loopBody543_1 loopBody543_15

def loopBody543_17 : HolLoopProg 64 :=
.mark loopBody543_16

def loopBody543_18 : HolLoopProg 64 :=
.seq loopBody543_1 loopBody543_17

def loopBody543_19 : HolLoopProg 64 :=
.mark loopBody543_18

def loopBody543_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 176#64]))

def loopBody543_21 : HolLoopProg 64 :=
.mark loopBody543_20

def loopBody543_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 272#64]))

def loopBody543_23 : HolLoopProg 64 :=
.mark loopBody543_22

def loopBody543_24 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 194) ([2, 3]) (some (2, loopBody543_7, loopBody543_1, (Flapjack.Spt.ln)))

def loopBody543_25 : HolLoopProg 64 :=
.mark loopBody543_24

def loopBody543_26 : HolLoopProg 64 :=
.seq loopBody543_25 loopBody543_1

def loopBody543_27 : HolLoopProg 64 :=
.mark loopBody543_26

def loopBody543_28 : HolLoopProg 64 :=
.seq loopBody543_23 loopBody543_27

def loopBody543_29 : HolLoopProg 64 :=
.mark loopBody543_28

def loopBody543_30 : HolLoopProg 64 :=
.seq loopBody543_21 loopBody543_29

def loopBody543_31 : HolLoopProg 64 :=
.mark loopBody543_30

def loopBody543_32 : HolLoopProg 64 :=
.seq loopBody543_1 loopBody543_31

def loopBody543_33 : HolLoopProg 64 :=
.mark loopBody543_32

def loopBody543_34 : HolLoopProg 64 :=
.seq loopBody543_1 loopBody543_33

def loopBody543_35 : HolLoopProg 64 :=
.mark loopBody543_34

def loopBody543_36 : HolLoopProg 64 :=
.seq loopBody543_19 loopBody543_35

def loopBody543_37 : HolLoopProg 64 :=
.mark loopBody543_36

def loopBody543_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody543_39 : HolLoopProg 64 :=
.mark loopBody543_38

def loopBody543_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody543_41 : HolLoopProg 64 :=
.mark loopBody543_40

def loopBody543_42 : HolLoopProg 64 :=
.seq loopBody543_41 loopBody543_1

def loopBody543_43 : HolLoopProg 64 :=
.mark loopBody543_42

def loopBody543_44 : HolLoopProg 64 :=
.seq loopBody543_39 loopBody543_43

def loopBody543_45 : HolLoopProg 64 :=
.mark loopBody543_44

def loopBody543_46 : HolLoopProg 64 :=
.seq loopBody543_37 loopBody543_45

def loopBody543_47 : HolLoopProg 64 :=
.mark loopBody543_46

def output543 : Nat × List Nat × HolLoopProg 64 :=
  (607, [0], loopBody543_47)
end InitECandidate.Proofs.FrontendStages.Loop
