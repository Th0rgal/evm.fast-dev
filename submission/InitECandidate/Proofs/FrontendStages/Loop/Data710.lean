import InitECandidate.Proofs.FrontendStages.Loop.Translate694
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody710_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody710_1 : HolLoopProg 64 :=
.mark loopBody710_0

def loopBody710_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody710_3 : HolLoopProg 64 :=
.mark loopBody710_2

def loopBody710_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody710_5 : HolLoopProg 64 :=
.mark loopBody710_4

def loopBody710_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 727) ([2]) (some (2, loopBody710_5, loopBody710_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody710_7 : HolLoopProg 64 :=
.mark loopBody710_6

def loopBody710_8 : HolLoopProg 64 :=
.seq loopBody710_7 loopBody710_1

def loopBody710_9 : HolLoopProg 64 :=
.mark loopBody710_8

def loopBody710_10 : HolLoopProg 64 :=
.seq loopBody710_3 loopBody710_9

def loopBody710_11 : HolLoopProg 64 :=
.mark loopBody710_10

def loopBody710_12 : HolLoopProg 64 :=
.seq loopBody710_1 loopBody710_11

def loopBody710_13 : HolLoopProg 64 :=
.mark loopBody710_12

def loopBody710_14 : HolLoopProg 64 :=
.seq loopBody710_1 loopBody710_13

def loopBody710_15 : HolLoopProg 64 :=
.mark loopBody710_14

def loopBody710_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody710_17 : HolLoopProg 64 :=
.mark loopBody710_16

def loopBody710_18 : HolLoopProg 64 :=
.seq loopBody710_17 loopBody710_9

def loopBody710_19 : HolLoopProg 64 :=
.mark loopBody710_18

def loopBody710_20 : HolLoopProg 64 :=
.seq loopBody710_1 loopBody710_19

def loopBody710_21 : HolLoopProg 64 :=
.mark loopBody710_20

def loopBody710_22 : HolLoopProg 64 :=
.seq loopBody710_1 loopBody710_21

def loopBody710_23 : HolLoopProg 64 :=
.mark loopBody710_22

def loopBody710_24 : HolLoopProg 64 :=
.seq loopBody710_15 loopBody710_23

def loopBody710_25 : HolLoopProg 64 :=
.mark loopBody710_24

def loopBody710_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody710_27 : HolLoopProg 64 :=
.mark loopBody710_26

def loopBody710_28 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 726) ([2]) (some (2, loopBody710_5, loopBody710_1, (Flapjack.Spt.ln)))

def loopBody710_29 : HolLoopProg 64 :=
.mark loopBody710_28

def loopBody710_30 : HolLoopProg 64 :=
.seq loopBody710_29 loopBody710_1

def loopBody710_31 : HolLoopProg 64 :=
.mark loopBody710_30

def loopBody710_32 : HolLoopProg 64 :=
.seq loopBody710_27 loopBody710_31

def loopBody710_33 : HolLoopProg 64 :=
.mark loopBody710_32

def loopBody710_34 : HolLoopProg 64 :=
.seq loopBody710_1 loopBody710_33

def loopBody710_35 : HolLoopProg 64 :=
.mark loopBody710_34

def loopBody710_36 : HolLoopProg 64 :=
.seq loopBody710_1 loopBody710_35

def loopBody710_37 : HolLoopProg 64 :=
.mark loopBody710_36

def loopBody710_38 : HolLoopProg 64 :=
.seq loopBody710_25 loopBody710_37

def loopBody710_39 : HolLoopProg 64 :=
.mark loopBody710_38

def loopBody710_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody710_41 : HolLoopProg 64 :=
.mark loopBody710_40

def loopBody710_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody710_43 : HolLoopProg 64 :=
.mark loopBody710_42

def loopBody710_44 : HolLoopProg 64 :=
.seq loopBody710_43 loopBody710_1

def loopBody710_45 : HolLoopProg 64 :=
.mark loopBody710_44

def loopBody710_46 : HolLoopProg 64 :=
.seq loopBody710_41 loopBody710_45

def loopBody710_47 : HolLoopProg 64 :=
.mark loopBody710_46

def loopBody710_48 : HolLoopProg 64 :=
.seq loopBody710_39 loopBody710_47

def loopBody710_49 : HolLoopProg 64 :=
.mark loopBody710_48

def output710 : Nat × List Nat × HolLoopProg 64 :=
  (774, [0], loopBody710_49)
end InitECandidate.Proofs.FrontendStages.Loop
