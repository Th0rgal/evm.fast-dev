import InitECandidate.Proofs.FrontendStages.Loop.Translate676
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody692_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody692_1 : HolLoopProg 64 :=
.mark loopBody692_0

def loopBody692_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody692_3 : HolLoopProg 64 :=
.mark loopBody692_2

def loopBody692_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody692_5 : HolLoopProg 64 :=
.mark loopBody692_4

def loopBody692_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody692_7 : HolLoopProg 64 :=
.mark loopBody692_6

def loopBody692_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 742) ([3, 4]) (some (3, loopBody692_7, loopBody692_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody692_9 : HolLoopProg 64 :=
.mark loopBody692_8

def loopBody692_10 : HolLoopProg 64 :=
.seq loopBody692_9 loopBody692_1

def loopBody692_11 : HolLoopProg 64 :=
.mark loopBody692_10

def loopBody692_12 : HolLoopProg 64 :=
.seq loopBody692_5 loopBody692_11

def loopBody692_13 : HolLoopProg 64 :=
.mark loopBody692_12

def loopBody692_14 : HolLoopProg 64 :=
.seq loopBody692_3 loopBody692_13

def loopBody692_15 : HolLoopProg 64 :=
.mark loopBody692_14

def loopBody692_16 : HolLoopProg 64 :=
.seq loopBody692_1 loopBody692_15

def loopBody692_17 : HolLoopProg 64 :=
.mark loopBody692_16

def loopBody692_18 : HolLoopProg 64 :=
.seq loopBody692_1 loopBody692_17

def loopBody692_19 : HolLoopProg 64 :=
.mark loopBody692_18

def loopBody692_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 288#64])

def loopBody692_21 : HolLoopProg 64 :=
.mark loopBody692_20

def loopBody692_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 288#64])

def loopBody692_23 : HolLoopProg 64 :=
.mark loopBody692_22

def loopBody692_24 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 747) ([3, 4]) (some (3, loopBody692_7, loopBody692_1, (Flapjack.Spt.ln)))

def loopBody692_25 : HolLoopProg 64 :=
.mark loopBody692_24

def loopBody692_26 : HolLoopProg 64 :=
.seq loopBody692_25 loopBody692_1

def loopBody692_27 : HolLoopProg 64 :=
.mark loopBody692_26

def loopBody692_28 : HolLoopProg 64 :=
.seq loopBody692_23 loopBody692_27

def loopBody692_29 : HolLoopProg 64 :=
.mark loopBody692_28

def loopBody692_30 : HolLoopProg 64 :=
.seq loopBody692_21 loopBody692_29

def loopBody692_31 : HolLoopProg 64 :=
.mark loopBody692_30

def loopBody692_32 : HolLoopProg 64 :=
.seq loopBody692_1 loopBody692_31

def loopBody692_33 : HolLoopProg 64 :=
.mark loopBody692_32

def loopBody692_34 : HolLoopProg 64 :=
.seq loopBody692_1 loopBody692_33

def loopBody692_35 : HolLoopProg 64 :=
.mark loopBody692_34

def loopBody692_36 : HolLoopProg 64 :=
.seq loopBody692_19 loopBody692_35

def loopBody692_37 : HolLoopProg 64 :=
.mark loopBody692_36

def loopBody692_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody692_39 : HolLoopProg 64 :=
.mark loopBody692_38

def loopBody692_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody692_41 : HolLoopProg 64 :=
.mark loopBody692_40

def loopBody692_42 : HolLoopProg 64 :=
.seq loopBody692_41 loopBody692_1

def loopBody692_43 : HolLoopProg 64 :=
.mark loopBody692_42

def loopBody692_44 : HolLoopProg 64 :=
.seq loopBody692_39 loopBody692_43

def loopBody692_45 : HolLoopProg 64 :=
.mark loopBody692_44

def loopBody692_46 : HolLoopProg 64 :=
.seq loopBody692_37 loopBody692_45

def loopBody692_47 : HolLoopProg 64 :=
.mark loopBody692_46

def output692 : Nat × List Nat × HolLoopProg 64 :=
  (756, [0, 1], loopBody692_47)
end InitECandidate.Proofs.FrontendStages.Loop
