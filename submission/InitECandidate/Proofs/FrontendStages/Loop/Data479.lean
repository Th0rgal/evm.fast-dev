import InitECandidate.Proofs.FrontendStages.Loop.Translate463
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody479_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody479_1 : HolLoopProg 64 :=
.mark loopBody479_0

def loopBody479_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody479_3 : HolLoopProg 64 :=
.mark loopBody479_2

def loopBody479_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody479_5 : HolLoopProg 64 :=
.mark loopBody479_4

def loopBody479_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody479_7 : HolLoopProg 64 :=
.mark loopBody479_6

def loopBody479_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 388) ([3, 4]) (some (3, loopBody479_7, loopBody479_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody479_9 : HolLoopProg 64 :=
.mark loopBody479_8

def loopBody479_10 : HolLoopProg 64 :=
.seq loopBody479_9 loopBody479_1

def loopBody479_11 : HolLoopProg 64 :=
.mark loopBody479_10

def loopBody479_12 : HolLoopProg 64 :=
.seq loopBody479_5 loopBody479_11

def loopBody479_13 : HolLoopProg 64 :=
.mark loopBody479_12

def loopBody479_14 : HolLoopProg 64 :=
.seq loopBody479_3 loopBody479_13

def loopBody479_15 : HolLoopProg 64 :=
.mark loopBody479_14

def loopBody479_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 176#64]))

def loopBody479_17 : HolLoopProg 64 :=
.mark loopBody479_16

def loopBody479_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody479_19 : HolLoopProg 64 :=
.mark loopBody479_18

def loopBody479_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody479_21 : HolLoopProg 64 :=
.mark loopBody479_20

def loopBody479_22 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 187) ([4, 5]) (some (4, loopBody479_21, loopBody479_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody479_23 : HolLoopProg 64 :=
.mark loopBody479_22

def loopBody479_24 : HolLoopProg 64 :=
.seq loopBody479_23 loopBody479_1

def loopBody479_25 : HolLoopProg 64 :=
.mark loopBody479_24

def loopBody479_26 : HolLoopProg 64 :=
.seq loopBody479_19 loopBody479_25

def loopBody479_27 : HolLoopProg 64 :=
.mark loopBody479_26

def loopBody479_28 : HolLoopProg 64 :=
.seq loopBody479_17 loopBody479_27

def loopBody479_29 : HolLoopProg 64 :=
.mark loopBody479_28

def loopBody479_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody479_31 : HolLoopProg 64 :=
.mark loopBody479_30

def loopBody479_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody479_33 : HolLoopProg 64 :=
.mark loopBody479_32

def loopBody479_34 : HolLoopProg 64 :=
.seq loopBody479_33 loopBody479_1

def loopBody479_35 : HolLoopProg 64 :=
.mark loopBody479_34

def loopBody479_36 : HolLoopProg 64 :=
.seq loopBody479_31 loopBody479_35

def loopBody479_37 : HolLoopProg 64 :=
.mark loopBody479_36

def loopBody479_38 : HolLoopProg 64 :=
.seq loopBody479_29 loopBody479_37

def loopBody479_39 : HolLoopProg 64 :=
.mark loopBody479_38

def loopBody479_40 : HolLoopProg 64 :=
.seq loopBody479_1 loopBody479_39

def loopBody479_41 : HolLoopProg 64 :=
.mark loopBody479_40

def loopBody479_42 : HolLoopProg 64 :=
.seq loopBody479_1 loopBody479_41

def loopBody479_43 : HolLoopProg 64 :=
.mark loopBody479_42

def loopBody479_44 : HolLoopProg 64 :=
.seq loopBody479_15 loopBody479_43

def loopBody479_45 : HolLoopProg 64 :=
.mark loopBody479_44

def loopBody479_46 : HolLoopProg 64 :=
.seq loopBody479_1 loopBody479_45

def loopBody479_47 : HolLoopProg 64 :=
.mark loopBody479_46

def loopBody479_48 : HolLoopProg 64 :=
.seq loopBody479_1 loopBody479_47

def loopBody479_49 : HolLoopProg 64 :=
.mark loopBody479_48

def output479 : Nat × List Nat × HolLoopProg 64 :=
  (543, [0, 1], loopBody479_49)
end InitECandidate.Proofs.FrontendStages.Loop
