import InitECandidate.Proofs.FrontendStages.Loop.Translate358
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody374_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody374_1 : HolLoopProg 64 :=
.mark loopBody374_0

def loopBody374_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody374_3 : HolLoopProg 64 :=
.mark loopBody374_2

def loopBody374_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody374_5 : HolLoopProg 64 :=
.mark loopBody374_4

def loopBody374_6 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 435) ([3]) (some (3, loopBody374_5, loopBody374_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody374_7 : HolLoopProg 64 :=
.mark loopBody374_6

def loopBody374_8 : HolLoopProg 64 :=
.seq loopBody374_7 loopBody374_1

def loopBody374_9 : HolLoopProg 64 :=
.mark loopBody374_8

def loopBody374_10 : HolLoopProg 64 :=
.seq loopBody374_3 loopBody374_9

def loopBody374_11 : HolLoopProg 64 :=
.mark loopBody374_10

def loopBody374_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.const 8#64]))

def loopBody374_13 : HolLoopProg 64 :=
.mark loopBody374_12

def loopBody374_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody374_15 : HolLoopProg 64 :=
.mark loopBody374_14

def loopBody374_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody374_17 : HolLoopProg 64 :=
.mark loopBody374_16

def loopBody374_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody374_19 : HolLoopProg 64 :=
.mark loopBody374_18

def loopBody374_20 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 192) ([4, 5, 6]) (some (4, loopBody374_19, loopBody374_1, (Flapjack.Spt.ln)))

def loopBody374_21 : HolLoopProg 64 :=
.mark loopBody374_20

def loopBody374_22 : HolLoopProg 64 :=
.seq loopBody374_21 loopBody374_1

def loopBody374_23 : HolLoopProg 64 :=
.mark loopBody374_22

def loopBody374_24 : HolLoopProg 64 :=
.seq loopBody374_17 loopBody374_23

def loopBody374_25 : HolLoopProg 64 :=
.mark loopBody374_24

def loopBody374_26 : HolLoopProg 64 :=
.seq loopBody374_15 loopBody374_25

def loopBody374_27 : HolLoopProg 64 :=
.mark loopBody374_26

def loopBody374_28 : HolLoopProg 64 :=
.seq loopBody374_13 loopBody374_27

def loopBody374_29 : HolLoopProg 64 :=
.mark loopBody374_28

def loopBody374_30 : HolLoopProg 64 :=
.seq loopBody374_1 loopBody374_29

def loopBody374_31 : HolLoopProg 64 :=
.mark loopBody374_30

def loopBody374_32 : HolLoopProg 64 :=
.seq loopBody374_1 loopBody374_31

def loopBody374_33 : HolLoopProg 64 :=
.mark loopBody374_32

def loopBody374_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody374_35 : HolLoopProg 64 :=
.mark loopBody374_34

def loopBody374_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody374_37 : HolLoopProg 64 :=
.mark loopBody374_36

def loopBody374_38 : HolLoopProg 64 :=
.seq loopBody374_37 loopBody374_1

def loopBody374_39 : HolLoopProg 64 :=
.mark loopBody374_38

def loopBody374_40 : HolLoopProg 64 :=
.seq loopBody374_35 loopBody374_39

def loopBody374_41 : HolLoopProg 64 :=
.mark loopBody374_40

def loopBody374_42 : HolLoopProg 64 :=
.seq loopBody374_33 loopBody374_41

def loopBody374_43 : HolLoopProg 64 :=
.mark loopBody374_42

def loopBody374_44 : HolLoopProg 64 :=
.seq loopBody374_11 loopBody374_43

def loopBody374_45 : HolLoopProg 64 :=
.mark loopBody374_44

def loopBody374_46 : HolLoopProg 64 :=
.seq loopBody374_1 loopBody374_45

def loopBody374_47 : HolLoopProg 64 :=
.mark loopBody374_46

def loopBody374_48 : HolLoopProg 64 :=
.seq loopBody374_1 loopBody374_47

def loopBody374_49 : HolLoopProg 64 :=
.mark loopBody374_48

def output374 : Nat × List Nat × HolLoopProg 64 :=
  (438, [0, 1], loopBody374_49)
end InitECandidate.Proofs.FrontendStages.Loop
