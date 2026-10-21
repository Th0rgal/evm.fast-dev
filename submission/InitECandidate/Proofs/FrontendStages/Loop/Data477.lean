import InitECandidate.Proofs.FrontendStages.Loop.Translate461
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody477_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody477_1 : HolLoopProg 64 :=
.mark loopBody477_0

def loopBody477_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 88#64]))

def loopBody477_3 : HolLoopProg 64 :=
.mark loopBody477_2

def loopBody477_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 8#64)

def loopBody477_5 : HolLoopProg 64 :=
.mark loopBody477_4

def loopBody477_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody477_7 : HolLoopProg 64 :=
.mark loopBody477_6

def loopBody477_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 433) ([3, 4]) (some (3, loopBody477_7, loopBody477_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))

def loopBody477_9 : HolLoopProg 64 :=
.mark loopBody477_8

def loopBody477_10 : HolLoopProg 64 :=
.seq loopBody477_9 loopBody477_1

def loopBody477_11 : HolLoopProg 64 :=
.mark loopBody477_10

def loopBody477_12 : HolLoopProg 64 :=
.seq loopBody477_5 loopBody477_11

def loopBody477_13 : HolLoopProg 64 :=
.mark loopBody477_12

def loopBody477_14 : HolLoopProg 64 :=
.seq loopBody477_3 loopBody477_13

def loopBody477_15 : HolLoopProg 64 :=
.mark loopBody477_14

def loopBody477_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody477_17 : HolLoopProg 64 :=
.mark loopBody477_16

def loopBody477_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody477_19 : HolLoopProg 64 :=
.mark loopBody477_18

def loopBody477_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody477_21 : HolLoopProg 64 :=
.mark loopBody477_20

def loopBody477_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 3) 5

def loopBody477_23 : HolLoopProg 64 :=
.mark loopBody477_22

def loopBody477_24 : HolLoopProg 64 :=
.seq loopBody477_23 loopBody477_1

def loopBody477_25 : HolLoopProg 64 :=
.mark loopBody477_24

def loopBody477_26 : HolLoopProg 64 :=
.seq loopBody477_21 loopBody477_25

def loopBody477_27 : HolLoopProg 64 :=
.mark loopBody477_26

def loopBody477_28 : HolLoopProg 64 :=
.seq loopBody477_27 loopBody477_1

def loopBody477_29 : HolLoopProg 64 :=
.mark loopBody477_28

def loopBody477_30 : HolLoopProg 64 :=
.seq loopBody477_19 loopBody477_29

def loopBody477_31 : HolLoopProg 64 :=
.mark loopBody477_30

def loopBody477_32 : HolLoopProg 64 :=
.seq loopBody477_1 loopBody477_31

def loopBody477_33 : HolLoopProg 64 :=
.mark loopBody477_32

def loopBody477_34 : HolLoopProg 64 :=
.seq loopBody477_17 loopBody477_33

def loopBody477_35 : HolLoopProg 64 :=
.mark loopBody477_34

def loopBody477_36 : HolLoopProg 64 :=
.seq loopBody477_1 loopBody477_35

def loopBody477_37 : HolLoopProg 64 :=
.mark loopBody477_36

def loopBody477_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody477_39 : HolLoopProg 64 :=
.mark loopBody477_38

def loopBody477_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody477_41 : HolLoopProg 64 :=
.mark loopBody477_40

def loopBody477_42 : HolLoopProg 64 :=
.seq loopBody477_41 loopBody477_1

def loopBody477_43 : HolLoopProg 64 :=
.mark loopBody477_42

def loopBody477_44 : HolLoopProg 64 :=
.seq loopBody477_39 loopBody477_43

def loopBody477_45 : HolLoopProg 64 :=
.mark loopBody477_44

def loopBody477_46 : HolLoopProg 64 :=
.seq loopBody477_37 loopBody477_45

def loopBody477_47 : HolLoopProg 64 :=
.mark loopBody477_46

def loopBody477_48 : HolLoopProg 64 :=
.seq loopBody477_15 loopBody477_47

def loopBody477_49 : HolLoopProg 64 :=
.mark loopBody477_48

def loopBody477_50 : HolLoopProg 64 :=
.seq loopBody477_1 loopBody477_49

def loopBody477_51 : HolLoopProg 64 :=
.mark loopBody477_50

def loopBody477_52 : HolLoopProg 64 :=
.seq loopBody477_1 loopBody477_51

def loopBody477_53 : HolLoopProg 64 :=
.mark loopBody477_52

def output477 : Nat × List Nat × HolLoopProg 64 :=
  (541, [0, 1], loopBody477_53)
end InitECandidate.Proofs.FrontendStages.Loop
