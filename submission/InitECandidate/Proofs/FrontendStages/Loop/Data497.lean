import InitECandidate.Proofs.FrontendStages.Loop.Translate481
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody497_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody497_1 : HolLoopProg 64 :=
.mark loopBody497_0

def loopBody497_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody497_3 : HolLoopProg 64 :=
.mark loopBody497_2

def loopBody497_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody497_5 : HolLoopProg 64 :=
.mark loopBody497_4

def loopBody497_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 403) ([2]) (some (2, loopBody497_5, loopBody497_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody497_7 : HolLoopProg 64 :=
.mark loopBody497_6

def loopBody497_8 : HolLoopProg 64 :=
.seq loopBody497_7 loopBody497_1

def loopBody497_9 : HolLoopProg 64 :=
.mark loopBody497_8

def loopBody497_10 : HolLoopProg 64 :=
.seq loopBody497_3 loopBody497_9

def loopBody497_11 : HolLoopProg 64 :=
.mark loopBody497_10

def loopBody497_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64]))

def loopBody497_13 : HolLoopProg 64 :=
.mark loopBody497_12

def loopBody497_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody497_15 : HolLoopProg 64 :=
.mark loopBody497_14

def loopBody497_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody497_17 : HolLoopProg 64 :=
.mark loopBody497_16

def loopBody497_18 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.ln)) (some 404) ([4, 5]) (some (4, loopBody497_17, loopBody497_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody497_19 : HolLoopProg 64 :=
.mark loopBody497_18

def loopBody497_20 : HolLoopProg 64 :=
.seq loopBody497_19 loopBody497_1

def loopBody497_21 : HolLoopProg 64 :=
.mark loopBody497_20

def loopBody497_22 : HolLoopProg 64 :=
.seq loopBody497_15 loopBody497_21

def loopBody497_23 : HolLoopProg 64 :=
.mark loopBody497_22

def loopBody497_24 : HolLoopProg 64 :=
.seq loopBody497_13 loopBody497_23

def loopBody497_25 : HolLoopProg 64 :=
.mark loopBody497_24

def loopBody497_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody497_27 : HolLoopProg 64 :=
.mark loopBody497_26

def loopBody497_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody497_29 : HolLoopProg 64 :=
.mark loopBody497_28

def loopBody497_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4, 5]

def loopBody497_31 : HolLoopProg 64 :=
.mark loopBody497_30

def loopBody497_32 : HolLoopProg 64 :=
.seq loopBody497_31 loopBody497_1

def loopBody497_33 : HolLoopProg 64 :=
.mark loopBody497_32

def loopBody497_34 : HolLoopProg 64 :=
.seq loopBody497_29 loopBody497_33

def loopBody497_35 : HolLoopProg 64 :=
.mark loopBody497_34

def loopBody497_36 : HolLoopProg 64 :=
.seq loopBody497_27 loopBody497_35

def loopBody497_37 : HolLoopProg 64 :=
.mark loopBody497_36

def loopBody497_38 : HolLoopProg 64 :=
.seq loopBody497_25 loopBody497_37

def loopBody497_39 : HolLoopProg 64 :=
.mark loopBody497_38

def loopBody497_40 : HolLoopProg 64 :=
.seq loopBody497_1 loopBody497_39

def loopBody497_41 : HolLoopProg 64 :=
.mark loopBody497_40

def loopBody497_42 : HolLoopProg 64 :=
.seq loopBody497_1 loopBody497_41

def loopBody497_43 : HolLoopProg 64 :=
.mark loopBody497_42

def loopBody497_44 : HolLoopProg 64 :=
.seq loopBody497_1 loopBody497_43

def loopBody497_45 : HolLoopProg 64 :=
.mark loopBody497_44

def loopBody497_46 : HolLoopProg 64 :=
.seq loopBody497_1 loopBody497_45

def loopBody497_47 : HolLoopProg 64 :=
.mark loopBody497_46

def loopBody497_48 : HolLoopProg 64 :=
.seq loopBody497_11 loopBody497_47

def loopBody497_49 : HolLoopProg 64 :=
.mark loopBody497_48

def loopBody497_50 : HolLoopProg 64 :=
.seq loopBody497_1 loopBody497_49

def loopBody497_51 : HolLoopProg 64 :=
.mark loopBody497_50

def loopBody497_52 : HolLoopProg 64 :=
.seq loopBody497_1 loopBody497_51

def loopBody497_53 : HolLoopProg 64 :=
.mark loopBody497_52

def output497 : Nat × List Nat × HolLoopProg 64 :=
  (561, [0], loopBody497_53)
end InitECandidate.Proofs.FrontendStages.Loop
