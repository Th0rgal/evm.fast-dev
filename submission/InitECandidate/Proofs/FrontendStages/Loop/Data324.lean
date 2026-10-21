import InitECandidate.Proofs.FrontendStages.Loop.Translate308
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody324_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody324_1 : HolLoopProg 64 :=
.mark loopBody324_0

def loopBody324_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 192#64]))

def loopBody324_3 : HolLoopProg 64 :=
.mark loopBody324_2

def loopBody324_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody324_5 : HolLoopProg 64 :=
.mark loopBody324_4

def loopBody324_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 20#64)

def loopBody324_7 : HolLoopProg 64 :=
.mark loopBody324_6

def loopBody324_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody324_9 : HolLoopProg 64 :=
.mark loopBody324_8

def loopBody324_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))) (some 77) ([3, 4, 5]) (some (3, loopBody324_9, loopBody324_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody324_11 : HolLoopProg 64 :=
.mark loopBody324_10

def loopBody324_12 : HolLoopProg 64 :=
.seq loopBody324_11 loopBody324_1

def loopBody324_13 : HolLoopProg 64 :=
.mark loopBody324_12

def loopBody324_14 : HolLoopProg 64 :=
.seq loopBody324_7 loopBody324_13

def loopBody324_15 : HolLoopProg 64 :=
.mark loopBody324_14

def loopBody324_16 : HolLoopProg 64 :=
.seq loopBody324_5 loopBody324_15

def loopBody324_17 : HolLoopProg 64 :=
.mark loopBody324_16

def loopBody324_18 : HolLoopProg 64 :=
.seq loopBody324_3 loopBody324_17

def loopBody324_19 : HolLoopProg 64 :=
.mark loopBody324_18

def loopBody324_20 : HolLoopProg 64 :=
.seq loopBody324_1 loopBody324_19

def loopBody324_21 : HolLoopProg 64 :=
.mark loopBody324_20

def loopBody324_22 : HolLoopProg 64 :=
.seq loopBody324_1 loopBody324_21

def loopBody324_23 : HolLoopProg 64 :=
.mark loopBody324_22

def loopBody324_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 192#64]),
      Flapjack.HolLoopExp.const 20#64])

def loopBody324_25 : HolLoopProg 64 :=
.mark loopBody324_24

def loopBody324_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody324_27 : HolLoopProg 64 :=
.mark loopBody324_26

def loopBody324_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 32#64)

def loopBody324_29 : HolLoopProg 64 :=
.mark loopBody324_28

def loopBody324_30 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 77) ([3, 4, 5]) (some (3, loopBody324_9, loopBody324_1, (Flapjack.Spt.ln)))

def loopBody324_31 : HolLoopProg 64 :=
.mark loopBody324_30

def loopBody324_32 : HolLoopProg 64 :=
.seq loopBody324_31 loopBody324_1

def loopBody324_33 : HolLoopProg 64 :=
.mark loopBody324_32

def loopBody324_34 : HolLoopProg 64 :=
.seq loopBody324_29 loopBody324_33

def loopBody324_35 : HolLoopProg 64 :=
.mark loopBody324_34

def loopBody324_36 : HolLoopProg 64 :=
.seq loopBody324_27 loopBody324_35

def loopBody324_37 : HolLoopProg 64 :=
.mark loopBody324_36

def loopBody324_38 : HolLoopProg 64 :=
.seq loopBody324_25 loopBody324_37

def loopBody324_39 : HolLoopProg 64 :=
.mark loopBody324_38

def loopBody324_40 : HolLoopProg 64 :=
.seq loopBody324_1 loopBody324_39

def loopBody324_41 : HolLoopProg 64 :=
.mark loopBody324_40

def loopBody324_42 : HolLoopProg 64 :=
.seq loopBody324_1 loopBody324_41

def loopBody324_43 : HolLoopProg 64 :=
.mark loopBody324_42

def loopBody324_44 : HolLoopProg 64 :=
.seq loopBody324_23 loopBody324_43

def loopBody324_45 : HolLoopProg 64 :=
.mark loopBody324_44

def loopBody324_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 192#64]))

def loopBody324_47 : HolLoopProg 64 :=
.mark loopBody324_46

def loopBody324_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody324_49 : HolLoopProg 64 :=
.mark loopBody324_48

def loopBody324_50 : HolLoopProg 64 :=
.seq loopBody324_49 loopBody324_1

def loopBody324_51 : HolLoopProg 64 :=
.mark loopBody324_50

def loopBody324_52 : HolLoopProg 64 :=
.seq loopBody324_47 loopBody324_51

def loopBody324_53 : HolLoopProg 64 :=
.mark loopBody324_52

def loopBody324_54 : HolLoopProg 64 :=
.seq loopBody324_45 loopBody324_53

def loopBody324_55 : HolLoopProg 64 :=
.mark loopBody324_54

def output324 : Nat × List Nat × HolLoopProg 64 :=
  (388, [0, 1], loopBody324_55)
end InitECandidate.Proofs.FrontendStages.Loop
