import InitECandidate.Proofs.FrontendStages.Loop.Translate310
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody326_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody326_1 : HolLoopProg 64 :=
.mark loopBody326_0

def loopBody326_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody326_3 : HolLoopProg 64 :=
.mark loopBody326_2

def loopBody326_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody326_5 : HolLoopProg 64 :=
.mark loopBody326_4

def loopBody326_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody326_7 : HolLoopProg 64 :=
.mark loopBody326_6

def loopBody326_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody326_9 : HolLoopProg 64 :=
.mark loopBody326_8

def loopBody326_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody326_11 : HolLoopProg 64 :=
.mark loopBody326_10

def loopBody326_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 136#64]))

def loopBody326_13 : HolLoopProg 64 :=
.mark loopBody326_12

def loopBody326_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody326_15 : HolLoopProg 64 :=
.mark loopBody326_14

def loopBody326_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 389) ([2, 3, 4, 5, 6, 7]) (some (2, loopBody326_15, loopBody326_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody326_17 : HolLoopProg 64 :=
.mark loopBody326_16

def loopBody326_18 : HolLoopProg 64 :=
.seq loopBody326_17 loopBody326_1

def loopBody326_19 : HolLoopProg 64 :=
.mark loopBody326_18

def loopBody326_20 : HolLoopProg 64 :=
.seq loopBody326_13 loopBody326_19

def loopBody326_21 : HolLoopProg 64 :=
.mark loopBody326_20

def loopBody326_22 : HolLoopProg 64 :=
.seq loopBody326_11 loopBody326_21

def loopBody326_23 : HolLoopProg 64 :=
.mark loopBody326_22

def loopBody326_24 : HolLoopProg 64 :=
.seq loopBody326_9 loopBody326_23

def loopBody326_25 : HolLoopProg 64 :=
.mark loopBody326_24

def loopBody326_26 : HolLoopProg 64 :=
.seq loopBody326_7 loopBody326_25

def loopBody326_27 : HolLoopProg 64 :=
.mark loopBody326_26

def loopBody326_28 : HolLoopProg 64 :=
.seq loopBody326_5 loopBody326_27

def loopBody326_29 : HolLoopProg 64 :=
.mark loopBody326_28

def loopBody326_30 : HolLoopProg 64 :=
.seq loopBody326_3 loopBody326_29

def loopBody326_31 : HolLoopProg 64 :=
.mark loopBody326_30

def loopBody326_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody326_33 : HolLoopProg 64 :=
.mark loopBody326_32

def loopBody326_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody326_35 : HolLoopProg 64 :=
.mark loopBody326_34

def loopBody326_36 : HolLoopProg 64 :=
.seq loopBody326_35 loopBody326_1

def loopBody326_37 : HolLoopProg 64 :=
.mark loopBody326_36

def loopBody326_38 : HolLoopProg 64 :=
.seq loopBody326_33 loopBody326_37

def loopBody326_39 : HolLoopProg 64 :=
.mark loopBody326_38

def loopBody326_40 : HolLoopProg 64 :=
.seq loopBody326_31 loopBody326_39

def loopBody326_41 : HolLoopProg 64 :=
.mark loopBody326_40

def loopBody326_42 : HolLoopProg 64 :=
.seq loopBody326_1 loopBody326_41

def loopBody326_43 : HolLoopProg 64 :=
.mark loopBody326_42

def loopBody326_44 : HolLoopProg 64 :=
.seq loopBody326_1 loopBody326_43

def loopBody326_45 : HolLoopProg 64 :=
.mark loopBody326_44

def output326 : Nat × List Nat × HolLoopProg 64 :=
  (390, [], loopBody326_45)
end InitECandidate.Proofs.FrontendStages.Loop
