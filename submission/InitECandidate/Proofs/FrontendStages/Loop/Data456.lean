import InitECandidate.Proofs.FrontendStages.Loop.Translate440
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody456_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody456_1 : HolLoopProg 64 :=
.mark loopBody456_0

def loopBody456_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 104#64])

def loopBody456_3 : HolLoopProg 64 :=
.mark loopBody456_2

def loopBody456_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody456_5 : HolLoopProg 64 :=
.mark loopBody456_4

def loopBody456_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody456_7 : HolLoopProg 64 :=
.mark loopBody456_6

def loopBody456_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody456_9 : HolLoopProg 64 :=
.mark loopBody456_8

def loopBody456_10 : HolLoopProg 64 :=
.seq loopBody456_9 loopBody456_1

def loopBody456_11 : HolLoopProg 64 :=
.mark loopBody456_10

def loopBody456_12 : HolLoopProg 64 :=
.seq loopBody456_7 loopBody456_11

def loopBody456_13 : HolLoopProg 64 :=
.mark loopBody456_12

def loopBody456_14 : HolLoopProg 64 :=
.seq loopBody456_13 loopBody456_1

def loopBody456_15 : HolLoopProg 64 :=
.mark loopBody456_14

def loopBody456_16 : HolLoopProg 64 :=
.seq loopBody456_5 loopBody456_15

def loopBody456_17 : HolLoopProg 64 :=
.mark loopBody456_16

def loopBody456_18 : HolLoopProg 64 :=
.seq loopBody456_1 loopBody456_17

def loopBody456_19 : HolLoopProg 64 :=
.mark loopBody456_18

def loopBody456_20 : HolLoopProg 64 :=
.seq loopBody456_3 loopBody456_19

def loopBody456_21 : HolLoopProg 64 :=
.mark loopBody456_20

def loopBody456_22 : HolLoopProg 64 :=
.seq loopBody456_1 loopBody456_21

def loopBody456_23 : HolLoopProg 64 :=
.mark loopBody456_22

def loopBody456_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody456_25 : HolLoopProg 64 :=
.mark loopBody456_24

def loopBody456_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody456_27 : HolLoopProg 64 :=
.mark loopBody456_26

def loopBody456_28 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 486) ([2]) (some (2, loopBody456_27, loopBody456_1, (Flapjack.Spt.ln)))

def loopBody456_29 : HolLoopProg 64 :=
.mark loopBody456_28

def loopBody456_30 : HolLoopProg 64 :=
.seq loopBody456_29 loopBody456_1

def loopBody456_31 : HolLoopProg 64 :=
.mark loopBody456_30

def loopBody456_32 : HolLoopProg 64 :=
.seq loopBody456_25 loopBody456_31

def loopBody456_33 : HolLoopProg 64 :=
.mark loopBody456_32

def loopBody456_34 : HolLoopProg 64 :=
.seq loopBody456_1 loopBody456_33

def loopBody456_35 : HolLoopProg 64 :=
.mark loopBody456_34

def loopBody456_36 : HolLoopProg 64 :=
.seq loopBody456_1 loopBody456_35

def loopBody456_37 : HolLoopProg 64 :=
.mark loopBody456_36

def loopBody456_38 : HolLoopProg 64 :=
.seq loopBody456_23 loopBody456_37

def loopBody456_39 : HolLoopProg 64 :=
.mark loopBody456_38

def loopBody456_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody456_41 : HolLoopProg 64 :=
.mark loopBody456_40

def loopBody456_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody456_43 : HolLoopProg 64 :=
.mark loopBody456_42

def loopBody456_44 : HolLoopProg 64 :=
.seq loopBody456_43 loopBody456_1

def loopBody456_45 : HolLoopProg 64 :=
.mark loopBody456_44

def loopBody456_46 : HolLoopProg 64 :=
.seq loopBody456_41 loopBody456_45

def loopBody456_47 : HolLoopProg 64 :=
.mark loopBody456_46

def loopBody456_48 : HolLoopProg 64 :=
.seq loopBody456_39 loopBody456_47

def loopBody456_49 : HolLoopProg 64 :=
.mark loopBody456_48

def output456 : Nat × List Nat × HolLoopProg 64 :=
  (520, [], loopBody456_49)
end InitECandidate.Proofs.FrontendStages.Loop
