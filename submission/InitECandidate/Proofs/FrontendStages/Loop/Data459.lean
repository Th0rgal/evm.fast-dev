import InitECandidate.Proofs.FrontendStages.Loop.Translate443
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody459_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody459_1 : HolLoopProg 64 :=
.mark loopBody459_0

def loopBody459_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody459_3 : HolLoopProg 64 :=
.mark loopBody459_2

def loopBody459_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody459_5 : HolLoopProg 64 :=
.mark loopBody459_4

def loopBody459_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody459_5, loopBody459_1, (Flapjack.Spt.ln)))

def loopBody459_7 : HolLoopProg 64 :=
.mark loopBody459_6

def loopBody459_8 : HolLoopProg 64 :=
.seq loopBody459_7 loopBody459_1

def loopBody459_9 : HolLoopProg 64 :=
.mark loopBody459_8

def loopBody459_10 : HolLoopProg 64 :=
.seq loopBody459_3 loopBody459_9

def loopBody459_11 : HolLoopProg 64 :=
.mark loopBody459_10

def loopBody459_12 : HolLoopProg 64 :=
.seq loopBody459_1 loopBody459_11

def loopBody459_13 : HolLoopProg 64 :=
.mark loopBody459_12

def loopBody459_14 : HolLoopProg 64 :=
.seq loopBody459_1 loopBody459_13

def loopBody459_15 : HolLoopProg 64 :=
.mark loopBody459_14

def loopBody459_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 0#64]))

def loopBody459_17 : HolLoopProg 64 :=
.mark loopBody459_16

def loopBody459_18 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 473) ([2]) (some (2, loopBody459_5, loopBody459_1, (Flapjack.Spt.ln)))

def loopBody459_19 : HolLoopProg 64 :=
.mark loopBody459_18

def loopBody459_20 : HolLoopProg 64 :=
.seq loopBody459_19 loopBody459_1

def loopBody459_21 : HolLoopProg 64 :=
.mark loopBody459_20

def loopBody459_22 : HolLoopProg 64 :=
.seq loopBody459_17 loopBody459_21

def loopBody459_23 : HolLoopProg 64 :=
.mark loopBody459_22

def loopBody459_24 : HolLoopProg 64 :=
.seq loopBody459_1 loopBody459_23

def loopBody459_25 : HolLoopProg 64 :=
.mark loopBody459_24

def loopBody459_26 : HolLoopProg 64 :=
.seq loopBody459_1 loopBody459_25

def loopBody459_27 : HolLoopProg 64 :=
.mark loopBody459_26

def loopBody459_28 : HolLoopProg 64 :=
.seq loopBody459_15 loopBody459_27

def loopBody459_29 : HolLoopProg 64 :=
.mark loopBody459_28

def loopBody459_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody459_31 : HolLoopProg 64 :=
.mark loopBody459_30

def loopBody459_32 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 486) ([2]) (some (2, loopBody459_5, loopBody459_1, (Flapjack.Spt.ln)))

def loopBody459_33 : HolLoopProg 64 :=
.mark loopBody459_32

def loopBody459_34 : HolLoopProg 64 :=
.seq loopBody459_33 loopBody459_1

def loopBody459_35 : HolLoopProg 64 :=
.mark loopBody459_34

def loopBody459_36 : HolLoopProg 64 :=
.seq loopBody459_31 loopBody459_35

def loopBody459_37 : HolLoopProg 64 :=
.mark loopBody459_36

def loopBody459_38 : HolLoopProg 64 :=
.seq loopBody459_1 loopBody459_37

def loopBody459_39 : HolLoopProg 64 :=
.mark loopBody459_38

def loopBody459_40 : HolLoopProg 64 :=
.seq loopBody459_1 loopBody459_39

def loopBody459_41 : HolLoopProg 64 :=
.mark loopBody459_40

def loopBody459_42 : HolLoopProg 64 :=
.seq loopBody459_29 loopBody459_41

def loopBody459_43 : HolLoopProg 64 :=
.mark loopBody459_42

def loopBody459_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody459_45 : HolLoopProg 64 :=
.mark loopBody459_44

def loopBody459_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody459_47 : HolLoopProg 64 :=
.mark loopBody459_46

def loopBody459_48 : HolLoopProg 64 :=
.seq loopBody459_47 loopBody459_1

def loopBody459_49 : HolLoopProg 64 :=
.mark loopBody459_48

def loopBody459_50 : HolLoopProg 64 :=
.seq loopBody459_45 loopBody459_49

def loopBody459_51 : HolLoopProg 64 :=
.mark loopBody459_50

def loopBody459_52 : HolLoopProg 64 :=
.seq loopBody459_43 loopBody459_51

def loopBody459_53 : HolLoopProg 64 :=
.mark loopBody459_52

def output459 : Nat × List Nat × HolLoopProg 64 :=
  (523, [], loopBody459_53)
end InitECandidate.Proofs.FrontendStages.Loop
