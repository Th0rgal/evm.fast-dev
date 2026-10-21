import InitECandidate.Proofs.FrontendStages.Loop.Translate478
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody494_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody494_1 : HolLoopProg 64 :=
.mark loopBody494_0

def loopBody494_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody494_3 : HolLoopProg 64 :=
.mark loopBody494_2

def loopBody494_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody494_5 : HolLoopProg 64 :=
.mark loopBody494_4

def loopBody494_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody494_5, loopBody494_1, (Flapjack.Spt.ln)))

def loopBody494_7 : HolLoopProg 64 :=
.mark loopBody494_6

def loopBody494_8 : HolLoopProg 64 :=
.seq loopBody494_7 loopBody494_1

def loopBody494_9 : HolLoopProg 64 :=
.mark loopBody494_8

def loopBody494_10 : HolLoopProg 64 :=
.seq loopBody494_3 loopBody494_9

def loopBody494_11 : HolLoopProg 64 :=
.mark loopBody494_10

def loopBody494_12 : HolLoopProg 64 :=
.seq loopBody494_1 loopBody494_11

def loopBody494_13 : HolLoopProg 64 :=
.mark loopBody494_12

def loopBody494_14 : HolLoopProg 64 :=
.seq loopBody494_1 loopBody494_13

def loopBody494_15 : HolLoopProg 64 :=
.mark loopBody494_14

def loopBody494_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 56#64]))

def loopBody494_17 : HolLoopProg 64 :=
.mark loopBody494_16

def loopBody494_18 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 473) ([2]) (some (2, loopBody494_5, loopBody494_1, (Flapjack.Spt.ln)))

def loopBody494_19 : HolLoopProg 64 :=
.mark loopBody494_18

def loopBody494_20 : HolLoopProg 64 :=
.seq loopBody494_19 loopBody494_1

def loopBody494_21 : HolLoopProg 64 :=
.mark loopBody494_20

def loopBody494_22 : HolLoopProg 64 :=
.seq loopBody494_17 loopBody494_21

def loopBody494_23 : HolLoopProg 64 :=
.mark loopBody494_22

def loopBody494_24 : HolLoopProg 64 :=
.seq loopBody494_1 loopBody494_23

def loopBody494_25 : HolLoopProg 64 :=
.mark loopBody494_24

def loopBody494_26 : HolLoopProg 64 :=
.seq loopBody494_1 loopBody494_25

def loopBody494_27 : HolLoopProg 64 :=
.mark loopBody494_26

def loopBody494_28 : HolLoopProg 64 :=
.seq loopBody494_15 loopBody494_27

def loopBody494_29 : HolLoopProg 64 :=
.mark loopBody494_28

def loopBody494_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody494_31 : HolLoopProg 64 :=
.mark loopBody494_30

def loopBody494_32 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 486) ([2]) (some (2, loopBody494_5, loopBody494_1, (Flapjack.Spt.ln)))

def loopBody494_33 : HolLoopProg 64 :=
.mark loopBody494_32

def loopBody494_34 : HolLoopProg 64 :=
.seq loopBody494_33 loopBody494_1

def loopBody494_35 : HolLoopProg 64 :=
.mark loopBody494_34

def loopBody494_36 : HolLoopProg 64 :=
.seq loopBody494_31 loopBody494_35

def loopBody494_37 : HolLoopProg 64 :=
.mark loopBody494_36

def loopBody494_38 : HolLoopProg 64 :=
.seq loopBody494_1 loopBody494_37

def loopBody494_39 : HolLoopProg 64 :=
.mark loopBody494_38

def loopBody494_40 : HolLoopProg 64 :=
.seq loopBody494_1 loopBody494_39

def loopBody494_41 : HolLoopProg 64 :=
.mark loopBody494_40

def loopBody494_42 : HolLoopProg 64 :=
.seq loopBody494_29 loopBody494_41

def loopBody494_43 : HolLoopProg 64 :=
.mark loopBody494_42

def loopBody494_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody494_45 : HolLoopProg 64 :=
.mark loopBody494_44

def loopBody494_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody494_47 : HolLoopProg 64 :=
.mark loopBody494_46

def loopBody494_48 : HolLoopProg 64 :=
.seq loopBody494_47 loopBody494_1

def loopBody494_49 : HolLoopProg 64 :=
.mark loopBody494_48

def loopBody494_50 : HolLoopProg 64 :=
.seq loopBody494_45 loopBody494_49

def loopBody494_51 : HolLoopProg 64 :=
.mark loopBody494_50

def loopBody494_52 : HolLoopProg 64 :=
.seq loopBody494_43 loopBody494_51

def loopBody494_53 : HolLoopProg 64 :=
.mark loopBody494_52

def output494 : Nat × List Nat × HolLoopProg 64 :=
  (558, [], loopBody494_53)
end InitECandidate.Proofs.FrontendStages.Loop
