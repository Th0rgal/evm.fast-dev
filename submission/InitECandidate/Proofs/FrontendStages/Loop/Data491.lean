import InitECandidate.Proofs.FrontendStages.Loop.Translate475
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody491_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody491_1 : HolLoopProg 64 :=
.mark loopBody491_0

def loopBody491_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody491_3 : HolLoopProg 64 :=
.mark loopBody491_2

def loopBody491_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody491_5 : HolLoopProg 64 :=
.mark loopBody491_4

def loopBody491_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody491_5, loopBody491_1, (Flapjack.Spt.ln)))

def loopBody491_7 : HolLoopProg 64 :=
.mark loopBody491_6

def loopBody491_8 : HolLoopProg 64 :=
.seq loopBody491_7 loopBody491_1

def loopBody491_9 : HolLoopProg 64 :=
.mark loopBody491_8

def loopBody491_10 : HolLoopProg 64 :=
.seq loopBody491_3 loopBody491_9

def loopBody491_11 : HolLoopProg 64 :=
.mark loopBody491_10

def loopBody491_12 : HolLoopProg 64 :=
.seq loopBody491_1 loopBody491_11

def loopBody491_13 : HolLoopProg 64 :=
.mark loopBody491_12

def loopBody491_14 : HolLoopProg 64 :=
.seq loopBody491_1 loopBody491_13

def loopBody491_15 : HolLoopProg 64 :=
.mark loopBody491_14

def loopBody491_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 96#64]))

def loopBody491_17 : HolLoopProg 64 :=
.mark loopBody491_16

def loopBody491_18 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 473) ([2]) (some (2, loopBody491_5, loopBody491_1, (Flapjack.Spt.ln)))

def loopBody491_19 : HolLoopProg 64 :=
.mark loopBody491_18

def loopBody491_20 : HolLoopProg 64 :=
.seq loopBody491_19 loopBody491_1

def loopBody491_21 : HolLoopProg 64 :=
.mark loopBody491_20

def loopBody491_22 : HolLoopProg 64 :=
.seq loopBody491_17 loopBody491_21

def loopBody491_23 : HolLoopProg 64 :=
.mark loopBody491_22

def loopBody491_24 : HolLoopProg 64 :=
.seq loopBody491_1 loopBody491_23

def loopBody491_25 : HolLoopProg 64 :=
.mark loopBody491_24

def loopBody491_26 : HolLoopProg 64 :=
.seq loopBody491_1 loopBody491_25

def loopBody491_27 : HolLoopProg 64 :=
.mark loopBody491_26

def loopBody491_28 : HolLoopProg 64 :=
.seq loopBody491_15 loopBody491_27

def loopBody491_29 : HolLoopProg 64 :=
.mark loopBody491_28

def loopBody491_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody491_31 : HolLoopProg 64 :=
.mark loopBody491_30

def loopBody491_32 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 486) ([2]) (some (2, loopBody491_5, loopBody491_1, (Flapjack.Spt.ln)))

def loopBody491_33 : HolLoopProg 64 :=
.mark loopBody491_32

def loopBody491_34 : HolLoopProg 64 :=
.seq loopBody491_33 loopBody491_1

def loopBody491_35 : HolLoopProg 64 :=
.mark loopBody491_34

def loopBody491_36 : HolLoopProg 64 :=
.seq loopBody491_31 loopBody491_35

def loopBody491_37 : HolLoopProg 64 :=
.mark loopBody491_36

def loopBody491_38 : HolLoopProg 64 :=
.seq loopBody491_1 loopBody491_37

def loopBody491_39 : HolLoopProg 64 :=
.mark loopBody491_38

def loopBody491_40 : HolLoopProg 64 :=
.seq loopBody491_1 loopBody491_39

def loopBody491_41 : HolLoopProg 64 :=
.mark loopBody491_40

def loopBody491_42 : HolLoopProg 64 :=
.seq loopBody491_29 loopBody491_41

def loopBody491_43 : HolLoopProg 64 :=
.mark loopBody491_42

def loopBody491_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody491_45 : HolLoopProg 64 :=
.mark loopBody491_44

def loopBody491_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody491_47 : HolLoopProg 64 :=
.mark loopBody491_46

def loopBody491_48 : HolLoopProg 64 :=
.seq loopBody491_47 loopBody491_1

def loopBody491_49 : HolLoopProg 64 :=
.mark loopBody491_48

def loopBody491_50 : HolLoopProg 64 :=
.seq loopBody491_45 loopBody491_49

def loopBody491_51 : HolLoopProg 64 :=
.mark loopBody491_50

def loopBody491_52 : HolLoopProg 64 :=
.seq loopBody491_43 loopBody491_51

def loopBody491_53 : HolLoopProg 64 :=
.mark loopBody491_52

def output491 : Nat × List Nat × HolLoopProg 64 :=
  (555, [], loopBody491_53)
end InitECandidate.Proofs.FrontendStages.Loop
