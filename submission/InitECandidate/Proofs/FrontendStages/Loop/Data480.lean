import InitECandidate.Proofs.FrontendStages.Loop.Translate464
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody480_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody480_1 : HolLoopProg 64 :=
.mark loopBody480_0

def loopBody480_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody480_3 : HolLoopProg 64 :=
.mark loopBody480_2

def loopBody480_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody480_5 : HolLoopProg 64 :=
.mark loopBody480_4

def loopBody480_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody480_7 : HolLoopProg 64 :=
.mark loopBody480_6

def loopBody480_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 388) ([3, 4]) (some (3, loopBody480_7, loopBody480_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody480_9 : HolLoopProg 64 :=
.mark loopBody480_8

def loopBody480_10 : HolLoopProg 64 :=
.seq loopBody480_9 loopBody480_1

def loopBody480_11 : HolLoopProg 64 :=
.mark loopBody480_10

def loopBody480_12 : HolLoopProg 64 :=
.seq loopBody480_5 loopBody480_11

def loopBody480_13 : HolLoopProg 64 :=
.mark loopBody480_12

def loopBody480_14 : HolLoopProg 64 :=
.seq loopBody480_3 loopBody480_13

def loopBody480_15 : HolLoopProg 64 :=
.mark loopBody480_14

def loopBody480_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 176#64]))

def loopBody480_17 : HolLoopProg 64 :=
.mark loopBody480_16

def loopBody480_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody480_19 : HolLoopProg 64 :=
.mark loopBody480_18

def loopBody480_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody480_21 : HolLoopProg 64 :=
.mark loopBody480_20

def loopBody480_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody480_23 : HolLoopProg 64 :=
.mark loopBody480_22

def loopBody480_24 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 192) ([4, 5, 6]) (some (4, loopBody480_23, loopBody480_1, (Flapjack.Spt.ln)))

def loopBody480_25 : HolLoopProg 64 :=
.mark loopBody480_24

def loopBody480_26 : HolLoopProg 64 :=
.seq loopBody480_25 loopBody480_1

def loopBody480_27 : HolLoopProg 64 :=
.mark loopBody480_26

def loopBody480_28 : HolLoopProg 64 :=
.seq loopBody480_21 loopBody480_27

def loopBody480_29 : HolLoopProg 64 :=
.mark loopBody480_28

def loopBody480_30 : HolLoopProg 64 :=
.seq loopBody480_19 loopBody480_29

def loopBody480_31 : HolLoopProg 64 :=
.mark loopBody480_30

def loopBody480_32 : HolLoopProg 64 :=
.seq loopBody480_17 loopBody480_31

def loopBody480_33 : HolLoopProg 64 :=
.mark loopBody480_32

def loopBody480_34 : HolLoopProg 64 :=
.seq loopBody480_1 loopBody480_33

def loopBody480_35 : HolLoopProg 64 :=
.mark loopBody480_34

def loopBody480_36 : HolLoopProg 64 :=
.seq loopBody480_1 loopBody480_35

def loopBody480_37 : HolLoopProg 64 :=
.mark loopBody480_36

def loopBody480_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody480_39 : HolLoopProg 64 :=
.mark loopBody480_38

def loopBody480_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody480_41 : HolLoopProg 64 :=
.mark loopBody480_40

def loopBody480_42 : HolLoopProg 64 :=
.seq loopBody480_41 loopBody480_1

def loopBody480_43 : HolLoopProg 64 :=
.mark loopBody480_42

def loopBody480_44 : HolLoopProg 64 :=
.seq loopBody480_39 loopBody480_43

def loopBody480_45 : HolLoopProg 64 :=
.mark loopBody480_44

def loopBody480_46 : HolLoopProg 64 :=
.seq loopBody480_37 loopBody480_45

def loopBody480_47 : HolLoopProg 64 :=
.mark loopBody480_46

def loopBody480_48 : HolLoopProg 64 :=
.seq loopBody480_15 loopBody480_47

def loopBody480_49 : HolLoopProg 64 :=
.mark loopBody480_48

def loopBody480_50 : HolLoopProg 64 :=
.seq loopBody480_1 loopBody480_49

def loopBody480_51 : HolLoopProg 64 :=
.mark loopBody480_50

def loopBody480_52 : HolLoopProg 64 :=
.seq loopBody480_1 loopBody480_51

def loopBody480_53 : HolLoopProg 64 :=
.mark loopBody480_52

def output480 : Nat × List Nat × HolLoopProg 64 :=
  (544, [0, 1], loopBody480_53)
end InitECandidate.Proofs.FrontendStages.Loop
