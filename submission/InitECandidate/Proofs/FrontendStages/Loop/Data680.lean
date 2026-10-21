import InitECandidate.Proofs.FrontendStages.Loop.Translate664
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody680_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody680_1 : HolLoopProg 64 :=
.mark loopBody680_0

def loopBody680_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody680_3 : HolLoopProg 64 :=
.mark loopBody680_2

def loopBody680_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody680_5 : HolLoopProg 64 :=
.mark loopBody680_4

def loopBody680_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 727) ([2]) (some (2, loopBody680_5, loopBody680_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody680_7 : HolLoopProg 64 :=
.mark loopBody680_6

def loopBody680_8 : HolLoopProg 64 :=
.seq loopBody680_7 loopBody680_1

def loopBody680_9 : HolLoopProg 64 :=
.mark loopBody680_8

def loopBody680_10 : HolLoopProg 64 :=
.seq loopBody680_3 loopBody680_9

def loopBody680_11 : HolLoopProg 64 :=
.mark loopBody680_10

def loopBody680_12 : HolLoopProg 64 :=
.seq loopBody680_1 loopBody680_11

def loopBody680_13 : HolLoopProg 64 :=
.mark loopBody680_12

def loopBody680_14 : HolLoopProg 64 :=
.seq loopBody680_1 loopBody680_13

def loopBody680_15 : HolLoopProg 64 :=
.mark loopBody680_14

def loopBody680_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody680_17 : HolLoopProg 64 :=
.mark loopBody680_16

def loopBody680_18 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 726) ([2]) (some (2, loopBody680_5, loopBody680_1, (Flapjack.Spt.ls PUnit.unit)))

def loopBody680_19 : HolLoopProg 64 :=
.mark loopBody680_18

def loopBody680_20 : HolLoopProg 64 :=
.seq loopBody680_19 loopBody680_1

def loopBody680_21 : HolLoopProg 64 :=
.mark loopBody680_20

def loopBody680_22 : HolLoopProg 64 :=
.seq loopBody680_17 loopBody680_21

def loopBody680_23 : HolLoopProg 64 :=
.mark loopBody680_22

def loopBody680_24 : HolLoopProg 64 :=
.seq loopBody680_1 loopBody680_23

def loopBody680_25 : HolLoopProg 64 :=
.mark loopBody680_24

def loopBody680_26 : HolLoopProg 64 :=
.seq loopBody680_1 loopBody680_25

def loopBody680_27 : HolLoopProg 64 :=
.mark loopBody680_26

def loopBody680_28 : HolLoopProg 64 :=
.seq loopBody680_15 loopBody680_27

def loopBody680_29 : HolLoopProg 64 :=
.mark loopBody680_28

def loopBody680_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody680_31 : HolLoopProg 64 :=
.mark loopBody680_30

def loopBody680_32 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 726) ([2]) (some (2, loopBody680_5, loopBody680_1, (Flapjack.Spt.ln)))

def loopBody680_33 : HolLoopProg 64 :=
.mark loopBody680_32

def loopBody680_34 : HolLoopProg 64 :=
.seq loopBody680_33 loopBody680_1

def loopBody680_35 : HolLoopProg 64 :=
.mark loopBody680_34

def loopBody680_36 : HolLoopProg 64 :=
.seq loopBody680_31 loopBody680_35

def loopBody680_37 : HolLoopProg 64 :=
.mark loopBody680_36

def loopBody680_38 : HolLoopProg 64 :=
.seq loopBody680_1 loopBody680_37

def loopBody680_39 : HolLoopProg 64 :=
.mark loopBody680_38

def loopBody680_40 : HolLoopProg 64 :=
.seq loopBody680_1 loopBody680_39

def loopBody680_41 : HolLoopProg 64 :=
.mark loopBody680_40

def loopBody680_42 : HolLoopProg 64 :=
.seq loopBody680_29 loopBody680_41

def loopBody680_43 : HolLoopProg 64 :=
.mark loopBody680_42

def loopBody680_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody680_45 : HolLoopProg 64 :=
.mark loopBody680_44

def loopBody680_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody680_47 : HolLoopProg 64 :=
.mark loopBody680_46

def loopBody680_48 : HolLoopProg 64 :=
.seq loopBody680_47 loopBody680_1

def loopBody680_49 : HolLoopProg 64 :=
.mark loopBody680_48

def loopBody680_50 : HolLoopProg 64 :=
.seq loopBody680_45 loopBody680_49

def loopBody680_51 : HolLoopProg 64 :=
.mark loopBody680_50

def loopBody680_52 : HolLoopProg 64 :=
.seq loopBody680_43 loopBody680_51

def loopBody680_53 : HolLoopProg 64 :=
.mark loopBody680_52

def output680 : Nat × List Nat × HolLoopProg 64 :=
  (744, [0], loopBody680_53)
end InitECandidate.Proofs.FrontendStages.Loop
