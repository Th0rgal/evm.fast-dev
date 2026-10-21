import InitECandidate.Proofs.FrontendStages.Loop.Translate215
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody231_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody231_1 : HolLoopProg 64 :=
.mark loopBody231_0

def loopBody231_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64])

def loopBody231_3 : HolLoopProg 64 :=
.mark loopBody231_2

def loopBody231_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody231_5 : HolLoopProg 64 :=
.mark loopBody231_4

def loopBody231_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody231_7 : HolLoopProg 64 :=
.mark loopBody231_6

def loopBody231_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody231_9 : HolLoopProg 64 :=
.mark loopBody231_8

def loopBody231_10 : HolLoopProg 64 :=
.seq loopBody231_9 loopBody231_1

def loopBody231_11 : HolLoopProg 64 :=
.mark loopBody231_10

def loopBody231_12 : HolLoopProg 64 :=
.seq loopBody231_7 loopBody231_11

def loopBody231_13 : HolLoopProg 64 :=
.mark loopBody231_12

def loopBody231_14 : HolLoopProg 64 :=
.seq loopBody231_13 loopBody231_1

def loopBody231_15 : HolLoopProg 64 :=
.mark loopBody231_14

def loopBody231_16 : HolLoopProg 64 :=
.seq loopBody231_5 loopBody231_15

def loopBody231_17 : HolLoopProg 64 :=
.mark loopBody231_16

def loopBody231_18 : HolLoopProg 64 :=
.seq loopBody231_1 loopBody231_17

def loopBody231_19 : HolLoopProg 64 :=
.mark loopBody231_18

def loopBody231_20 : HolLoopProg 64 :=
.seq loopBody231_3 loopBody231_19

def loopBody231_21 : HolLoopProg 64 :=
.mark loopBody231_20

def loopBody231_22 : HolLoopProg 64 :=
.seq loopBody231_1 loopBody231_21

def loopBody231_23 : HolLoopProg 64 :=
.mark loopBody231_22

def loopBody231_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64])

def loopBody231_25 : HolLoopProg 64 :=
.mark loopBody231_24

def loopBody231_26 : HolLoopProg 64 :=
.seq loopBody231_25 loopBody231_19

def loopBody231_27 : HolLoopProg 64 :=
.mark loopBody231_26

def loopBody231_28 : HolLoopProg 64 :=
.seq loopBody231_1 loopBody231_27

def loopBody231_29 : HolLoopProg 64 :=
.mark loopBody231_28

def loopBody231_30 : HolLoopProg 64 :=
.seq loopBody231_23 loopBody231_29

def loopBody231_31 : HolLoopProg 64 :=
.mark loopBody231_30

def loopBody231_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 24#64])

def loopBody231_33 : HolLoopProg 64 :=
.mark loopBody231_32

def loopBody231_34 : HolLoopProg 64 :=
.seq loopBody231_33 loopBody231_19

def loopBody231_35 : HolLoopProg 64 :=
.mark loopBody231_34

def loopBody231_36 : HolLoopProg 64 :=
.seq loopBody231_1 loopBody231_35

def loopBody231_37 : HolLoopProg 64 :=
.mark loopBody231_36

def loopBody231_38 : HolLoopProg 64 :=
.seq loopBody231_31 loopBody231_37

def loopBody231_39 : HolLoopProg 64 :=
.mark loopBody231_38

def loopBody231_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody231_41 : HolLoopProg 64 :=
.mark loopBody231_40

def loopBody231_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody231_43 : HolLoopProg 64 :=
.mark loopBody231_42

def loopBody231_44 : HolLoopProg 64 :=
.seq loopBody231_43 loopBody231_1

def loopBody231_45 : HolLoopProg 64 :=
.mark loopBody231_44

def loopBody231_46 : HolLoopProg 64 :=
.seq loopBody231_41 loopBody231_45

def loopBody231_47 : HolLoopProg 64 :=
.mark loopBody231_46

def loopBody231_48 : HolLoopProg 64 :=
.seq loopBody231_39 loopBody231_47

def loopBody231_49 : HolLoopProg 64 :=
.mark loopBody231_48

def output231 : Nat × List Nat × HolLoopProg 64 :=
  (295, [0], loopBody231_49)
end InitECandidate.Proofs.FrontendStages.Loop
