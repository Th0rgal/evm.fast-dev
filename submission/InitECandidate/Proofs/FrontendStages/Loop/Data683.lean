import InitECandidate.Proofs.FrontendStages.Loop.Translate667
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody683_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody683_1 : HolLoopProg 64 :=
.mark loopBody683_0

def loopBody683_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody683_3 : HolLoopProg 64 :=
.mark loopBody683_2

def loopBody683_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody683_5 : HolLoopProg 64 :=
.mark loopBody683_4

def loopBody683_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody683_7 : HolLoopProg 64 :=
.mark loopBody683_6

def loopBody683_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 732) ([3, 4]) (some (3, loopBody683_7, loopBody683_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody683_9 : HolLoopProg 64 :=
.mark loopBody683_8

def loopBody683_10 : HolLoopProg 64 :=
.seq loopBody683_9 loopBody683_1

def loopBody683_11 : HolLoopProg 64 :=
.mark loopBody683_10

def loopBody683_12 : HolLoopProg 64 :=
.seq loopBody683_5 loopBody683_11

def loopBody683_13 : HolLoopProg 64 :=
.mark loopBody683_12

def loopBody683_14 : HolLoopProg 64 :=
.seq loopBody683_3 loopBody683_13

def loopBody683_15 : HolLoopProg 64 :=
.mark loopBody683_14

def loopBody683_16 : HolLoopProg 64 :=
.seq loopBody683_1 loopBody683_15

def loopBody683_17 : HolLoopProg 64 :=
.mark loopBody683_16

def loopBody683_18 : HolLoopProg 64 :=
.seq loopBody683_1 loopBody683_17

def loopBody683_19 : HolLoopProg 64 :=
.mark loopBody683_18

def loopBody683_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64])

def loopBody683_21 : HolLoopProg 64 :=
.mark loopBody683_20

def loopBody683_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64])

def loopBody683_23 : HolLoopProg 64 :=
.mark loopBody683_22

def loopBody683_24 : HolLoopProg 64 :=
.seq loopBody683_23 loopBody683_11

def loopBody683_25 : HolLoopProg 64 :=
.mark loopBody683_24

def loopBody683_26 : HolLoopProg 64 :=
.seq loopBody683_21 loopBody683_25

def loopBody683_27 : HolLoopProg 64 :=
.mark loopBody683_26

def loopBody683_28 : HolLoopProg 64 :=
.seq loopBody683_1 loopBody683_27

def loopBody683_29 : HolLoopProg 64 :=
.mark loopBody683_28

def loopBody683_30 : HolLoopProg 64 :=
.seq loopBody683_1 loopBody683_29

def loopBody683_31 : HolLoopProg 64 :=
.mark loopBody683_30

def loopBody683_32 : HolLoopProg 64 :=
.seq loopBody683_19 loopBody683_31

def loopBody683_33 : HolLoopProg 64 :=
.mark loopBody683_32

def loopBody683_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64])

def loopBody683_35 : HolLoopProg 64 :=
.mark loopBody683_34

def loopBody683_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 192#64])

def loopBody683_37 : HolLoopProg 64 :=
.mark loopBody683_36

def loopBody683_38 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 732) ([3, 4]) (some (3, loopBody683_7, loopBody683_1, (Flapjack.Spt.ln)))

def loopBody683_39 : HolLoopProg 64 :=
.mark loopBody683_38

def loopBody683_40 : HolLoopProg 64 :=
.seq loopBody683_39 loopBody683_1

def loopBody683_41 : HolLoopProg 64 :=
.mark loopBody683_40

def loopBody683_42 : HolLoopProg 64 :=
.seq loopBody683_37 loopBody683_41

def loopBody683_43 : HolLoopProg 64 :=
.mark loopBody683_42

def loopBody683_44 : HolLoopProg 64 :=
.seq loopBody683_35 loopBody683_43

def loopBody683_45 : HolLoopProg 64 :=
.mark loopBody683_44

def loopBody683_46 : HolLoopProg 64 :=
.seq loopBody683_1 loopBody683_45

def loopBody683_47 : HolLoopProg 64 :=
.mark loopBody683_46

def loopBody683_48 : HolLoopProg 64 :=
.seq loopBody683_1 loopBody683_47

def loopBody683_49 : HolLoopProg 64 :=
.mark loopBody683_48

def loopBody683_50 : HolLoopProg 64 :=
.seq loopBody683_33 loopBody683_49

def loopBody683_51 : HolLoopProg 64 :=
.mark loopBody683_50

def loopBody683_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody683_53 : HolLoopProg 64 :=
.mark loopBody683_52

def loopBody683_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody683_55 : HolLoopProg 64 :=
.mark loopBody683_54

def loopBody683_56 : HolLoopProg 64 :=
.seq loopBody683_55 loopBody683_1

def loopBody683_57 : HolLoopProg 64 :=
.mark loopBody683_56

def loopBody683_58 : HolLoopProg 64 :=
.seq loopBody683_53 loopBody683_57

def loopBody683_59 : HolLoopProg 64 :=
.mark loopBody683_58

def loopBody683_60 : HolLoopProg 64 :=
.seq loopBody683_51 loopBody683_59

def loopBody683_61 : HolLoopProg 64 :=
.mark loopBody683_60

def output683 : Nat × List Nat × HolLoopProg 64 :=
  (747, [0, 1], loopBody683_61)
end InitECandidate.Proofs.FrontendStages.Loop
