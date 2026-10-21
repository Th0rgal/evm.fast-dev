import InitECandidate.Proofs.FrontendStages.Loop.Translate683
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody699_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody699_1 : HolLoopProg 64 :=
.mark loopBody699_0

def loopBody699_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64]))

def loopBody699_3 : HolLoopProg 64 :=
.mark loopBody699_2

def loopBody699_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody699_5 : HolLoopProg 64 :=
.mark loopBody699_4

def loopBody699_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody699_7 : HolLoopProg 64 :=
.mark loopBody699_6

def loopBody699_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody699_9 : HolLoopProg 64 :=
.mark loopBody699_8

def loopBody699_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64],
        Flapjack.HolLoopExp.const 32#64]))

def loopBody699_11 : HolLoopProg 64 :=
.mark loopBody699_10

def loopBody699_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 96#64],
        Flapjack.HolLoopExp.const 40#64]))

def loopBody699_13 : HolLoopProg 64 :=
.mark loopBody699_12

def loopBody699_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody699_15 : HolLoopProg 64 :=
.mark loopBody699_14

def loopBody699_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody699_17 : HolLoopProg 64 :=
.mark loopBody699_16

def loopBody699_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody699_19 : HolLoopProg 64 :=
.mark loopBody699_18

def loopBody699_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 4)

def loopBody699_21 : HolLoopProg 64 :=
.mark loopBody699_20

def loopBody699_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 5)

def loopBody699_23 : HolLoopProg 64 :=
.mark loopBody699_22

def loopBody699_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 6)

def loopBody699_25 : HolLoopProg 64 :=
.mark loopBody699_24

def loopBody699_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 701) [7, 8, 9, 10, 11, 12] none

def loopBody699_27 : HolLoopProg 64 :=
.mark loopBody699_26

def loopBody699_28 : HolLoopProg 64 :=
.seq loopBody699_27 loopBody699_1

def loopBody699_29 : HolLoopProg 64 :=
.mark loopBody699_28

def loopBody699_30 : HolLoopProg 64 :=
.seq loopBody699_25 loopBody699_29

def loopBody699_31 : HolLoopProg 64 :=
.mark loopBody699_30

def loopBody699_32 : HolLoopProg 64 :=
.seq loopBody699_23 loopBody699_31

def loopBody699_33 : HolLoopProg 64 :=
.mark loopBody699_32

def loopBody699_34 : HolLoopProg 64 :=
.seq loopBody699_21 loopBody699_33

def loopBody699_35 : HolLoopProg 64 :=
.mark loopBody699_34

def loopBody699_36 : HolLoopProg 64 :=
.seq loopBody699_19 loopBody699_35

def loopBody699_37 : HolLoopProg 64 :=
.mark loopBody699_36

def loopBody699_38 : HolLoopProg 64 :=
.seq loopBody699_17 loopBody699_37

def loopBody699_39 : HolLoopProg 64 :=
.mark loopBody699_38

def loopBody699_40 : HolLoopProg 64 :=
.seq loopBody699_15 loopBody699_39

def loopBody699_41 : HolLoopProg 64 :=
.mark loopBody699_40

def loopBody699_42 : HolLoopProg 64 :=
.seq loopBody699_13 loopBody699_41

def loopBody699_43 : HolLoopProg 64 :=
.mark loopBody699_42

def loopBody699_44 : HolLoopProg 64 :=
.seq loopBody699_1 loopBody699_43

def loopBody699_45 : HolLoopProg 64 :=
.mark loopBody699_44

def loopBody699_46 : HolLoopProg 64 :=
.seq loopBody699_11 loopBody699_45

def loopBody699_47 : HolLoopProg 64 :=
.mark loopBody699_46

def loopBody699_48 : HolLoopProg 64 :=
.seq loopBody699_1 loopBody699_47

def loopBody699_49 : HolLoopProg 64 :=
.mark loopBody699_48

def loopBody699_50 : HolLoopProg 64 :=
.seq loopBody699_9 loopBody699_49

def loopBody699_51 : HolLoopProg 64 :=
.mark loopBody699_50

def loopBody699_52 : HolLoopProg 64 :=
.seq loopBody699_1 loopBody699_51

def loopBody699_53 : HolLoopProg 64 :=
.mark loopBody699_52

def loopBody699_54 : HolLoopProg 64 :=
.seq loopBody699_7 loopBody699_53

def loopBody699_55 : HolLoopProg 64 :=
.mark loopBody699_54

def loopBody699_56 : HolLoopProg 64 :=
.seq loopBody699_1 loopBody699_55

def loopBody699_57 : HolLoopProg 64 :=
.mark loopBody699_56

def loopBody699_58 : HolLoopProg 64 :=
.seq loopBody699_5 loopBody699_57

def loopBody699_59 : HolLoopProg 64 :=
.mark loopBody699_58

def loopBody699_60 : HolLoopProg 64 :=
.seq loopBody699_1 loopBody699_59

def loopBody699_61 : HolLoopProg 64 :=
.mark loopBody699_60

def loopBody699_62 : HolLoopProg 64 :=
.seq loopBody699_3 loopBody699_61

def loopBody699_63 : HolLoopProg 64 :=
.mark loopBody699_62

def loopBody699_64 : HolLoopProg 64 :=
.seq loopBody699_1 loopBody699_63

def loopBody699_65 : HolLoopProg 64 :=
.mark loopBody699_64

def output699 : Nat × List Nat × HolLoopProg 64 :=
  (763, [0], loopBody699_65)
end InitECandidate.Proofs.FrontendStages.Loop
