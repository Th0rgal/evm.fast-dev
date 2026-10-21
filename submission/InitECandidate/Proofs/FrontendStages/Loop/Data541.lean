import InitECandidate.Proofs.FrontendStages.Loop.Translate525
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody541_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody541_1 : HolLoopProg 64 :=
.mark loopBody541_0

def loopBody541_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 64#64])

def loopBody541_3 : HolLoopProg 64 :=
.mark loopBody541_2

def loopBody541_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 64#64]),
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 64#64])])

def loopBody541_5 : HolLoopProg 64 :=
.mark loopBody541_4

def loopBody541_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody541_7 : HolLoopProg 64 :=
.mark loopBody541_6

def loopBody541_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 1) 3

def loopBody541_9 : HolLoopProg 64 :=
.mark loopBody541_8

def loopBody541_10 : HolLoopProg 64 :=
.seq loopBody541_9 loopBody541_1

def loopBody541_11 : HolLoopProg 64 :=
.mark loopBody541_10

def loopBody541_12 : HolLoopProg 64 :=
.seq loopBody541_7 loopBody541_11

def loopBody541_13 : HolLoopProg 64 :=
.mark loopBody541_12

def loopBody541_14 : HolLoopProg 64 :=
.seq loopBody541_13 loopBody541_1

def loopBody541_15 : HolLoopProg 64 :=
.mark loopBody541_14

def loopBody541_16 : HolLoopProg 64 :=
.seq loopBody541_5 loopBody541_15

def loopBody541_17 : HolLoopProg 64 :=
.mark loopBody541_16

def loopBody541_18 : HolLoopProg 64 :=
.seq loopBody541_1 loopBody541_17

def loopBody541_19 : HolLoopProg 64 :=
.mark loopBody541_18

def loopBody541_20 : HolLoopProg 64 :=
.seq loopBody541_3 loopBody541_19

def loopBody541_21 : HolLoopProg 64 :=
.mark loopBody541_20

def loopBody541_22 : HolLoopProg 64 :=
.seq loopBody541_1 loopBody541_21

def loopBody541_23 : HolLoopProg 64 :=
.mark loopBody541_22

def loopBody541_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 72#64])

def loopBody541_25 : HolLoopProg 64 :=
.mark loopBody541_24

def loopBody541_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 72#64]),
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 72#64])])

def loopBody541_27 : HolLoopProg 64 :=
.mark loopBody541_26

def loopBody541_28 : HolLoopProg 64 :=
.seq loopBody541_27 loopBody541_15

def loopBody541_29 : HolLoopProg 64 :=
.mark loopBody541_28

def loopBody541_30 : HolLoopProg 64 :=
.seq loopBody541_1 loopBody541_29

def loopBody541_31 : HolLoopProg 64 :=
.mark loopBody541_30

def loopBody541_32 : HolLoopProg 64 :=
.seq loopBody541_25 loopBody541_31

def loopBody541_33 : HolLoopProg 64 :=
.mark loopBody541_32

def loopBody541_34 : HolLoopProg 64 :=
.seq loopBody541_1 loopBody541_33

def loopBody541_35 : HolLoopProg 64 :=
.mark loopBody541_34

def loopBody541_36 : HolLoopProg 64 :=
.seq loopBody541_23 loopBody541_35

def loopBody541_37 : HolLoopProg 64 :=
.mark loopBody541_36

def loopBody541_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 184#64])

def loopBody541_39 : HolLoopProg 64 :=
.mark loopBody541_38

def loopBody541_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 184#64]),
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 184#64])])

def loopBody541_41 : HolLoopProg 64 :=
.mark loopBody541_40

def loopBody541_42 : HolLoopProg 64 :=
.seq loopBody541_41 loopBody541_15

def loopBody541_43 : HolLoopProg 64 :=
.mark loopBody541_42

def loopBody541_44 : HolLoopProg 64 :=
.seq loopBody541_1 loopBody541_43

def loopBody541_45 : HolLoopProg 64 :=
.mark loopBody541_44

def loopBody541_46 : HolLoopProg 64 :=
.seq loopBody541_39 loopBody541_45

def loopBody541_47 : HolLoopProg 64 :=
.mark loopBody541_46

def loopBody541_48 : HolLoopProg 64 :=
.seq loopBody541_1 loopBody541_47

def loopBody541_49 : HolLoopProg 64 :=
.mark loopBody541_48

def loopBody541_50 : HolLoopProg 64 :=
.seq loopBody541_37 loopBody541_49

def loopBody541_51 : HolLoopProg 64 :=
.mark loopBody541_50

def loopBody541_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.const 0#64)

def loopBody541_53 : HolLoopProg 64 :=
.mark loopBody541_52

def loopBody541_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [1]

def loopBody541_55 : HolLoopProg 64 :=
.mark loopBody541_54

def loopBody541_56 : HolLoopProg 64 :=
.seq loopBody541_55 loopBody541_1

def loopBody541_57 : HolLoopProg 64 :=
.mark loopBody541_56

def loopBody541_58 : HolLoopProg 64 :=
.seq loopBody541_53 loopBody541_57

def loopBody541_59 : HolLoopProg 64 :=
.mark loopBody541_58

def loopBody541_60 : HolLoopProg 64 :=
.seq loopBody541_51 loopBody541_59

def loopBody541_61 : HolLoopProg 64 :=
.mark loopBody541_60

def output541 : Nat × List Nat × HolLoopProg 64 :=
  (605, [0], loopBody541_61)
end InitECandidate.Proofs.FrontendStages.Loop
