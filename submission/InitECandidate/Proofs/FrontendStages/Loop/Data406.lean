import InitECandidate.Proofs.FrontendStages.Loop.Translate390
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody406_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody406_1 : HolLoopProg 64 :=
.mark loopBody406_0

def loopBody406_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 112#64]))

def loopBody406_3 : HolLoopProg 64 :=
.mark loopBody406_2

def loopBody406_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 64#64])

def loopBody406_5 : HolLoopProg 64 :=
.mark loopBody406_4

def loopBody406_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 64#64]),
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 192#64])])

def loopBody406_7 : HolLoopProg 64 :=
.mark loopBody406_6

def loopBody406_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody406_9 : HolLoopProg 64 :=
.mark loopBody406_8

def loopBody406_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 4

def loopBody406_11 : HolLoopProg 64 :=
.mark loopBody406_10

def loopBody406_12 : HolLoopProg 64 :=
.seq loopBody406_11 loopBody406_1

def loopBody406_13 : HolLoopProg 64 :=
.mark loopBody406_12

def loopBody406_14 : HolLoopProg 64 :=
.seq loopBody406_9 loopBody406_13

def loopBody406_15 : HolLoopProg 64 :=
.mark loopBody406_14

def loopBody406_16 : HolLoopProg 64 :=
.seq loopBody406_15 loopBody406_1

def loopBody406_17 : HolLoopProg 64 :=
.mark loopBody406_16

def loopBody406_18 : HolLoopProg 64 :=
.seq loopBody406_7 loopBody406_17

def loopBody406_19 : HolLoopProg 64 :=
.mark loopBody406_18

def loopBody406_20 : HolLoopProg 64 :=
.seq loopBody406_1 loopBody406_19

def loopBody406_21 : HolLoopProg 64 :=
.mark loopBody406_20

def loopBody406_22 : HolLoopProg 64 :=
.seq loopBody406_5 loopBody406_21

def loopBody406_23 : HolLoopProg 64 :=
.mark loopBody406_22

def loopBody406_24 : HolLoopProg 64 :=
.seq loopBody406_1 loopBody406_23

def loopBody406_25 : HolLoopProg 64 :=
.mark loopBody406_24

def loopBody406_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 72#64])

def loopBody406_27 : HolLoopProg 64 :=
.mark loopBody406_26

def loopBody406_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64]))

def loopBody406_29 : HolLoopProg 64 :=
.mark loopBody406_28

def loopBody406_30 : HolLoopProg 64 :=
.seq loopBody406_29 loopBody406_17

def loopBody406_31 : HolLoopProg 64 :=
.mark loopBody406_30

def loopBody406_32 : HolLoopProg 64 :=
.seq loopBody406_1 loopBody406_31

def loopBody406_33 : HolLoopProg 64 :=
.mark loopBody406_32

def loopBody406_34 : HolLoopProg 64 :=
.seq loopBody406_27 loopBody406_33

def loopBody406_35 : HolLoopProg 64 :=
.mark loopBody406_34

def loopBody406_36 : HolLoopProg 64 :=
.seq loopBody406_1 loopBody406_35

def loopBody406_37 : HolLoopProg 64 :=
.mark loopBody406_36

def loopBody406_38 : HolLoopProg 64 :=
.seq loopBody406_25 loopBody406_37

def loopBody406_39 : HolLoopProg 64 :=
.mark loopBody406_38

def loopBody406_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 192#64])

def loopBody406_41 : HolLoopProg 64 :=
.mark loopBody406_40

def loopBody406_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody406_43 : HolLoopProg 64 :=
.mark loopBody406_42

def loopBody406_44 : HolLoopProg 64 :=
.seq loopBody406_43 loopBody406_17

def loopBody406_45 : HolLoopProg 64 :=
.mark loopBody406_44

def loopBody406_46 : HolLoopProg 64 :=
.seq loopBody406_1 loopBody406_45

def loopBody406_47 : HolLoopProg 64 :=
.mark loopBody406_46

def loopBody406_48 : HolLoopProg 64 :=
.seq loopBody406_41 loopBody406_47

def loopBody406_49 : HolLoopProg 64 :=
.mark loopBody406_48

def loopBody406_50 : HolLoopProg 64 :=
.seq loopBody406_1 loopBody406_49

def loopBody406_51 : HolLoopProg 64 :=
.mark loopBody406_50

def loopBody406_52 : HolLoopProg 64 :=
.seq loopBody406_39 loopBody406_51

def loopBody406_53 : HolLoopProg 64 :=
.mark loopBody406_52

def loopBody406_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody406_55 : HolLoopProg 64 :=
.mark loopBody406_54

def loopBody406_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody406_57 : HolLoopProg 64 :=
.mark loopBody406_56

def loopBody406_58 : HolLoopProg 64 :=
.seq loopBody406_57 loopBody406_1

def loopBody406_59 : HolLoopProg 64 :=
.mark loopBody406_58

def loopBody406_60 : HolLoopProg 64 :=
.seq loopBody406_55 loopBody406_59

def loopBody406_61 : HolLoopProg 64 :=
.mark loopBody406_60

def loopBody406_62 : HolLoopProg 64 :=
.seq loopBody406_53 loopBody406_61

def loopBody406_63 : HolLoopProg 64 :=
.mark loopBody406_62

def loopBody406_64 : HolLoopProg 64 :=
.seq loopBody406_3 loopBody406_63

def loopBody406_65 : HolLoopProg 64 :=
.mark loopBody406_64

def loopBody406_66 : HolLoopProg 64 :=
.seq loopBody406_1 loopBody406_65

def loopBody406_67 : HolLoopProg 64 :=
.mark loopBody406_66

def output406 : Nat × List Nat × HolLoopProg 64 :=
  (470, [], loopBody406_67)
end InitECandidate.Proofs.FrontendStages.Loop
