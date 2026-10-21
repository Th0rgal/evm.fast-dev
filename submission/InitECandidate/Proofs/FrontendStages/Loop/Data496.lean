import InitECandidate.Proofs.FrontendStages.Loop.Translate480
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody496_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody496_1 : HolLoopProg 64 :=
.mark loopBody496_0

def loopBody496_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody496_3 : HolLoopProg 64 :=
.mark loopBody496_2

def loopBody496_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody496_5 : HolLoopProg 64 :=
.mark loopBody496_4

def loopBody496_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody496_5, loopBody496_1, (Flapjack.Spt.ln)))

def loopBody496_7 : HolLoopProg 64 :=
.mark loopBody496_6

def loopBody496_8 : HolLoopProg 64 :=
.seq loopBody496_7 loopBody496_1

def loopBody496_9 : HolLoopProg 64 :=
.mark loopBody496_8

def loopBody496_10 : HolLoopProg 64 :=
.seq loopBody496_3 loopBody496_9

def loopBody496_11 : HolLoopProg 64 :=
.mark loopBody496_10

def loopBody496_12 : HolLoopProg 64 :=
.seq loopBody496_1 loopBody496_11

def loopBody496_13 : HolLoopProg 64 :=
.mark loopBody496_12

def loopBody496_14 : HolLoopProg 64 :=
.seq loopBody496_1 loopBody496_13

def loopBody496_15 : HolLoopProg 64 :=
.mark loopBody496_14

def loopBody496_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody496_17 : HolLoopProg 64 :=
.mark loopBody496_16

def loopBody496_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64]))

def loopBody496_19 : HolLoopProg 64 :=
.mark loopBody496_18

def loopBody496_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody496_21 : HolLoopProg 64 :=
.mark loopBody496_20

def loopBody496_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody496_23 : HolLoopProg 64 :=
.mark loopBody496_22

def loopBody496_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody496_25 : HolLoopProg 64 :=
.mark loopBody496_24

def loopBody496_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody496_27 : HolLoopProg 64 :=
.mark loopBody496_26

def loopBody496_28 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 472) ([3, 4, 5, 6]) (some (3, loopBody496_27, loopBody496_1, (Flapjack.Spt.ln)))

def loopBody496_29 : HolLoopProg 64 :=
.mark loopBody496_28

def loopBody496_30 : HolLoopProg 64 :=
.seq loopBody496_29 loopBody496_1

def loopBody496_31 : HolLoopProg 64 :=
.mark loopBody496_30

def loopBody496_32 : HolLoopProg 64 :=
.seq loopBody496_25 loopBody496_31

def loopBody496_33 : HolLoopProg 64 :=
.mark loopBody496_32

def loopBody496_34 : HolLoopProg 64 :=
.seq loopBody496_23 loopBody496_33

def loopBody496_35 : HolLoopProg 64 :=
.mark loopBody496_34

def loopBody496_36 : HolLoopProg 64 :=
.seq loopBody496_21 loopBody496_35

def loopBody496_37 : HolLoopProg 64 :=
.mark loopBody496_36

def loopBody496_38 : HolLoopProg 64 :=
.seq loopBody496_19 loopBody496_37

def loopBody496_39 : HolLoopProg 64 :=
.mark loopBody496_38

def loopBody496_40 : HolLoopProg 64 :=
.seq loopBody496_1 loopBody496_39

def loopBody496_41 : HolLoopProg 64 :=
.mark loopBody496_40

def loopBody496_42 : HolLoopProg 64 :=
.seq loopBody496_1 loopBody496_41

def loopBody496_43 : HolLoopProg 64 :=
.mark loopBody496_42

def loopBody496_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody496_45 : HolLoopProg 64 :=
.mark loopBody496_44

def loopBody496_46 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 486) ([3]) (some (3, loopBody496_27, loopBody496_1, (Flapjack.Spt.ln)))

def loopBody496_47 : HolLoopProg 64 :=
.mark loopBody496_46

def loopBody496_48 : HolLoopProg 64 :=
.seq loopBody496_47 loopBody496_1

def loopBody496_49 : HolLoopProg 64 :=
.mark loopBody496_48

def loopBody496_50 : HolLoopProg 64 :=
.seq loopBody496_45 loopBody496_49

def loopBody496_51 : HolLoopProg 64 :=
.mark loopBody496_50

def loopBody496_52 : HolLoopProg 64 :=
.seq loopBody496_1 loopBody496_51

def loopBody496_53 : HolLoopProg 64 :=
.mark loopBody496_52

def loopBody496_54 : HolLoopProg 64 :=
.seq loopBody496_1 loopBody496_53

def loopBody496_55 : HolLoopProg 64 :=
.mark loopBody496_54

def loopBody496_56 : HolLoopProg 64 :=
.seq loopBody496_43 loopBody496_55

def loopBody496_57 : HolLoopProg 64 :=
.mark loopBody496_56

def loopBody496_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody496_59 : HolLoopProg 64 :=
.mark loopBody496_58

def loopBody496_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody496_61 : HolLoopProg 64 :=
.mark loopBody496_60

def loopBody496_62 : HolLoopProg 64 :=
.seq loopBody496_61 loopBody496_1

def loopBody496_63 : HolLoopProg 64 :=
.mark loopBody496_62

def loopBody496_64 : HolLoopProg 64 :=
.seq loopBody496_59 loopBody496_63

def loopBody496_65 : HolLoopProg 64 :=
.mark loopBody496_64

def loopBody496_66 : HolLoopProg 64 :=
.seq loopBody496_57 loopBody496_65

def loopBody496_67 : HolLoopProg 64 :=
.mark loopBody496_66

def loopBody496_68 : HolLoopProg 64 :=
.seq loopBody496_17 loopBody496_67

def loopBody496_69 : HolLoopProg 64 :=
.mark loopBody496_68

def loopBody496_70 : HolLoopProg 64 :=
.seq loopBody496_1 loopBody496_69

def loopBody496_71 : HolLoopProg 64 :=
.mark loopBody496_70

def loopBody496_72 : HolLoopProg 64 :=
.seq loopBody496_15 loopBody496_71

def loopBody496_73 : HolLoopProg 64 :=
.mark loopBody496_72

def output496 : Nat × List Nat × HolLoopProg 64 :=
  (560, [], loopBody496_73)
end InitECandidate.Proofs.FrontendStages.Loop
