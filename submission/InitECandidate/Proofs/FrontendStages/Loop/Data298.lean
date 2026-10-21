import InitECandidate.Proofs.FrontendStages.Loop.Translate282
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody298_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody298_1 : HolLoopProg 64 :=
.mark loopBody298_0

def loopBody298_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 208#64]))

def loopBody298_3 : HolLoopProg 64 :=
.mark loopBody298_2

def loopBody298_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 216#64]))

def loopBody298_5 : HolLoopProg 64 :=
.mark loopBody298_4

def loopBody298_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody298_7 : HolLoopProg 64 :=
.mark loopBody298_6

def loopBody298_8 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 356) ([2, 3]) (some (2, loopBody298_7, loopBody298_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody298_9 : HolLoopProg 64 :=
.mark loopBody298_8

def loopBody298_10 : HolLoopProg 64 :=
.seq loopBody298_9 loopBody298_1

def loopBody298_11 : HolLoopProg 64 :=
.mark loopBody298_10

def loopBody298_12 : HolLoopProg 64 :=
.seq loopBody298_5 loopBody298_11

def loopBody298_13 : HolLoopProg 64 :=
.mark loopBody298_12

def loopBody298_14 : HolLoopProg 64 :=
.seq loopBody298_3 loopBody298_13

def loopBody298_15 : HolLoopProg 64 :=
.mark loopBody298_14

def loopBody298_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 272#64]))

def loopBody298_17 : HolLoopProg 64 :=
.mark loopBody298_16

def loopBody298_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 280#64]))

def loopBody298_19 : HolLoopProg 64 :=
.mark loopBody298_18

def loopBody298_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody298_21 : HolLoopProg 64 :=
.mark loopBody298_20

def loopBody298_22 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 360) ([3, 4]) (some (3, loopBody298_21, loopBody298_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody298_23 : HolLoopProg 64 :=
.mark loopBody298_22

def loopBody298_24 : HolLoopProg 64 :=
.seq loopBody298_23 loopBody298_1

def loopBody298_25 : HolLoopProg 64 :=
.mark loopBody298_24

def loopBody298_26 : HolLoopProg 64 :=
.seq loopBody298_19 loopBody298_25

def loopBody298_27 : HolLoopProg 64 :=
.mark loopBody298_26

def loopBody298_28 : HolLoopProg 64 :=
.seq loopBody298_17 loopBody298_27

def loopBody298_29 : HolLoopProg 64 :=
.mark loopBody298_28

def loopBody298_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 264#64]))

def loopBody298_31 : HolLoopProg 64 :=
.mark loopBody298_30

def loopBody298_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 33#64)

def loopBody298_33 : HolLoopProg 64 :=
.mark loopBody298_32

def loopBody298_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 5 5 3 4)

def loopBody298_35 : HolLoopProg 64 :=
.mark loopBody298_34

def loopBody298_36 : HolLoopProg 64 :=
.seq loopBody298_35 loopBody298_1

def loopBody298_37 : HolLoopProg 64 :=
.mark loopBody298_36

def loopBody298_38 : HolLoopProg 64 :=
.seq loopBody298_33 loopBody298_37

def loopBody298_39 : HolLoopProg 64 :=
.mark loopBody298_38

def loopBody298_40 : HolLoopProg 64 :=
.seq loopBody298_31 loopBody298_39

def loopBody298_41 : HolLoopProg 64 :=
.mark loopBody298_40

def loopBody298_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody298_43 : HolLoopProg 64 :=
.mark loopBody298_42

def loopBody298_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.const 64#64, Flapjack.HolLoopExp.const 561#64, Flapjack.HolLoopExp.const 30#64,
      Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 200#64]),
      Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 6])

def loopBody298_45 : HolLoopProg 64 :=
.mark loopBody298_44

def loopBody298_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody298_47 : HolLoopProg 64 :=
.mark loopBody298_46

def loopBody298_48 : HolLoopProg 64 :=
.seq loopBody298_47 loopBody298_1

def loopBody298_49 : HolLoopProg 64 :=
.mark loopBody298_48

def loopBody298_50 : HolLoopProg 64 :=
.seq loopBody298_45 loopBody298_49

def loopBody298_51 : HolLoopProg 64 :=
.mark loopBody298_50

def loopBody298_52 : HolLoopProg 64 :=
.seq loopBody298_43 loopBody298_51

def loopBody298_53 : HolLoopProg 64 :=
.mark loopBody298_52

def loopBody298_54 : HolLoopProg 64 :=
.seq loopBody298_41 loopBody298_53

def loopBody298_55 : HolLoopProg 64 :=
.mark loopBody298_54

def loopBody298_56 : HolLoopProg 64 :=
.seq loopBody298_29 loopBody298_55

def loopBody298_57 : HolLoopProg 64 :=
.mark loopBody298_56

def loopBody298_58 : HolLoopProg 64 :=
.seq loopBody298_1 loopBody298_57

def loopBody298_59 : HolLoopProg 64 :=
.mark loopBody298_58

def loopBody298_60 : HolLoopProg 64 :=
.seq loopBody298_1 loopBody298_59

def loopBody298_61 : HolLoopProg 64 :=
.mark loopBody298_60

def loopBody298_62 : HolLoopProg 64 :=
.seq loopBody298_15 loopBody298_61

def loopBody298_63 : HolLoopProg 64 :=
.mark loopBody298_62

def loopBody298_64 : HolLoopProg 64 :=
.seq loopBody298_1 loopBody298_63

def loopBody298_65 : HolLoopProg 64 :=
.mark loopBody298_64

def loopBody298_66 : HolLoopProg 64 :=
.seq loopBody298_1 loopBody298_65

def loopBody298_67 : HolLoopProg 64 :=
.mark loopBody298_66

def output298 : Nat × List Nat × HolLoopProg 64 :=
  (362, [0], loopBody298_67)
end InitECandidate.Proofs.FrontendStages.Loop
