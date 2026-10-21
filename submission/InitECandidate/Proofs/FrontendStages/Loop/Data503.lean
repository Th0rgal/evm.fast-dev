import InitECandidate.Proofs.FrontendStages.Loop.Translate487
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody503_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody503_1 : HolLoopProg 64 :=
.mark loopBody503_0

def loopBody503_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 5#64)

def loopBody503_3 : HolLoopProg 64 :=
.mark loopBody503_2

def loopBody503_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody503_5 : HolLoopProg 64 :=
.mark loopBody503_4

def loopBody503_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody503_5, loopBody503_1, (Flapjack.Spt.ln)))

def loopBody503_7 : HolLoopProg 64 :=
.mark loopBody503_6

def loopBody503_8 : HolLoopProg 64 :=
.seq loopBody503_7 loopBody503_1

def loopBody503_9 : HolLoopProg 64 :=
.mark loopBody503_8

def loopBody503_10 : HolLoopProg 64 :=
.seq loopBody503_3 loopBody503_9

def loopBody503_11 : HolLoopProg 64 :=
.mark loopBody503_10

def loopBody503_12 : HolLoopProg 64 :=
.seq loopBody503_1 loopBody503_11

def loopBody503_13 : HolLoopProg 64 :=
.mark loopBody503_12

def loopBody503_14 : HolLoopProg 64 :=
.seq loopBody503_1 loopBody503_13

def loopBody503_15 : HolLoopProg 64 :=
.mark loopBody503_14

def loopBody503_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.add
            [Flapjack.HolLoopExp.load
                (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                  [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
              Flapjack.HolLoopExp.const 112#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody503_17 : HolLoopProg 64 :=
.mark loopBody503_16

def loopBody503_18 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 403) ([2]) (some (2, loopBody503_5, loopBody503_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody503_19 : HolLoopProg 64 :=
.mark loopBody503_18

def loopBody503_20 : HolLoopProg 64 :=
.seq loopBody503_19 loopBody503_1

def loopBody503_21 : HolLoopProg 64 :=
.mark loopBody503_20

def loopBody503_22 : HolLoopProg 64 :=
.seq loopBody503_17 loopBody503_21

def loopBody503_23 : HolLoopProg 64 :=
.mark loopBody503_22

def loopBody503_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64]))

def loopBody503_25 : HolLoopProg 64 :=
.mark loopBody503_24

def loopBody503_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody503_27 : HolLoopProg 64 :=
.mark loopBody503_26

def loopBody503_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody503_29 : HolLoopProg 64 :=
.mark loopBody503_28

def loopBody503_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody503_31 : HolLoopProg 64 :=
.mark loopBody503_30

def loopBody503_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody503_33 : HolLoopProg 64 :=
.mark loopBody503_32

def loopBody503_34 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 472) ([3, 4, 5, 6]) (some (3, loopBody503_33, loopBody503_1, (Flapjack.Spt.ln)))

def loopBody503_35 : HolLoopProg 64 :=
.mark loopBody503_34

def loopBody503_36 : HolLoopProg 64 :=
.seq loopBody503_35 loopBody503_1

def loopBody503_37 : HolLoopProg 64 :=
.mark loopBody503_36

def loopBody503_38 : HolLoopProg 64 :=
.seq loopBody503_31 loopBody503_37

def loopBody503_39 : HolLoopProg 64 :=
.mark loopBody503_38

def loopBody503_40 : HolLoopProg 64 :=
.seq loopBody503_29 loopBody503_39

def loopBody503_41 : HolLoopProg 64 :=
.mark loopBody503_40

def loopBody503_42 : HolLoopProg 64 :=
.seq loopBody503_27 loopBody503_41

def loopBody503_43 : HolLoopProg 64 :=
.mark loopBody503_42

def loopBody503_44 : HolLoopProg 64 :=
.seq loopBody503_25 loopBody503_43

def loopBody503_45 : HolLoopProg 64 :=
.mark loopBody503_44

def loopBody503_46 : HolLoopProg 64 :=
.seq loopBody503_1 loopBody503_45

def loopBody503_47 : HolLoopProg 64 :=
.mark loopBody503_46

def loopBody503_48 : HolLoopProg 64 :=
.seq loopBody503_1 loopBody503_47

def loopBody503_49 : HolLoopProg 64 :=
.mark loopBody503_48

def loopBody503_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody503_51 : HolLoopProg 64 :=
.mark loopBody503_50

def loopBody503_52 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 486) ([3]) (some (3, loopBody503_33, loopBody503_1, (Flapjack.Spt.ln)))

def loopBody503_53 : HolLoopProg 64 :=
.mark loopBody503_52

def loopBody503_54 : HolLoopProg 64 :=
.seq loopBody503_53 loopBody503_1

def loopBody503_55 : HolLoopProg 64 :=
.mark loopBody503_54

def loopBody503_56 : HolLoopProg 64 :=
.seq loopBody503_51 loopBody503_55

def loopBody503_57 : HolLoopProg 64 :=
.mark loopBody503_56

def loopBody503_58 : HolLoopProg 64 :=
.seq loopBody503_1 loopBody503_57

def loopBody503_59 : HolLoopProg 64 :=
.mark loopBody503_58

def loopBody503_60 : HolLoopProg 64 :=
.seq loopBody503_1 loopBody503_59

def loopBody503_61 : HolLoopProg 64 :=
.mark loopBody503_60

def loopBody503_62 : HolLoopProg 64 :=
.seq loopBody503_49 loopBody503_61

def loopBody503_63 : HolLoopProg 64 :=
.mark loopBody503_62

def loopBody503_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody503_65 : HolLoopProg 64 :=
.mark loopBody503_64

def loopBody503_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody503_67 : HolLoopProg 64 :=
.mark loopBody503_66

def loopBody503_68 : HolLoopProg 64 :=
.seq loopBody503_67 loopBody503_1

def loopBody503_69 : HolLoopProg 64 :=
.mark loopBody503_68

def loopBody503_70 : HolLoopProg 64 :=
.seq loopBody503_65 loopBody503_69

def loopBody503_71 : HolLoopProg 64 :=
.mark loopBody503_70

def loopBody503_72 : HolLoopProg 64 :=
.seq loopBody503_63 loopBody503_71

def loopBody503_73 : HolLoopProg 64 :=
.mark loopBody503_72

def loopBody503_74 : HolLoopProg 64 :=
.seq loopBody503_23 loopBody503_73

def loopBody503_75 : HolLoopProg 64 :=
.mark loopBody503_74

def loopBody503_76 : HolLoopProg 64 :=
.seq loopBody503_1 loopBody503_75

def loopBody503_77 : HolLoopProg 64 :=
.mark loopBody503_76

def loopBody503_78 : HolLoopProg 64 :=
.seq loopBody503_1 loopBody503_77

def loopBody503_79 : HolLoopProg 64 :=
.mark loopBody503_78

def loopBody503_80 : HolLoopProg 64 :=
.seq loopBody503_15 loopBody503_79

def loopBody503_81 : HolLoopProg 64 :=
.mark loopBody503_80

def output503 : Nat × List Nat × HolLoopProg 64 :=
  (567, [], loopBody503_81)
end InitECandidate.Proofs.FrontendStages.Loop
