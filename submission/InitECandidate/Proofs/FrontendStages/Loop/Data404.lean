import InitECandidate.Proofs.FrontendStages.Loop.Translate388
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody404_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody404_1 : HolLoopProg 64 :=
.mark loopBody404_0

def loopBody404_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
        Flapjack.HolLoopExp.const 192#64]))

def loopBody404_3 : HolLoopProg 64 :=
.mark loopBody404_2

def loopBody404_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody404_5 : HolLoopProg 64 :=
.mark loopBody404_4

def loopBody404_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody404_7 : HolLoopProg 64 :=
.mark loopBody404_6

def loopBody404_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody404_9 : HolLoopProg 64 :=
.mark loopBody404_8

def loopBody404_10 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 92) ([3, 4]) (some (3, loopBody404_9, loopBody404_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody404_11 : HolLoopProg 64 :=
.mark loopBody404_10

def loopBody404_12 : HolLoopProg 64 :=
.seq loopBody404_11 loopBody404_1

def loopBody404_13 : HolLoopProg 64 :=
.mark loopBody404_12

def loopBody404_14 : HolLoopProg 64 :=
.seq loopBody404_7 loopBody404_13

def loopBody404_15 : HolLoopProg 64 :=
.mark loopBody404_14

def loopBody404_16 : HolLoopProg 64 :=
.seq loopBody404_5 loopBody404_15

def loopBody404_17 : HolLoopProg 64 :=
.mark loopBody404_16

def loopBody404_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 64#64])

def loopBody404_19 : HolLoopProg 64 :=
.mark loopBody404_18

def loopBody404_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 64#64]),
      Flapjack.HolLoopExp.var 2])

def loopBody404_21 : HolLoopProg 64 :=
.mark loopBody404_20

def loopBody404_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody404_23 : HolLoopProg 64 :=
.mark loopBody404_22

def loopBody404_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 3) 5

def loopBody404_25 : HolLoopProg 64 :=
.mark loopBody404_24

def loopBody404_26 : HolLoopProg 64 :=
.seq loopBody404_25 loopBody404_1

def loopBody404_27 : HolLoopProg 64 :=
.mark loopBody404_26

def loopBody404_28 : HolLoopProg 64 :=
.seq loopBody404_23 loopBody404_27

def loopBody404_29 : HolLoopProg 64 :=
.mark loopBody404_28

def loopBody404_30 : HolLoopProg 64 :=
.seq loopBody404_29 loopBody404_1

def loopBody404_31 : HolLoopProg 64 :=
.mark loopBody404_30

def loopBody404_32 : HolLoopProg 64 :=
.seq loopBody404_21 loopBody404_31

def loopBody404_33 : HolLoopProg 64 :=
.mark loopBody404_32

def loopBody404_34 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_33

def loopBody404_35 : HolLoopProg 64 :=
.mark loopBody404_34

def loopBody404_36 : HolLoopProg 64 :=
.seq loopBody404_19 loopBody404_35

def loopBody404_37 : HolLoopProg 64 :=
.mark loopBody404_36

def loopBody404_38 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_37

def loopBody404_39 : HolLoopProg 64 :=
.mark loopBody404_38

def loopBody404_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 192#64])

def loopBody404_41 : HolLoopProg 64 :=
.mark loopBody404_40

def loopBody404_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2])

def loopBody404_43 : HolLoopProg 64 :=
.mark loopBody404_42

def loopBody404_44 : HolLoopProg 64 :=
.seq loopBody404_43 loopBody404_31

def loopBody404_45 : HolLoopProg 64 :=
.mark loopBody404_44

def loopBody404_46 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_45

def loopBody404_47 : HolLoopProg 64 :=
.mark loopBody404_46

def loopBody404_48 : HolLoopProg 64 :=
.seq loopBody404_41 loopBody404_47

def loopBody404_49 : HolLoopProg 64 :=
.mark loopBody404_48

def loopBody404_50 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_49

def loopBody404_51 : HolLoopProg 64 :=
.mark loopBody404_50

def loopBody404_52 : HolLoopProg 64 :=
.seq loopBody404_39 loopBody404_51

def loopBody404_53 : HolLoopProg 64 :=
.mark loopBody404_52

def loopBody404_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 72#64])

def loopBody404_55 : HolLoopProg 64 :=
.mark loopBody404_54

def loopBody404_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add
          [Flapjack.HolLoopExp.load
              (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
                [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
            Flapjack.HolLoopExp.const 72#64]),
      Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 2]])

def loopBody404_57 : HolLoopProg 64 :=
.mark loopBody404_56

def loopBody404_58 : HolLoopProg 64 :=
.seq loopBody404_57 loopBody404_31

def loopBody404_59 : HolLoopProg 64 :=
.mark loopBody404_58

def loopBody404_60 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_59

def loopBody404_61 : HolLoopProg 64 :=
.mark loopBody404_60

def loopBody404_62 : HolLoopProg 64 :=
.seq loopBody404_55 loopBody404_61

def loopBody404_63 : HolLoopProg 64 :=
.mark loopBody404_62

def loopBody404_64 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_63

def loopBody404_65 : HolLoopProg 64 :=
.mark loopBody404_64

def loopBody404_66 : HolLoopProg 64 :=
.seq loopBody404_53 loopBody404_65

def loopBody404_67 : HolLoopProg 64 :=
.mark loopBody404_66

def loopBody404_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody404_69 : HolLoopProg 64 :=
.mark loopBody404_68

def loopBody404_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody404_71 : HolLoopProg 64 :=
.mark loopBody404_70

def loopBody404_72 : HolLoopProg 64 :=
.seq loopBody404_71 loopBody404_1

def loopBody404_73 : HolLoopProg 64 :=
.mark loopBody404_72

def loopBody404_74 : HolLoopProg 64 :=
.seq loopBody404_69 loopBody404_73

def loopBody404_75 : HolLoopProg 64 :=
.mark loopBody404_74

def loopBody404_76 : HolLoopProg 64 :=
.seq loopBody404_67 loopBody404_75

def loopBody404_77 : HolLoopProg 64 :=
.mark loopBody404_76

def loopBody404_78 : HolLoopProg 64 :=
.seq loopBody404_17 loopBody404_77

def loopBody404_79 : HolLoopProg 64 :=
.mark loopBody404_78

def loopBody404_80 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_79

def loopBody404_81 : HolLoopProg 64 :=
.mark loopBody404_80

def loopBody404_82 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_81

def loopBody404_83 : HolLoopProg 64 :=
.mark loopBody404_82

def loopBody404_84 : HolLoopProg 64 :=
.seq loopBody404_3 loopBody404_83

def loopBody404_85 : HolLoopProg 64 :=
.mark loopBody404_84

def loopBody404_86 : HolLoopProg 64 :=
.seq loopBody404_1 loopBody404_85

def loopBody404_87 : HolLoopProg 64 :=
.mark loopBody404_86

def output404 : Nat × List Nat × HolLoopProg 64 :=
  (468, [0], loopBody404_87)
end InitECandidate.Proofs.FrontendStages.Loop
