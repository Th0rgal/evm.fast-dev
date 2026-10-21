import InitECandidate.Proofs.FrontendStages.Loop.Translate489
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody505_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody505_1 : HolLoopProg 64 :=
.mark loopBody505_0

def loopBody505_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody505_3 : HolLoopProg 64 :=
.mark loopBody505_2

def loopBody505_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody505_5 : HolLoopProg 64 :=
.mark loopBody505_4

def loopBody505_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody505_5, loopBody505_1, (Flapjack.Spt.ln)))

def loopBody505_7 : HolLoopProg 64 :=
.mark loopBody505_6

def loopBody505_8 : HolLoopProg 64 :=
.seq loopBody505_7 loopBody505_1

def loopBody505_9 : HolLoopProg 64 :=
.mark loopBody505_8

def loopBody505_10 : HolLoopProg 64 :=
.seq loopBody505_3 loopBody505_9

def loopBody505_11 : HolLoopProg 64 :=
.mark loopBody505_10

def loopBody505_12 : HolLoopProg 64 :=
.seq loopBody505_1 loopBody505_11

def loopBody505_13 : HolLoopProg 64 :=
.mark loopBody505_12

def loopBody505_14 : HolLoopProg 64 :=
.seq loopBody505_1 loopBody505_13

def loopBody505_15 : HolLoopProg 64 :=
.mark loopBody505_14

def loopBody505_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 568) ([]) (some (2, loopBody505_5, loopBody505_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody505_17 : HolLoopProg 64 :=
.mark loopBody505_16

def loopBody505_18 : HolLoopProg 64 :=
.seq loopBody505_17 loopBody505_1

def loopBody505_19 : HolLoopProg 64 :=
.mark loopBody505_18

def loopBody505_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64]))

def loopBody505_21 : HolLoopProg 64 :=
.mark loopBody505_20

def loopBody505_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody505_23 : HolLoopProg 64 :=
.mark loopBody505_22

def loopBody505_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody505_25 : HolLoopProg 64 :=
.mark loopBody505_24

def loopBody505_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 48#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody505_27 : HolLoopProg 64 :=
.mark loopBody505_26

def loopBody505_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody505_29 : HolLoopProg 64 :=
.mark loopBody505_28

def loopBody505_30 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 472) ([3, 4, 5, 6]) (some (3, loopBody505_29, loopBody505_1, (Flapjack.Spt.ln)))

def loopBody505_31 : HolLoopProg 64 :=
.mark loopBody505_30

def loopBody505_32 : HolLoopProg 64 :=
.seq loopBody505_31 loopBody505_1

def loopBody505_33 : HolLoopProg 64 :=
.mark loopBody505_32

def loopBody505_34 : HolLoopProg 64 :=
.seq loopBody505_27 loopBody505_33

def loopBody505_35 : HolLoopProg 64 :=
.mark loopBody505_34

def loopBody505_36 : HolLoopProg 64 :=
.seq loopBody505_25 loopBody505_35

def loopBody505_37 : HolLoopProg 64 :=
.mark loopBody505_36

def loopBody505_38 : HolLoopProg 64 :=
.seq loopBody505_23 loopBody505_37

def loopBody505_39 : HolLoopProg 64 :=
.mark loopBody505_38

def loopBody505_40 : HolLoopProg 64 :=
.seq loopBody505_21 loopBody505_39

def loopBody505_41 : HolLoopProg 64 :=
.mark loopBody505_40

def loopBody505_42 : HolLoopProg 64 :=
.seq loopBody505_1 loopBody505_41

def loopBody505_43 : HolLoopProg 64 :=
.mark loopBody505_42

def loopBody505_44 : HolLoopProg 64 :=
.seq loopBody505_1 loopBody505_43

def loopBody505_45 : HolLoopProg 64 :=
.mark loopBody505_44

def loopBody505_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 1#64)

def loopBody505_47 : HolLoopProg 64 :=
.mark loopBody505_46

def loopBody505_48 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 486) ([3]) (some (3, loopBody505_29, loopBody505_1, (Flapjack.Spt.ln)))

def loopBody505_49 : HolLoopProg 64 :=
.mark loopBody505_48

def loopBody505_50 : HolLoopProg 64 :=
.seq loopBody505_49 loopBody505_1

def loopBody505_51 : HolLoopProg 64 :=
.mark loopBody505_50

def loopBody505_52 : HolLoopProg 64 :=
.seq loopBody505_47 loopBody505_51

def loopBody505_53 : HolLoopProg 64 :=
.mark loopBody505_52

def loopBody505_54 : HolLoopProg 64 :=
.seq loopBody505_1 loopBody505_53

def loopBody505_55 : HolLoopProg 64 :=
.mark loopBody505_54

def loopBody505_56 : HolLoopProg 64 :=
.seq loopBody505_1 loopBody505_55

def loopBody505_57 : HolLoopProg 64 :=
.mark loopBody505_56

def loopBody505_58 : HolLoopProg 64 :=
.seq loopBody505_45 loopBody505_57

def loopBody505_59 : HolLoopProg 64 :=
.mark loopBody505_58

def loopBody505_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody505_61 : HolLoopProg 64 :=
.mark loopBody505_60

def loopBody505_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody505_63 : HolLoopProg 64 :=
.mark loopBody505_62

def loopBody505_64 : HolLoopProg 64 :=
.seq loopBody505_63 loopBody505_1

def loopBody505_65 : HolLoopProg 64 :=
.mark loopBody505_64

def loopBody505_66 : HolLoopProg 64 :=
.seq loopBody505_61 loopBody505_65

def loopBody505_67 : HolLoopProg 64 :=
.mark loopBody505_66

def loopBody505_68 : HolLoopProg 64 :=
.seq loopBody505_59 loopBody505_67

def loopBody505_69 : HolLoopProg 64 :=
.mark loopBody505_68

def loopBody505_70 : HolLoopProg 64 :=
.seq loopBody505_19 loopBody505_69

def loopBody505_71 : HolLoopProg 64 :=
.mark loopBody505_70

def loopBody505_72 : HolLoopProg 64 :=
.seq loopBody505_1 loopBody505_71

def loopBody505_73 : HolLoopProg 64 :=
.mark loopBody505_72

def loopBody505_74 : HolLoopProg 64 :=
.seq loopBody505_1 loopBody505_73

def loopBody505_75 : HolLoopProg 64 :=
.mark loopBody505_74

def loopBody505_76 : HolLoopProg 64 :=
.seq loopBody505_15 loopBody505_75

def loopBody505_77 : HolLoopProg 64 :=
.mark loopBody505_76

def output505 : Nat × List Nat × HolLoopProg 64 :=
  (569, [], loopBody505_77)
end InitECandidate.Proofs.FrontendStages.Loop
