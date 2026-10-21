import InitECandidate.Proofs.FrontendStages.Loop.Translate382
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody398_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody398_1 : HolLoopProg 64 :=
.mark loopBody398_0

def loopBody398_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.const 240#64])

def loopBody398_3 : HolLoopProg 64 :=
.mark loopBody398_2

def loopBody398_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody398_5 : HolLoopProg 64 :=
.mark loopBody398_4

def loopBody398_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody398_7 : HolLoopProg 64 :=
.mark loopBody398_6

def loopBody398_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody398_9 : HolLoopProg 64 :=
.mark loopBody398_8

def loopBody398_10 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))) (some 88) ([6, 7]) (some (6, loopBody398_9, loopBody398_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody398_11 : HolLoopProg 64 :=
.mark loopBody398_10

def loopBody398_12 : HolLoopProg 64 :=
.seq loopBody398_11 loopBody398_1

def loopBody398_13 : HolLoopProg 64 :=
.mark loopBody398_12

def loopBody398_14 : HolLoopProg 64 :=
.seq loopBody398_7 loopBody398_13

def loopBody398_15 : HolLoopProg 64 :=
.mark loopBody398_14

def loopBody398_16 : HolLoopProg 64 :=
.seq loopBody398_5 loopBody398_15

def loopBody398_17 : HolLoopProg 64 :=
.mark loopBody398_16

def loopBody398_18 : HolLoopProg 64 :=
.seq loopBody398_1 loopBody398_17

def loopBody398_19 : HolLoopProg 64 :=
.mark loopBody398_18

def loopBody398_20 : HolLoopProg 64 :=
.seq loopBody398_1 loopBody398_19

def loopBody398_21 : HolLoopProg 64 :=
.mark loopBody398_20

def loopBody398_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 4#64])

def loopBody398_23 : HolLoopProg 64 :=
.mark loopBody398_22

def loopBody398_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody398_25 : HolLoopProg 64 :=
.mark loopBody398_24

def loopBody398_26 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)) (some 89) ([6, 7]) (some (6, loopBody398_9, loopBody398_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))

def loopBody398_27 : HolLoopProg 64 :=
.mark loopBody398_26

def loopBody398_28 : HolLoopProg 64 :=
.seq loopBody398_27 loopBody398_1

def loopBody398_29 : HolLoopProg 64 :=
.mark loopBody398_28

def loopBody398_30 : HolLoopProg 64 :=
.seq loopBody398_25 loopBody398_29

def loopBody398_31 : HolLoopProg 64 :=
.mark loopBody398_30

def loopBody398_32 : HolLoopProg 64 :=
.seq loopBody398_23 loopBody398_31

def loopBody398_33 : HolLoopProg 64 :=
.mark loopBody398_32

def loopBody398_34 : HolLoopProg 64 :=
.seq loopBody398_1 loopBody398_33

def loopBody398_35 : HolLoopProg 64 :=
.mark loopBody398_34

def loopBody398_36 : HolLoopProg 64 :=
.seq loopBody398_1 loopBody398_35

def loopBody398_37 : HolLoopProg 64 :=
.mark loopBody398_36

def loopBody398_38 : HolLoopProg 64 :=
.seq loopBody398_21 loopBody398_37

def loopBody398_39 : HolLoopProg 64 :=
.mark loopBody398_38

def loopBody398_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 12#64])

def loopBody398_41 : HolLoopProg 64 :=
.mark loopBody398_40

def loopBody398_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody398_43 : HolLoopProg 64 :=
.mark loopBody398_42

def loopBody398_44 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 89) ([6, 7]) (some (6, loopBody398_9, loopBody398_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody398_45 : HolLoopProg 64 :=
.mark loopBody398_44

def loopBody398_46 : HolLoopProg 64 :=
.seq loopBody398_45 loopBody398_1

def loopBody398_47 : HolLoopProg 64 :=
.mark loopBody398_46

def loopBody398_48 : HolLoopProg 64 :=
.seq loopBody398_43 loopBody398_47

def loopBody398_49 : HolLoopProg 64 :=
.mark loopBody398_48

def loopBody398_50 : HolLoopProg 64 :=
.seq loopBody398_41 loopBody398_49

def loopBody398_51 : HolLoopProg 64 :=
.mark loopBody398_50

def loopBody398_52 : HolLoopProg 64 :=
.seq loopBody398_1 loopBody398_51

def loopBody398_53 : HolLoopProg 64 :=
.mark loopBody398_52

def loopBody398_54 : HolLoopProg 64 :=
.seq loopBody398_1 loopBody398_53

def loopBody398_55 : HolLoopProg 64 :=
.mark loopBody398_54

def loopBody398_56 : HolLoopProg 64 :=
.seq loopBody398_39 loopBody398_55

def loopBody398_57 : HolLoopProg 64 :=
.mark loopBody398_56

def loopBody398_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody398_59 : HolLoopProg 64 :=
.mark loopBody398_58

def loopBody398_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody398_61 : HolLoopProg 64 :=
.mark loopBody398_60

def loopBody398_62 : HolLoopProg 64 :=
.seq loopBody398_61 loopBody398_1

def loopBody398_63 : HolLoopProg 64 :=
.mark loopBody398_62

def loopBody398_64 : HolLoopProg 64 :=
.seq loopBody398_59 loopBody398_63

def loopBody398_65 : HolLoopProg 64 :=
.mark loopBody398_64

def loopBody398_66 : HolLoopProg 64 :=
.seq loopBody398_57 loopBody398_65

def loopBody398_67 : HolLoopProg 64 :=
.mark loopBody398_66

def loopBody398_68 : HolLoopProg 64 :=
.seq loopBody398_3 loopBody398_67

def loopBody398_69 : HolLoopProg 64 :=
.mark loopBody398_68

def loopBody398_70 : HolLoopProg 64 :=
.seq loopBody398_1 loopBody398_69

def loopBody398_71 : HolLoopProg 64 :=
.mark loopBody398_70

def output398 : Nat × List Nat × HolLoopProg 64 :=
  (462, [0, 1, 2, 3], loopBody398_71)
end InitECandidate.Proofs.FrontendStages.Loop
