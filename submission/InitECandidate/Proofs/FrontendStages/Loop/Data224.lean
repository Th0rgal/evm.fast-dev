import InitECandidate.Proofs.FrontendStages.Loop.Translate208
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody224_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody224_1 : HolLoopProg 64 :=
.mark loopBody224_0

def loopBody224_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 3])

def loopBody224_3 : HolLoopProg 64 :=
.mark loopBody224_2

def loopBody224_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody224_5 : HolLoopProg 64 :=
.mark loopBody224_4

def loopBody224_6 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody224_5, loopBody224_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody224_7 : HolLoopProg 64 :=
.mark loopBody224_6

def loopBody224_8 : HolLoopProg 64 :=
.seq loopBody224_7 loopBody224_1

def loopBody224_9 : HolLoopProg 64 :=
.mark loopBody224_8

def loopBody224_10 : HolLoopProg 64 :=
.seq loopBody224_3 loopBody224_9

def loopBody224_11 : HolLoopProg 64 :=
.mark loopBody224_10

def loopBody224_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody224_13 : HolLoopProg 64 :=
.mark loopBody224_12

def loopBody224_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody224_15 : HolLoopProg 64 :=
.mark loopBody224_14

def loopBody224_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody224_17 : HolLoopProg 64 :=
.mark loopBody224_16

def loopBody224_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody224_19 : HolLoopProg 64 :=
.mark loopBody224_18

def loopBody224_20 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([6, 7, 8]) (some (6, loopBody224_19, loopBody224_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody224_21 : HolLoopProg 64 :=
.mark loopBody224_20

def loopBody224_22 : HolLoopProg 64 :=
.seq loopBody224_21 loopBody224_1

def loopBody224_23 : HolLoopProg 64 :=
.mark loopBody224_22

def loopBody224_24 : HolLoopProg 64 :=
.seq loopBody224_17 loopBody224_23

def loopBody224_25 : HolLoopProg 64 :=
.mark loopBody224_24

def loopBody224_26 : HolLoopProg 64 :=
.seq loopBody224_15 loopBody224_25

def loopBody224_27 : HolLoopProg 64 :=
.mark loopBody224_26

def loopBody224_28 : HolLoopProg 64 :=
.seq loopBody224_13 loopBody224_27

def loopBody224_29 : HolLoopProg 64 :=
.mark loopBody224_28

def loopBody224_30 : HolLoopProg 64 :=
.seq loopBody224_1 loopBody224_29

def loopBody224_31 : HolLoopProg 64 :=
.mark loopBody224_30

def loopBody224_32 : HolLoopProg 64 :=
.seq loopBody224_1 loopBody224_31

def loopBody224_33 : HolLoopProg 64 :=
.mark loopBody224_32

def loopBody224_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 1])

def loopBody224_35 : HolLoopProg 64 :=
.mark loopBody224_34

def loopBody224_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody224_37 : HolLoopProg 64 :=
.mark loopBody224_36

def loopBody224_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody224_39 : HolLoopProg 64 :=
.mark loopBody224_38

def loopBody224_40 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 77) ([6, 7, 8]) (some (6, loopBody224_19, loopBody224_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody224_41 : HolLoopProg 64 :=
.mark loopBody224_40

def loopBody224_42 : HolLoopProg 64 :=
.seq loopBody224_41 loopBody224_1

def loopBody224_43 : HolLoopProg 64 :=
.mark loopBody224_42

def loopBody224_44 : HolLoopProg 64 :=
.seq loopBody224_39 loopBody224_43

def loopBody224_45 : HolLoopProg 64 :=
.mark loopBody224_44

def loopBody224_46 : HolLoopProg 64 :=
.seq loopBody224_37 loopBody224_45

def loopBody224_47 : HolLoopProg 64 :=
.mark loopBody224_46

def loopBody224_48 : HolLoopProg 64 :=
.seq loopBody224_35 loopBody224_47

def loopBody224_49 : HolLoopProg 64 :=
.mark loopBody224_48

def loopBody224_50 : HolLoopProg 64 :=
.seq loopBody224_1 loopBody224_49

def loopBody224_51 : HolLoopProg 64 :=
.mark loopBody224_50

def loopBody224_52 : HolLoopProg 64 :=
.seq loopBody224_1 loopBody224_51

def loopBody224_53 : HolLoopProg 64 :=
.mark loopBody224_52

def loopBody224_54 : HolLoopProg 64 :=
.seq loopBody224_33 loopBody224_53

def loopBody224_55 : HolLoopProg 64 :=
.mark loopBody224_54

def loopBody224_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody224_57 : HolLoopProg 64 :=
.mark loopBody224_56

def loopBody224_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody224_59 : HolLoopProg 64 :=
.mark loopBody224_58

def loopBody224_60 : HolLoopProg 64 :=
.seq loopBody224_59 loopBody224_1

def loopBody224_61 : HolLoopProg 64 :=
.mark loopBody224_60

def loopBody224_62 : HolLoopProg 64 :=
.seq loopBody224_57 loopBody224_61

def loopBody224_63 : HolLoopProg 64 :=
.mark loopBody224_62

def loopBody224_64 : HolLoopProg 64 :=
.seq loopBody224_55 loopBody224_63

def loopBody224_65 : HolLoopProg 64 :=
.mark loopBody224_64

def loopBody224_66 : HolLoopProg 64 :=
.seq loopBody224_11 loopBody224_65

def loopBody224_67 : HolLoopProg 64 :=
.mark loopBody224_66

def loopBody224_68 : HolLoopProg 64 :=
.seq loopBody224_1 loopBody224_67

def loopBody224_69 : HolLoopProg 64 :=
.mark loopBody224_68

def loopBody224_70 : HolLoopProg 64 :=
.seq loopBody224_1 loopBody224_69

def loopBody224_71 : HolLoopProg 64 :=
.mark loopBody224_70

def output224 : Nat × List Nat × HolLoopProg 64 :=
  (288, [0, 1, 2, 3], loopBody224_71)
end InitECandidate.Proofs.FrontendStages.Loop
