import InitECandidate.Proofs.FrontendStages.Loop.Translate756
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody772_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody772_1 : HolLoopProg 64 :=
.mark loopBody772_0

def loopBody772_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub
    [Flapjack.HolLoopExp.var 1,
      Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 9#64]])

def loopBody772_3 : HolLoopProg 64 :=
.mark loopBody772_2

def loopBody772_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody772_5 : HolLoopProg 64 :=
.mark loopBody772_4

def loopBody772_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody772_7 : HolLoopProg 64 :=
.mark loopBody772_6

def loopBody772_8 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)) (some 180) ([4]) (some (4, loopBody772_7, loopBody772_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody772_9 : HolLoopProg 64 :=
.mark loopBody772_8

def loopBody772_10 : HolLoopProg 64 :=
.seq loopBody772_9 loopBody772_1

def loopBody772_11 : HolLoopProg 64 :=
.mark loopBody772_10

def loopBody772_12 : HolLoopProg 64 :=
.seq loopBody772_5 loopBody772_11

def loopBody772_13 : HolLoopProg 64 :=
.mark loopBody772_12

def loopBody772_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 3])

def loopBody772_15 : HolLoopProg 64 :=
.mark loopBody772_14

def loopBody772_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 9#64])

def loopBody772_17 : HolLoopProg 64 :=
.mark loopBody772_16

def loopBody772_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody772_19 : HolLoopProg 64 :=
.mark loopBody772_18

def loopBody772_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody772_21 : HolLoopProg 64 :=
.mark loopBody772_20

def loopBody772_22 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([5, 6, 7]) (some (5, loopBody772_21, loopBody772_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody772_23 : HolLoopProg 64 :=
.mark loopBody772_22

def loopBody772_24 : HolLoopProg 64 :=
.seq loopBody772_23 loopBody772_1

def loopBody772_25 : HolLoopProg 64 :=
.mark loopBody772_24

def loopBody772_26 : HolLoopProg 64 :=
.seq loopBody772_19 loopBody772_25

def loopBody772_27 : HolLoopProg 64 :=
.mark loopBody772_26

def loopBody772_28 : HolLoopProg 64 :=
.seq loopBody772_17 loopBody772_27

def loopBody772_29 : HolLoopProg 64 :=
.mark loopBody772_28

def loopBody772_30 : HolLoopProg 64 :=
.seq loopBody772_15 loopBody772_29

def loopBody772_31 : HolLoopProg 64 :=
.mark loopBody772_30

def loopBody772_32 : HolLoopProg 64 :=
.seq loopBody772_1 loopBody772_31

def loopBody772_33 : HolLoopProg 64 :=
.mark loopBody772_32

def loopBody772_34 : HolLoopProg 64 :=
.seq loopBody772_1 loopBody772_33

def loopBody772_35 : HolLoopProg 64 :=
.mark loopBody772_34

def loopBody772_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody772_37 : HolLoopProg 64 :=
.mark loopBody772_36

def loopBody772_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody772_39 : HolLoopProg 64 :=
.mark loopBody772_38

def loopBody772_40 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 178) ([5, 6]) (some (5, loopBody772_21, loopBody772_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody772_41 : HolLoopProg 64 :=
.mark loopBody772_40

def loopBody772_42 : HolLoopProg 64 :=
.seq loopBody772_41 loopBody772_1

def loopBody772_43 : HolLoopProg 64 :=
.mark loopBody772_42

def loopBody772_44 : HolLoopProg 64 :=
.seq loopBody772_39 loopBody772_43

def loopBody772_45 : HolLoopProg 64 :=
.mark loopBody772_44

def loopBody772_46 : HolLoopProg 64 :=
.seq loopBody772_37 loopBody772_45

def loopBody772_47 : HolLoopProg 64 :=
.mark loopBody772_46

def loopBody772_48 : HolLoopProg 64 :=
.seq loopBody772_1 loopBody772_47

def loopBody772_49 : HolLoopProg 64 :=
.mark loopBody772_48

def loopBody772_50 : HolLoopProg 64 :=
.seq loopBody772_1 loopBody772_49

def loopBody772_51 : HolLoopProg 64 :=
.mark loopBody772_50

def loopBody772_52 : HolLoopProg 64 :=
.seq loopBody772_35 loopBody772_51

def loopBody772_53 : HolLoopProg 64 :=
.mark loopBody772_52

def loopBody772_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.var 2])

def loopBody772_55 : HolLoopProg 64 :=
.mark loopBody772_54

def loopBody772_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody772_57 : HolLoopProg 64 :=
.mark loopBody772_56

def loopBody772_58 : HolLoopProg 64 :=
.seq loopBody772_57 loopBody772_1

def loopBody772_59 : HolLoopProg 64 :=
.mark loopBody772_58

def loopBody772_60 : HolLoopProg 64 :=
.seq loopBody772_55 loopBody772_59

def loopBody772_61 : HolLoopProg 64 :=
.mark loopBody772_60

def loopBody772_62 : HolLoopProg 64 :=
.seq loopBody772_53 loopBody772_61

def loopBody772_63 : HolLoopProg 64 :=
.mark loopBody772_62

def loopBody772_64 : HolLoopProg 64 :=
.seq loopBody772_13 loopBody772_63

def loopBody772_65 : HolLoopProg 64 :=
.mark loopBody772_64

def loopBody772_66 : HolLoopProg 64 :=
.seq loopBody772_1 loopBody772_65

def loopBody772_67 : HolLoopProg 64 :=
.mark loopBody772_66

def loopBody772_68 : HolLoopProg 64 :=
.seq loopBody772_1 loopBody772_67

def loopBody772_69 : HolLoopProg 64 :=
.mark loopBody772_68

def loopBody772_70 : HolLoopProg 64 :=
.seq loopBody772_3 loopBody772_69

def loopBody772_71 : HolLoopProg 64 :=
.mark loopBody772_70

def loopBody772_72 : HolLoopProg 64 :=
.seq loopBody772_1 loopBody772_71

def loopBody772_73 : HolLoopProg 64 :=
.mark loopBody772_72

def output772 : Nat × List Nat × HolLoopProg 64 :=
  (836, [0, 1], loopBody772_73)
end InitECandidate.Proofs.FrontendStages.Loop
