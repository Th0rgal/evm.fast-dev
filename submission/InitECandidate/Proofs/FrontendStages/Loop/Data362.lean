import InitECandidate.Proofs.FrontendStages.Loop.Translate346
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody362_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody362_1 : HolLoopProg 64 :=
.mark loopBody362_0

def loopBody362_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 0)

def loopBody362_3 : HolLoopProg 64 :=
.mark loopBody362_2

def loopBody362_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody362_5 : HolLoopProg 64 :=
.mark loopBody362_4

def loopBody362_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 403) ([2]) (some (2, loopBody362_5, loopBody362_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody362_7 : HolLoopProg 64 :=
.mark loopBody362_6

def loopBody362_8 : HolLoopProg 64 :=
.seq loopBody362_7 loopBody362_1

def loopBody362_9 : HolLoopProg 64 :=
.mark loopBody362_8

def loopBody362_10 : HolLoopProg 64 :=
.seq loopBody362_3 loopBody362_9

def loopBody362_11 : HolLoopProg 64 :=
.mark loopBody362_10

def loopBody362_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.var 1)

def loopBody362_13 : HolLoopProg 64 :=
.mark loopBody362_12

def loopBody362_14 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 391) ([2]) (some (2, loopBody362_5, loopBody362_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody362_15 : HolLoopProg 64 :=
.mark loopBody362_14

def loopBody362_16 : HolLoopProg 64 :=
.seq loopBody362_15 loopBody362_1

def loopBody362_17 : HolLoopProg 64 :=
.mark loopBody362_16

def loopBody362_18 : HolLoopProg 64 :=
.seq loopBody362_13 loopBody362_17

def loopBody362_19 : HolLoopProg 64 :=
.mark loopBody362_18

def loopBody362_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 0#64])

def loopBody362_21 : HolLoopProg 64 :=
.mark loopBody362_20

def loopBody362_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 0#64]),
      Flapjack.HolLoopExp.const 1#64])

def loopBody362_23 : HolLoopProg 64 :=
.mark loopBody362_22

def loopBody362_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 3)

def loopBody362_25 : HolLoopProg 64 :=
.mark loopBody362_24

def loopBody362_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 2) 4

def loopBody362_27 : HolLoopProg 64 :=
.mark loopBody362_26

def loopBody362_28 : HolLoopProg 64 :=
.seq loopBody362_27 loopBody362_1

def loopBody362_29 : HolLoopProg 64 :=
.mark loopBody362_28

def loopBody362_30 : HolLoopProg 64 :=
.seq loopBody362_25 loopBody362_29

def loopBody362_31 : HolLoopProg 64 :=
.mark loopBody362_30

def loopBody362_32 : HolLoopProg 64 :=
.seq loopBody362_31 loopBody362_1

def loopBody362_33 : HolLoopProg 64 :=
.mark loopBody362_32

def loopBody362_34 : HolLoopProg 64 :=
.seq loopBody362_23 loopBody362_33

def loopBody362_35 : HolLoopProg 64 :=
.mark loopBody362_34

def loopBody362_36 : HolLoopProg 64 :=
.seq loopBody362_1 loopBody362_35

def loopBody362_37 : HolLoopProg 64 :=
.mark loopBody362_36

def loopBody362_38 : HolLoopProg 64 :=
.seq loopBody362_21 loopBody362_37

def loopBody362_39 : HolLoopProg 64 :=
.mark loopBody362_38

def loopBody362_40 : HolLoopProg 64 :=
.seq loopBody362_1 loopBody362_39

def loopBody362_41 : HolLoopProg 64 :=
.mark loopBody362_40

def loopBody362_42 : HolLoopProg 64 :=
.seq loopBody362_19 loopBody362_41

def loopBody362_43 : HolLoopProg 64 :=
.mark loopBody362_42

def loopBody362_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody362_45 : HolLoopProg 64 :=
.mark loopBody362_44

def loopBody362_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody362_47 : HolLoopProg 64 :=
.mark loopBody362_46

def loopBody362_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody362_49 : HolLoopProg 64 :=
.mark loopBody362_48

def loopBody362_50 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ln)) (some 419) ([3, 4]) (some (3, loopBody362_49, loopBody362_1, (Flapjack.Spt.ln)))

def loopBody362_51 : HolLoopProg 64 :=
.mark loopBody362_50

def loopBody362_52 : HolLoopProg 64 :=
.seq loopBody362_51 loopBody362_1

def loopBody362_53 : HolLoopProg 64 :=
.mark loopBody362_52

def loopBody362_54 : HolLoopProg 64 :=
.seq loopBody362_47 loopBody362_53

def loopBody362_55 : HolLoopProg 64 :=
.mark loopBody362_54

def loopBody362_56 : HolLoopProg 64 :=
.seq loopBody362_45 loopBody362_55

def loopBody362_57 : HolLoopProg 64 :=
.mark loopBody362_56

def loopBody362_58 : HolLoopProg 64 :=
.seq loopBody362_1 loopBody362_57

def loopBody362_59 : HolLoopProg 64 :=
.mark loopBody362_58

def loopBody362_60 : HolLoopProg 64 :=
.seq loopBody362_1 loopBody362_59

def loopBody362_61 : HolLoopProg 64 :=
.mark loopBody362_60

def loopBody362_62 : HolLoopProg 64 :=
.seq loopBody362_43 loopBody362_61

def loopBody362_63 : HolLoopProg 64 :=
.mark loopBody362_62

def loopBody362_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody362_65 : HolLoopProg 64 :=
.mark loopBody362_64

def loopBody362_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [2]

def loopBody362_67 : HolLoopProg 64 :=
.mark loopBody362_66

def loopBody362_68 : HolLoopProg 64 :=
.seq loopBody362_67 loopBody362_1

def loopBody362_69 : HolLoopProg 64 :=
.mark loopBody362_68

def loopBody362_70 : HolLoopProg 64 :=
.seq loopBody362_65 loopBody362_69

def loopBody362_71 : HolLoopProg 64 :=
.mark loopBody362_70

def loopBody362_72 : HolLoopProg 64 :=
.seq loopBody362_63 loopBody362_71

def loopBody362_73 : HolLoopProg 64 :=
.mark loopBody362_72

def loopBody362_74 : HolLoopProg 64 :=
.seq loopBody362_11 loopBody362_73

def loopBody362_75 : HolLoopProg 64 :=
.mark loopBody362_74

def loopBody362_76 : HolLoopProg 64 :=
.seq loopBody362_1 loopBody362_75

def loopBody362_77 : HolLoopProg 64 :=
.mark loopBody362_76

def loopBody362_78 : HolLoopProg 64 :=
.seq loopBody362_1 loopBody362_77

def loopBody362_79 : HolLoopProg 64 :=
.mark loopBody362_78

def output362 : Nat × List Nat × HolLoopProg 64 :=
  (426, [0], loopBody362_79)
end InitECandidate.Proofs.FrontendStages.Loop
