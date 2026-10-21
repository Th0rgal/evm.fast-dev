import InitECandidate.Proofs.FrontendStages.Loop.Translate793
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody809_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody809_1 : HolLoopProg 64 :=
.mark loopBody809_0

def loopBody809_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 1#64)

def loopBody809_3 : HolLoopProg 64 :=
.mark loopBody809_2

def loopBody809_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody809_5 : HolLoopProg 64 :=
.mark loopBody809_4

def loopBody809_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody809_7 : HolLoopProg 64 :=
.mark loopBody809_6

def loopBody809_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody809_9 : HolLoopProg 64 :=
.mark loopBody809_8

def loopBody809_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody809_11 : HolLoopProg 64 :=
.mark loopBody809_10

def loopBody809_12 : HolLoopProg 64 :=
.seq loopBody809_11 loopBody809_1

def loopBody809_13 : HolLoopProg 64 :=
.mark loopBody809_12

def loopBody809_14 : HolLoopProg 64 :=
.seq loopBody809_13 loopBody809_1

def loopBody809_15 : HolLoopProg 64 :=
.mark loopBody809_14

def loopBody809_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 0#64)

def loopBody809_17 : HolLoopProg 64 :=
.mark loopBody809_16

def loopBody809_18 : HolLoopProg 64 :=
.seq loopBody809_17 loopBody809_1

def loopBody809_19 : HolLoopProg 64 :=
.mark loopBody809_18

def loopBody809_20 : HolLoopProg 64 :=
.seq loopBody809_19 loopBody809_1

def loopBody809_21 : HolLoopProg 64 :=
.mark loopBody809_20

def loopBody809_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 536#64])

def loopBody809_23 : HolLoopProg 64 :=
.mark loopBody809_22

def loopBody809_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody809_25 : HolLoopProg 64 :=
.mark loopBody809_24

def loopBody809_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody809_27 : HolLoopProg 64 :=
.mark loopBody809_26

def loopBody809_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.store (Flapjack.HolLoopExp.var 4) 6

def loopBody809_29 : HolLoopProg 64 :=
.mark loopBody809_28

def loopBody809_30 : HolLoopProg 64 :=
.seq loopBody809_29 loopBody809_1

def loopBody809_31 : HolLoopProg 64 :=
.mark loopBody809_30

def loopBody809_32 : HolLoopProg 64 :=
.seq loopBody809_27 loopBody809_31

def loopBody809_33 : HolLoopProg 64 :=
.mark loopBody809_32

def loopBody809_34 : HolLoopProg 64 :=
.seq loopBody809_33 loopBody809_1

def loopBody809_35 : HolLoopProg 64 :=
.mark loopBody809_34

def loopBody809_36 : HolLoopProg 64 :=
.seq loopBody809_25 loopBody809_35

def loopBody809_37 : HolLoopProg 64 :=
.mark loopBody809_36

def loopBody809_38 : HolLoopProg 64 :=
.seq loopBody809_1 loopBody809_37

def loopBody809_39 : HolLoopProg 64 :=
.mark loopBody809_38

def loopBody809_40 : HolLoopProg 64 :=
.seq loopBody809_23 loopBody809_39

def loopBody809_41 : HolLoopProg 64 :=
.mark loopBody809_40

def loopBody809_42 : HolLoopProg 64 :=
.seq loopBody809_1 loopBody809_41

def loopBody809_43 : HolLoopProg 64 :=
.mark loopBody809_42

def loopBody809_44 : HolLoopProg 64 :=
.seq loopBody809_21 loopBody809_43

def loopBody809_45 : HolLoopProg 64 :=
.mark loopBody809_44

def loopBody809_46 : HolLoopProg 64 :=
.seq loopBody809_15 loopBody809_45

def loopBody809_47 : HolLoopProg 64 :=
.mark loopBody809_46

def loopBody809_48 : HolLoopProg 64 :=
.seq loopBody809_9 loopBody809_47

def loopBody809_49 : HolLoopProg 64 :=
.mark loopBody809_48

def loopBody809_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.imm 9#64) loopBody809_7 loopBody809_49 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)

def loopBody809_51 : HolLoopProg 64 :=
.mark loopBody809_50

def loopBody809_52 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 872) ([4]) (some (4, loopBody809_51, loopBody809_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))

def loopBody809_53 : HolLoopProg 64 :=
.mark loopBody809_52

def loopBody809_54 : HolLoopProg 64 :=
.seq loopBody809_53 loopBody809_1

def loopBody809_55 : HolLoopProg 64 :=
.mark loopBody809_54

def loopBody809_56 : HolLoopProg 64 :=
.seq loopBody809_5 loopBody809_55

def loopBody809_57 : HolLoopProg 64 :=
.mark loopBody809_56

def loopBody809_58 : HolLoopProg 64 :=
.seq loopBody809_1 loopBody809_57

def loopBody809_59 : HolLoopProg 64 :=
.mark loopBody809_58

def loopBody809_60 : HolLoopProg 64 :=
.seq loopBody809_1 loopBody809_59

def loopBody809_61 : HolLoopProg 64 :=
.mark loopBody809_60

def loopBody809_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 2)

def loopBody809_63 : HolLoopProg 64 :=
.mark loopBody809_62

def loopBody809_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody809_65 : HolLoopProg 64 :=
.mark loopBody809_64

def loopBody809_66 : HolLoopProg 64 :=
.seq loopBody809_65 loopBody809_1

def loopBody809_67 : HolLoopProg 64 :=
.mark loopBody809_66

def loopBody809_68 : HolLoopProg 64 :=
.seq loopBody809_63 loopBody809_67

def loopBody809_69 : HolLoopProg 64 :=
.mark loopBody809_68

def loopBody809_70 : HolLoopProg 64 :=
.seq loopBody809_61 loopBody809_69

def loopBody809_71 : HolLoopProg 64 :=
.mark loopBody809_70

def loopBody809_72 : HolLoopProg 64 :=
.seq loopBody809_3 loopBody809_71

def loopBody809_73 : HolLoopProg 64 :=
.mark loopBody809_72

def loopBody809_74 : HolLoopProg 64 :=
.seq loopBody809_1 loopBody809_73

def loopBody809_75 : HolLoopProg 64 :=
.mark loopBody809_74

def loopBody809_76 : HolLoopProg 64 :=
.seq loopBody809_1 loopBody809_75

def loopBody809_77 : HolLoopProg 64 :=
.mark loopBody809_76

def loopBody809_78 : HolLoopProg 64 :=
.seq loopBody809_1 loopBody809_77

def loopBody809_79 : HolLoopProg 64 :=
.mark loopBody809_78

def output809 : Nat × List Nat × HolLoopProg 64 :=
  (873, [0], loopBody809_79)
end InitECandidate.Proofs.FrontendStages.Loop
