import InitECandidate.Proofs.FrontendStages.Loop.Translate252
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody268_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody268_1 : HolLoopProg 64 :=
.mark loopBody268_0

def loopBody268_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody268_3 : HolLoopProg 64 :=
.mark loopBody268_2

def loopBody268_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody268_5 : HolLoopProg 64 :=
.mark loopBody268_4

def loopBody268_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody268_7 : HolLoopProg 64 :=
.mark loopBody268_6

def loopBody268_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody268_9 : HolLoopProg 64 :=
.mark loopBody268_8

def loopBody268_10 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.ln)) (some 331) ([5, 6, 7]) (some (5, loopBody268_9, loopBody268_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody268_11 : HolLoopProg 64 :=
.mark loopBody268_10

def loopBody268_12 : HolLoopProg 64 :=
.seq loopBody268_11 loopBody268_1

def loopBody268_13 : HolLoopProg 64 :=
.mark loopBody268_12

def loopBody268_14 : HolLoopProg 64 :=
.seq loopBody268_7 loopBody268_13

def loopBody268_15 : HolLoopProg 64 :=
.mark loopBody268_14

def loopBody268_16 : HolLoopProg 64 :=
.seq loopBody268_5 loopBody268_15

def loopBody268_17 : HolLoopProg 64 :=
.mark loopBody268_16

def loopBody268_18 : HolLoopProg 64 :=
.seq loopBody268_3 loopBody268_17

def loopBody268_19 : HolLoopProg 64 :=
.mark loopBody268_18

def loopBody268_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 32#64)

def loopBody268_21 : HolLoopProg 64 :=
.mark loopBody268_20

def loopBody268_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody268_23 : HolLoopProg 64 :=
.mark loopBody268_22

def loopBody268_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody268_25 : HolLoopProg 64 :=
.mark loopBody268_24

def loopBody268_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody268_27 : HolLoopProg 64 :=
.mark loopBody268_26

def loopBody268_28 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.RegImm.reg 7) loopBody268_25 loopBody268_27 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody268_29 : HolLoopProg 64 :=
.mark loopBody268_28

def loopBody268_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody268_31 : HolLoopProg 64 :=
.mark loopBody268_30

def loopBody268_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 13#64)

def loopBody268_33 : HolLoopProg 64 :=
.mark loopBody268_32

def loopBody268_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 5)

def loopBody268_35 : HolLoopProg 64 :=
.mark loopBody268_34

def loopBody268_36 : HolLoopProg 64 :=
.seq loopBody268_35 loopBody268_1

def loopBody268_37 : HolLoopProg 64 :=
.mark loopBody268_36

def loopBody268_38 : HolLoopProg 64 :=
.seq loopBody268_37 loopBody268_1

def loopBody268_39 : HolLoopProg 64 :=
.mark loopBody268_38

def loopBody268_40 : HolLoopProg 64 :=
.seq loopBody268_33 loopBody268_39

def loopBody268_41 : HolLoopProg 64 :=
.mark loopBody268_40

def loopBody268_42 : HolLoopProg 64 :=
.seq loopBody268_1 loopBody268_41

def loopBody268_43 : HolLoopProg 64 :=
.mark loopBody268_42

def loopBody268_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 6#64)

def loopBody268_45 : HolLoopProg 64 :=
.mark loopBody268_44

def loopBody268_46 : HolLoopProg 64 :=
.seq loopBody268_45 loopBody268_9

def loopBody268_47 : HolLoopProg 64 :=
.mark loopBody268_46

def loopBody268_48 : HolLoopProg 64 :=
.seq loopBody268_43 loopBody268_47

def loopBody268_49 : HolLoopProg 64 :=
.mark loopBody268_48

def loopBody268_50 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody268_49 loopBody268_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody268_51 : HolLoopProg 64 :=
.mark loopBody268_50

def loopBody268_52 : HolLoopProg 64 :=
.seq loopBody268_51 loopBody268_1

def loopBody268_53 : HolLoopProg 64 :=
.mark loopBody268_52

def loopBody268_54 : HolLoopProg 64 :=
.seq loopBody268_31 loopBody268_53

def loopBody268_55 : HolLoopProg 64 :=
.mark loopBody268_54

def loopBody268_56 : HolLoopProg 64 :=
.seq loopBody268_29 loopBody268_55

def loopBody268_57 : HolLoopProg 64 :=
.mark loopBody268_56

def loopBody268_58 : HolLoopProg 64 :=
.seq loopBody268_23 loopBody268_57

def loopBody268_59 : HolLoopProg 64 :=
.mark loopBody268_58

def loopBody268_60 : HolLoopProg 64 :=
.seq loopBody268_21 loopBody268_59

def loopBody268_61 : HolLoopProg 64 :=
.mark loopBody268_60

def loopBody268_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody268_63 : HolLoopProg 64 :=
.mark loopBody268_62

def loopBody268_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody268_65 : HolLoopProg 64 :=
.mark loopBody268_64

def loopBody268_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.call none (some 146) [5, 6] none

def loopBody268_67 : HolLoopProg 64 :=
.mark loopBody268_66

def loopBody268_68 : HolLoopProg 64 :=
.seq loopBody268_67 loopBody268_1

def loopBody268_69 : HolLoopProg 64 :=
.mark loopBody268_68

def loopBody268_70 : HolLoopProg 64 :=
.seq loopBody268_65 loopBody268_69

def loopBody268_71 : HolLoopProg 64 :=
.mark loopBody268_70

def loopBody268_72 : HolLoopProg 64 :=
.seq loopBody268_63 loopBody268_71

def loopBody268_73 : HolLoopProg 64 :=
.mark loopBody268_72

def loopBody268_74 : HolLoopProg 64 :=
.seq loopBody268_61 loopBody268_73

def loopBody268_75 : HolLoopProg 64 :=
.mark loopBody268_74

def loopBody268_76 : HolLoopProg 64 :=
.seq loopBody268_19 loopBody268_75

def loopBody268_77 : HolLoopProg 64 :=
.mark loopBody268_76

def loopBody268_78 : HolLoopProg 64 :=
.seq loopBody268_1 loopBody268_77

def loopBody268_79 : HolLoopProg 64 :=
.mark loopBody268_78

def loopBody268_80 : HolLoopProg 64 :=
.seq loopBody268_1 loopBody268_79

def loopBody268_81 : HolLoopProg 64 :=
.mark loopBody268_80

def loopBody268_82 : HolLoopProg 64 :=
.seq loopBody268_1 loopBody268_81

def loopBody268_83 : HolLoopProg 64 :=
.mark loopBody268_82

def loopBody268_84 : HolLoopProg 64 :=
.seq loopBody268_1 loopBody268_83

def loopBody268_85 : HolLoopProg 64 :=
.mark loopBody268_84

def output268 : Nat × List Nat × HolLoopProg 64 :=
  (332, [0, 1, 2], loopBody268_85)
end InitECandidate.Proofs.FrontendStages.Loop
