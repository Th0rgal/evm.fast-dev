import InitECandidate.Proofs.FrontendStages.Loop.Translate339
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody355_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody355_1 : HolLoopProg 64 :=
.mark loopBody355_0

def loopBody355_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 0)

def loopBody355_3 : HolLoopProg 64 :=
.mark loopBody355_2

def loopBody355_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody355_5 : HolLoopProg 64 :=
.mark loopBody355_4

def loopBody355_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody355_7 : HolLoopProg 64 :=
.mark loopBody355_6

def loopBody355_8 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 415) ([3, 4]) (some (3, loopBody355_7, loopBody355_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody355_9 : HolLoopProg 64 :=
.mark loopBody355_8

def loopBody355_10 : HolLoopProg 64 :=
.seq loopBody355_9 loopBody355_1

def loopBody355_11 : HolLoopProg 64 :=
.mark loopBody355_10

def loopBody355_12 : HolLoopProg 64 :=
.seq loopBody355_5 loopBody355_11

def loopBody355_13 : HolLoopProg 64 :=
.mark loopBody355_12

def loopBody355_14 : HolLoopProg 64 :=
.seq loopBody355_3 loopBody355_13

def loopBody355_15 : HolLoopProg 64 :=
.mark loopBody355_14

def loopBody355_16 : HolLoopProg 64 :=
.seq loopBody355_1 loopBody355_15

def loopBody355_17 : HolLoopProg 64 :=
.mark loopBody355_16

def loopBody355_18 : HolLoopProg 64 :=
.seq loopBody355_1 loopBody355_17

def loopBody355_19 : HolLoopProg 64 :=
.mark loopBody355_18

def loopBody355_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.var 1)

def loopBody355_21 : HolLoopProg 64 :=
.mark loopBody355_20

def loopBody355_22 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.ls PUnit.unit)) (some 412) ([3]) (some (3, loopBody355_7, loopBody355_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody355_23 : HolLoopProg 64 :=
.mark loopBody355_22

def loopBody355_24 : HolLoopProg 64 :=
.seq loopBody355_23 loopBody355_1

def loopBody355_25 : HolLoopProg 64 :=
.mark loopBody355_24

def loopBody355_26 : HolLoopProg 64 :=
.seq loopBody355_21 loopBody355_25

def loopBody355_27 : HolLoopProg 64 :=
.mark loopBody355_26

def loopBody355_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 2)

def loopBody355_29 : HolLoopProg 64 :=
.mark loopBody355_28

def loopBody355_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody355_31 : HolLoopProg 64 :=
.mark loopBody355_30

def loopBody355_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody355_33 : HolLoopProg 64 :=
.mark loopBody355_32

def loopBody355_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 0#64)

def loopBody355_35 : HolLoopProg 64 :=
.mark loopBody355_34

def loopBody355_36 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.RegImm.reg 5) loopBody355_33 loopBody355_35 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody355_37 : HolLoopProg 64 :=
.mark loopBody355_36

def loopBody355_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody355_39 : HolLoopProg 64 :=
.mark loopBody355_38

def loopBody355_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody355_41 : HolLoopProg 64 :=
.mark loopBody355_40

def loopBody355_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody355_43 : HolLoopProg 64 :=
.mark loopBody355_42

def loopBody355_44 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.ln)) (some 418) ([4]) (some (4, loopBody355_43, loopBody355_1, (Flapjack.Spt.ln)))

def loopBody355_45 : HolLoopProg 64 :=
.mark loopBody355_44

def loopBody355_46 : HolLoopProg 64 :=
.seq loopBody355_45 loopBody355_1

def loopBody355_47 : HolLoopProg 64 :=
.mark loopBody355_46

def loopBody355_48 : HolLoopProg 64 :=
.seq loopBody355_41 loopBody355_47

def loopBody355_49 : HolLoopProg 64 :=
.mark loopBody355_48

def loopBody355_50 : HolLoopProg 64 :=
.seq loopBody355_1 loopBody355_49

def loopBody355_51 : HolLoopProg 64 :=
.mark loopBody355_50

def loopBody355_52 : HolLoopProg 64 :=
.seq loopBody355_1 loopBody355_51

def loopBody355_53 : HolLoopProg 64 :=
.mark loopBody355_52

def loopBody355_54 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 0#64) loopBody355_53 loopBody355_1 (Flapjack.Spt.ln)

def loopBody355_55 : HolLoopProg 64 :=
.mark loopBody355_54

def loopBody355_56 : HolLoopProg 64 :=
.seq loopBody355_55 loopBody355_1

def loopBody355_57 : HolLoopProg 64 :=
.mark loopBody355_56

def loopBody355_58 : HolLoopProg 64 :=
.seq loopBody355_39 loopBody355_57

def loopBody355_59 : HolLoopProg 64 :=
.mark loopBody355_58

def loopBody355_60 : HolLoopProg 64 :=
.seq loopBody355_37 loopBody355_59

def loopBody355_61 : HolLoopProg 64 :=
.mark loopBody355_60

def loopBody355_62 : HolLoopProg 64 :=
.seq loopBody355_31 loopBody355_61

def loopBody355_63 : HolLoopProg 64 :=
.mark loopBody355_62

def loopBody355_64 : HolLoopProg 64 :=
.seq loopBody355_29 loopBody355_63

def loopBody355_65 : HolLoopProg 64 :=
.mark loopBody355_64

def loopBody355_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3 (Flapjack.HolLoopExp.const 0#64)

def loopBody355_67 : HolLoopProg 64 :=
.mark loopBody355_66

def loopBody355_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [3]

def loopBody355_69 : HolLoopProg 64 :=
.mark loopBody355_68

def loopBody355_70 : HolLoopProg 64 :=
.seq loopBody355_69 loopBody355_1

def loopBody355_71 : HolLoopProg 64 :=
.mark loopBody355_70

def loopBody355_72 : HolLoopProg 64 :=
.seq loopBody355_67 loopBody355_71

def loopBody355_73 : HolLoopProg 64 :=
.mark loopBody355_72

def loopBody355_74 : HolLoopProg 64 :=
.seq loopBody355_65 loopBody355_73

def loopBody355_75 : HolLoopProg 64 :=
.mark loopBody355_74

def loopBody355_76 : HolLoopProg 64 :=
.seq loopBody355_27 loopBody355_75

def loopBody355_77 : HolLoopProg 64 :=
.mark loopBody355_76

def loopBody355_78 : HolLoopProg 64 :=
.seq loopBody355_1 loopBody355_77

def loopBody355_79 : HolLoopProg 64 :=
.mark loopBody355_78

def loopBody355_80 : HolLoopProg 64 :=
.seq loopBody355_1 loopBody355_79

def loopBody355_81 : HolLoopProg 64 :=
.mark loopBody355_80

def loopBody355_82 : HolLoopProg 64 :=
.seq loopBody355_19 loopBody355_81

def loopBody355_83 : HolLoopProg 64 :=
.mark loopBody355_82

def output355 : Nat × List Nat × HolLoopProg 64 :=
  (419, [0, 1], loopBody355_83)
end InitECandidate.Proofs.FrontendStages.Loop
