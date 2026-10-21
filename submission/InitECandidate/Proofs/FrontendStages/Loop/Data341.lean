import InitECandidate.Proofs.FrontendStages.Loop.Translate325
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody341_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody341_1 : HolLoopProg 64 :=
.mark loopBody341_0

def loopBody341_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody341_3 : HolLoopProg 64 :=
.mark loopBody341_2

def loopBody341_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody341_5 : HolLoopProg 64 :=
.mark loopBody341_4

def loopBody341_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody341_7 : HolLoopProg 64 :=
.mark loopBody341_6

def loopBody341_8 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 186) ([5, 6]) (some (5, loopBody341_7, loopBody341_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody341_9 : HolLoopProg 64 :=
.mark loopBody341_8

def loopBody341_10 : HolLoopProg 64 :=
.seq loopBody341_9 loopBody341_1

def loopBody341_11 : HolLoopProg 64 :=
.mark loopBody341_10

def loopBody341_12 : HolLoopProg 64 :=
.seq loopBody341_5 loopBody341_11

def loopBody341_13 : HolLoopProg 64 :=
.mark loopBody341_12

def loopBody341_14 : HolLoopProg 64 :=
.seq loopBody341_3 loopBody341_13

def loopBody341_15 : HolLoopProg 64 :=
.mark loopBody341_14

def loopBody341_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody341_17 : HolLoopProg 64 :=
.mark loopBody341_16

def loopBody341_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody341_19 : HolLoopProg 64 :=
.mark loopBody341_18

def loopBody341_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody341_21 : HolLoopProg 64 :=
.mark loopBody341_20

def loopBody341_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody341_23 : HolLoopProg 64 :=
.mark loopBody341_22

def loopBody341_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.RegImm.reg 7) loopBody341_21 loopBody341_23 (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody341_25 : HolLoopProg 64 :=
.mark loopBody341_24

def loopBody341_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody341_27 : HolLoopProg 64 :=
.mark loopBody341_26

def loopBody341_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody341_29 : HolLoopProg 64 :=
.mark loopBody341_28

def loopBody341_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5, 6]

def loopBody341_31 : HolLoopProg 64 :=
.mark loopBody341_30

def loopBody341_32 : HolLoopProg 64 :=
.seq loopBody341_31 loopBody341_1

def loopBody341_33 : HolLoopProg 64 :=
.mark loopBody341_32

def loopBody341_34 : HolLoopProg 64 :=
.seq loopBody341_23 loopBody341_33

def loopBody341_35 : HolLoopProg 64 :=
.mark loopBody341_34

def loopBody341_36 : HolLoopProg 64 :=
.seq loopBody341_29 loopBody341_35

def loopBody341_37 : HolLoopProg 64 :=
.mark loopBody341_36

def loopBody341_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody341_37 loopBody341_1 (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody341_39 : HolLoopProg 64 :=
.mark loopBody341_38

def loopBody341_40 : HolLoopProg 64 :=
.seq loopBody341_39 loopBody341_1

def loopBody341_41 : HolLoopProg 64 :=
.mark loopBody341_40

def loopBody341_42 : HolLoopProg 64 :=
.seq loopBody341_27 loopBody341_41

def loopBody341_43 : HolLoopProg 64 :=
.mark loopBody341_42

def loopBody341_44 : HolLoopProg 64 :=
.seq loopBody341_25 loopBody341_43

def loopBody341_45 : HolLoopProg 64 :=
.mark loopBody341_44

def loopBody341_46 : HolLoopProg 64 :=
.seq loopBody341_19 loopBody341_45

def loopBody341_47 : HolLoopProg 64 :=
.mark loopBody341_46

def loopBody341_48 : HolLoopProg 64 :=
.seq loopBody341_17 loopBody341_47

def loopBody341_49 : HolLoopProg 64 :=
.mark loopBody341_48

def loopBody341_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody341_51 : HolLoopProg 64 :=
.mark loopBody341_50

def loopBody341_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody341_53 : HolLoopProg 64 :=
.mark loopBody341_52

def loopBody341_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody341_55 : HolLoopProg 64 :=
.mark loopBody341_54

def loopBody341_56 : HolLoopProg 64 :=
.call (some ([5, 6], Flapjack.Spt.ln)) (some 186) ([7, 8]) (some (7, loopBody341_55, loopBody341_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody341_57 : HolLoopProg 64 :=
.mark loopBody341_56

def loopBody341_58 : HolLoopProg 64 :=
.seq loopBody341_57 loopBody341_1

def loopBody341_59 : HolLoopProg 64 :=
.mark loopBody341_58

def loopBody341_60 : HolLoopProg 64 :=
.seq loopBody341_53 loopBody341_59

def loopBody341_61 : HolLoopProg 64 :=
.mark loopBody341_60

def loopBody341_62 : HolLoopProg 64 :=
.seq loopBody341_51 loopBody341_61

def loopBody341_63 : HolLoopProg 64 :=
.mark loopBody341_62

def loopBody341_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody341_65 : HolLoopProg 64 :=
.mark loopBody341_64

def loopBody341_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7, 8]

def loopBody341_67 : HolLoopProg 64 :=
.mark loopBody341_66

def loopBody341_68 : HolLoopProg 64 :=
.seq loopBody341_67 loopBody341_1

def loopBody341_69 : HolLoopProg 64 :=
.mark loopBody341_68

def loopBody341_70 : HolLoopProg 64 :=
.seq loopBody341_27 loopBody341_69

def loopBody341_71 : HolLoopProg 64 :=
.mark loopBody341_70

def loopBody341_72 : HolLoopProg 64 :=
.seq loopBody341_65 loopBody341_71

def loopBody341_73 : HolLoopProg 64 :=
.mark loopBody341_72

def loopBody341_74 : HolLoopProg 64 :=
.seq loopBody341_63 loopBody341_73

def loopBody341_75 : HolLoopProg 64 :=
.mark loopBody341_74

def loopBody341_76 : HolLoopProg 64 :=
.seq loopBody341_1 loopBody341_75

def loopBody341_77 : HolLoopProg 64 :=
.mark loopBody341_76

def loopBody341_78 : HolLoopProg 64 :=
.seq loopBody341_1 loopBody341_77

def loopBody341_79 : HolLoopProg 64 :=
.mark loopBody341_78

def loopBody341_80 : HolLoopProg 64 :=
.seq loopBody341_1 loopBody341_79

def loopBody341_81 : HolLoopProg 64 :=
.mark loopBody341_80

def loopBody341_82 : HolLoopProg 64 :=
.seq loopBody341_1 loopBody341_81

def loopBody341_83 : HolLoopProg 64 :=
.mark loopBody341_82

def loopBody341_84 : HolLoopProg 64 :=
.seq loopBody341_49 loopBody341_83

def loopBody341_85 : HolLoopProg 64 :=
.mark loopBody341_84

def loopBody341_86 : HolLoopProg 64 :=
.seq loopBody341_15 loopBody341_85

def loopBody341_87 : HolLoopProg 64 :=
.mark loopBody341_86

def loopBody341_88 : HolLoopProg 64 :=
.seq loopBody341_1 loopBody341_87

def loopBody341_89 : HolLoopProg 64 :=
.mark loopBody341_88

def loopBody341_90 : HolLoopProg 64 :=
.seq loopBody341_1 loopBody341_89

def loopBody341_91 : HolLoopProg 64 :=
.mark loopBody341_90

def loopBody341_92 : HolLoopProg 64 :=
.seq loopBody341_1 loopBody341_91

def loopBody341_93 : HolLoopProg 64 :=
.mark loopBody341_92

def loopBody341_94 : HolLoopProg 64 :=
.seq loopBody341_1 loopBody341_93

def loopBody341_95 : HolLoopProg 64 :=
.mark loopBody341_94

def output341 : Nat × List Nat × HolLoopProg 64 :=
  (405, [0, 1, 2], loopBody341_95)
end InitECandidate.Proofs.FrontendStages.Loop
