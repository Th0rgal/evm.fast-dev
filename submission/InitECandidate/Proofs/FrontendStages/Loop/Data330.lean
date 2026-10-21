import InitECandidate.Proofs.FrontendStages.Loop.Translate314
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody330_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody330_1 : HolLoopProg 64 :=
.mark loopBody330_0

def loopBody330_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 0)

def loopBody330_3 : HolLoopProg 64 :=
.mark loopBody330_2

def loopBody330_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody330_5 : HolLoopProg 64 :=
.mark loopBody330_4

def loopBody330_6 : HolLoopProg 64 :=
.call (some ([1, 2, 3], Flapjack.Spt.ln)) (some 393) ([4]) (some (4, loopBody330_5, loopBody330_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody330_7 : HolLoopProg 64 :=
.mark loopBody330_6

def loopBody330_8 : HolLoopProg 64 :=
.seq loopBody330_7 loopBody330_1

def loopBody330_9 : HolLoopProg 64 :=
.mark loopBody330_8

def loopBody330_10 : HolLoopProg 64 :=
.seq loopBody330_3 loopBody330_9

def loopBody330_11 : HolLoopProg 64 :=
.mark loopBody330_10

def loopBody330_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 1)

def loopBody330_13 : HolLoopProg 64 :=
.mark loopBody330_12

def loopBody330_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody330_15 : HolLoopProg 64 :=
.mark loopBody330_14

def loopBody330_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody330_17 : HolLoopProg 64 :=
.mark loopBody330_16

def loopBody330_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody330_19 : HolLoopProg 64 :=
.mark loopBody330_18

def loopBody330_20 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 5 (Flapjack.RegImm.reg 6) loopBody330_17 loopBody330_19 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))

def loopBody330_21 : HolLoopProg 64 :=
.mark loopBody330_20

def loopBody330_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody330_23 : HolLoopProg 64 :=
.mark loopBody330_22

def loopBody330_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.const 1#64)

def loopBody330_25 : HolLoopProg 64 :=
.mark loopBody330_24

def loopBody330_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody330_27 : HolLoopProg 64 :=
.mark loopBody330_26

def loopBody330_28 : HolLoopProg 64 :=
.seq loopBody330_27 loopBody330_1

def loopBody330_29 : HolLoopProg 64 :=
.mark loopBody330_28

def loopBody330_30 : HolLoopProg 64 :=
.seq loopBody330_25 loopBody330_29

def loopBody330_31 : HolLoopProg 64 :=
.mark loopBody330_30

def loopBody330_32 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody330_31 loopBody330_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody330_33 : HolLoopProg 64 :=
.mark loopBody330_32

def loopBody330_34 : HolLoopProg 64 :=
.seq loopBody330_33 loopBody330_1

def loopBody330_35 : HolLoopProg 64 :=
.mark loopBody330_34

def loopBody330_36 : HolLoopProg 64 :=
.seq loopBody330_23 loopBody330_35

def loopBody330_37 : HolLoopProg 64 :=
.mark loopBody330_36

def loopBody330_38 : HolLoopProg 64 :=
.seq loopBody330_21 loopBody330_37

def loopBody330_39 : HolLoopProg 64 :=
.mark loopBody330_38

def loopBody330_40 : HolLoopProg 64 :=
.seq loopBody330_15 loopBody330_39

def loopBody330_41 : HolLoopProg 64 :=
.mark loopBody330_40

def loopBody330_42 : HolLoopProg 64 :=
.seq loopBody330_13 loopBody330_41

def loopBody330_43 : HolLoopProg 64 :=
.mark loopBody330_42

def loopBody330_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 56#64)

def loopBody330_45 : HolLoopProg 64 :=
.mark loopBody330_44

def loopBody330_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody330_47 : HolLoopProg 64 :=
.mark loopBody330_46

def loopBody330_48 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 68) ([5]) (some (5, loopBody330_47, loopBody330_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody330_49 : HolLoopProg 64 :=
.mark loopBody330_48

def loopBody330_50 : HolLoopProg 64 :=
.seq loopBody330_49 loopBody330_1

def loopBody330_51 : HolLoopProg 64 :=
.mark loopBody330_50

def loopBody330_52 : HolLoopProg 64 :=
.seq loopBody330_45 loopBody330_51

def loopBody330_53 : HolLoopProg 64 :=
.mark loopBody330_52

def loopBody330_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody330_55 : HolLoopProg 64 :=
.mark loopBody330_54

def loopBody330_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody330_57 : HolLoopProg 64 :=
.mark loopBody330_56

def loopBody330_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody330_59 : HolLoopProg 64 :=
.mark loopBody330_58

def loopBody330_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody330_61 : HolLoopProg 64 :=
.mark loopBody330_60

def loopBody330_62 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 329) ([6, 7, 8]) (some (6, loopBody330_61, loopBody330_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody330_63 : HolLoopProg 64 :=
.mark loopBody330_62

def loopBody330_64 : HolLoopProg 64 :=
.seq loopBody330_63 loopBody330_1

def loopBody330_65 : HolLoopProg 64 :=
.mark loopBody330_64

def loopBody330_66 : HolLoopProg 64 :=
.seq loopBody330_59 loopBody330_65

def loopBody330_67 : HolLoopProg 64 :=
.mark loopBody330_66

def loopBody330_68 : HolLoopProg 64 :=
.seq loopBody330_57 loopBody330_67

def loopBody330_69 : HolLoopProg 64 :=
.mark loopBody330_68

def loopBody330_70 : HolLoopProg 64 :=
.seq loopBody330_55 loopBody330_69

def loopBody330_71 : HolLoopProg 64 :=
.mark loopBody330_70

def loopBody330_72 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_71

def loopBody330_73 : HolLoopProg 64 :=
.mark loopBody330_72

def loopBody330_74 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_73

def loopBody330_75 : HolLoopProg 64 :=
.mark loopBody330_74

def loopBody330_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody330_77 : HolLoopProg 64 :=
.mark loopBody330_76

def loopBody330_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody330_79 : HolLoopProg 64 :=
.mark loopBody330_78

def loopBody330_80 : HolLoopProg 64 :=
.seq loopBody330_79 loopBody330_1

def loopBody330_81 : HolLoopProg 64 :=
.mark loopBody330_80

def loopBody330_82 : HolLoopProg 64 :=
.seq loopBody330_77 loopBody330_81

def loopBody330_83 : HolLoopProg 64 :=
.mark loopBody330_82

def loopBody330_84 : HolLoopProg 64 :=
.seq loopBody330_75 loopBody330_83

def loopBody330_85 : HolLoopProg 64 :=
.mark loopBody330_84

def loopBody330_86 : HolLoopProg 64 :=
.seq loopBody330_53 loopBody330_85

def loopBody330_87 : HolLoopProg 64 :=
.mark loopBody330_86

def loopBody330_88 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_87

def loopBody330_89 : HolLoopProg 64 :=
.mark loopBody330_88

def loopBody330_90 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_89

def loopBody330_91 : HolLoopProg 64 :=
.mark loopBody330_90

def loopBody330_92 : HolLoopProg 64 :=
.seq loopBody330_43 loopBody330_91

def loopBody330_93 : HolLoopProg 64 :=
.mark loopBody330_92

def loopBody330_94 : HolLoopProg 64 :=
.seq loopBody330_11 loopBody330_93

def loopBody330_95 : HolLoopProg 64 :=
.mark loopBody330_94

def loopBody330_96 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_95

def loopBody330_97 : HolLoopProg 64 :=
.mark loopBody330_96

def loopBody330_98 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_97

def loopBody330_99 : HolLoopProg 64 :=
.mark loopBody330_98

def loopBody330_100 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_99

def loopBody330_101 : HolLoopProg 64 :=
.mark loopBody330_100

def loopBody330_102 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_101

def loopBody330_103 : HolLoopProg 64 :=
.mark loopBody330_102

def loopBody330_104 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_103

def loopBody330_105 : HolLoopProg 64 :=
.mark loopBody330_104

def loopBody330_106 : HolLoopProg 64 :=
.seq loopBody330_1 loopBody330_105

def loopBody330_107 : HolLoopProg 64 :=
.mark loopBody330_106

def output330 : Nat × List Nat × HolLoopProg 64 :=
  (394, [0], loopBody330_107)
end InitECandidate.Proofs.FrontendStages.Loop
