import InitECandidate.Proofs.FrontendStages.Loop.Translate168
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody184_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody184_1 : HolLoopProg 64 :=
.mark loopBody184_0

def loopBody184_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody184_3 : HolLoopProg 64 :=
.mark loopBody184_2

def loopBody184_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody184_5 : HolLoopProg 64 :=
.mark loopBody184_4

def loopBody184_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody184_7 : HolLoopProg 64 :=
.mark loopBody184_6

def loopBody184_8 : HolLoopProg 64 :=
.call (some ([3, 4], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)) (some 94) ([5, 6]) (some (5, loopBody184_7, loopBody184_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody184_9 : HolLoopProg 64 :=
.mark loopBody184_8

def loopBody184_10 : HolLoopProg 64 :=
.seq loopBody184_9 loopBody184_1

def loopBody184_11 : HolLoopProg 64 :=
.mark loopBody184_10

def loopBody184_12 : HolLoopProg 64 :=
.seq loopBody184_5 loopBody184_11

def loopBody184_13 : HolLoopProg 64 :=
.mark loopBody184_12

def loopBody184_14 : HolLoopProg 64 :=
.seq loopBody184_3 loopBody184_13

def loopBody184_15 : HolLoopProg 64 :=
.mark loopBody184_14

def loopBody184_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody184_17 : HolLoopProg 64 :=
.mark loopBody184_16

def loopBody184_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody184_19 : HolLoopProg 64 :=
.mark loopBody184_18

def loopBody184_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody184_21 : HolLoopProg 64 :=
.mark loopBody184_20

def loopBody184_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody184_23 : HolLoopProg 64 :=
.mark loopBody184_22

def loopBody184_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.reg 7) loopBody184_21 loopBody184_23 (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody184_25 : HolLoopProg 64 :=
.mark loopBody184_24

def loopBody184_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 6)

def loopBody184_27 : HolLoopProg 64 :=
.mark loopBody184_26

def loopBody184_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 30#64)

def loopBody184_29 : HolLoopProg 64 :=
.mark loopBody184_28

def loopBody184_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody184_31 : HolLoopProg 64 :=
.mark loopBody184_30

def loopBody184_32 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 245) ([6]) (some (6, loopBody184_31, loopBody184_1, (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody184_33 : HolLoopProg 64 :=
.mark loopBody184_32

def loopBody184_34 : HolLoopProg 64 :=
.seq loopBody184_33 loopBody184_1

def loopBody184_35 : HolLoopProg 64 :=
.mark loopBody184_34

def loopBody184_36 : HolLoopProg 64 :=
.seq loopBody184_29 loopBody184_35

def loopBody184_37 : HolLoopProg 64 :=
.mark loopBody184_36

def loopBody184_38 : HolLoopProg 64 :=
.seq loopBody184_1 loopBody184_37

def loopBody184_39 : HolLoopProg 64 :=
.mark loopBody184_38

def loopBody184_40 : HolLoopProg 64 :=
.seq loopBody184_1 loopBody184_39

def loopBody184_41 : HolLoopProg 64 :=
.mark loopBody184_40

def loopBody184_42 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody184_41 loopBody184_1 (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody184_43 : HolLoopProg 64 :=
.mark loopBody184_42

def loopBody184_44 : HolLoopProg 64 :=
.seq loopBody184_43 loopBody184_1

def loopBody184_45 : HolLoopProg 64 :=
.mark loopBody184_44

def loopBody184_46 : HolLoopProg 64 :=
.seq loopBody184_27 loopBody184_45

def loopBody184_47 : HolLoopProg 64 :=
.mark loopBody184_46

def loopBody184_48 : HolLoopProg 64 :=
.seq loopBody184_25 loopBody184_47

def loopBody184_49 : HolLoopProg 64 :=
.mark loopBody184_48

def loopBody184_50 : HolLoopProg 64 :=
.seq loopBody184_19 loopBody184_49

def loopBody184_51 : HolLoopProg 64 :=
.mark loopBody184_50

def loopBody184_52 : HolLoopProg 64 :=
.seq loopBody184_17 loopBody184_51

def loopBody184_53 : HolLoopProg 64 :=
.mark loopBody184_52

def loopBody184_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 2)

def loopBody184_55 : HolLoopProg 64 :=
.mark loopBody184_54

def loopBody184_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody184_57 : HolLoopProg 64 :=
.mark loopBody184_56

def loopBody184_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.RegImm.reg 7) loopBody184_21 loopBody184_23 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody184_59 : HolLoopProg 64 :=
.mark loopBody184_58

def loopBody184_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 31#64)

def loopBody184_61 : HolLoopProg 64 :=
.mark loopBody184_60

def loopBody184_62 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 245) ([6]) (some (6, loopBody184_31, loopBody184_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))

def loopBody184_63 : HolLoopProg 64 :=
.mark loopBody184_62

def loopBody184_64 : HolLoopProg 64 :=
.seq loopBody184_63 loopBody184_1

def loopBody184_65 : HolLoopProg 64 :=
.mark loopBody184_64

def loopBody184_66 : HolLoopProg 64 :=
.seq loopBody184_61 loopBody184_65

def loopBody184_67 : HolLoopProg 64 :=
.mark loopBody184_66

def loopBody184_68 : HolLoopProg 64 :=
.seq loopBody184_1 loopBody184_67

def loopBody184_69 : HolLoopProg 64 :=
.mark loopBody184_68

def loopBody184_70 : HolLoopProg 64 :=
.seq loopBody184_1 loopBody184_69

def loopBody184_71 : HolLoopProg 64 :=
.mark loopBody184_70

def loopBody184_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.RegImm.imm 0#64) loopBody184_71 loopBody184_1 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))

def loopBody184_73 : HolLoopProg 64 :=
.mark loopBody184_72

def loopBody184_74 : HolLoopProg 64 :=
.seq loopBody184_73 loopBody184_1

def loopBody184_75 : HolLoopProg 64 :=
.mark loopBody184_74

def loopBody184_76 : HolLoopProg 64 :=
.seq loopBody184_27 loopBody184_75

def loopBody184_77 : HolLoopProg 64 :=
.mark loopBody184_76

def loopBody184_78 : HolLoopProg 64 :=
.seq loopBody184_59 loopBody184_77

def loopBody184_79 : HolLoopProg 64 :=
.mark loopBody184_78

def loopBody184_80 : HolLoopProg 64 :=
.seq loopBody184_57 loopBody184_79

def loopBody184_81 : HolLoopProg 64 :=
.mark loopBody184_80

def loopBody184_82 : HolLoopProg 64 :=
.seq loopBody184_55 loopBody184_81

def loopBody184_83 : HolLoopProg 64 :=
.mark loopBody184_82

def loopBody184_84 : HolLoopProg 64 :=
.seq loopBody184_53 loopBody184_83

def loopBody184_85 : HolLoopProg 64 :=
.mark loopBody184_84

def loopBody184_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody184_87 : HolLoopProg 64 :=
.mark loopBody184_86

def loopBody184_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody184_89 : HolLoopProg 64 :=
.mark loopBody184_88

def loopBody184_90 : HolLoopProg 64 :=
.seq loopBody184_89 loopBody184_1

def loopBody184_91 : HolLoopProg 64 :=
.mark loopBody184_90

def loopBody184_92 : HolLoopProg 64 :=
.seq loopBody184_87 loopBody184_91

def loopBody184_93 : HolLoopProg 64 :=
.mark loopBody184_92

def loopBody184_94 : HolLoopProg 64 :=
.seq loopBody184_85 loopBody184_93

def loopBody184_95 : HolLoopProg 64 :=
.mark loopBody184_94

def loopBody184_96 : HolLoopProg 64 :=
.seq loopBody184_15 loopBody184_95

def loopBody184_97 : HolLoopProg 64 :=
.mark loopBody184_96

def loopBody184_98 : HolLoopProg 64 :=
.seq loopBody184_1 loopBody184_97

def loopBody184_99 : HolLoopProg 64 :=
.mark loopBody184_98

def loopBody184_100 : HolLoopProg 64 :=
.seq loopBody184_1 loopBody184_99

def loopBody184_101 : HolLoopProg 64 :=
.mark loopBody184_100

def loopBody184_102 : HolLoopProg 64 :=
.seq loopBody184_1 loopBody184_101

def loopBody184_103 : HolLoopProg 64 :=
.mark loopBody184_102

def loopBody184_104 : HolLoopProg 64 :=
.seq loopBody184_1 loopBody184_103

def loopBody184_105 : HolLoopProg 64 :=
.mark loopBody184_104

def output184 : Nat × List Nat × HolLoopProg 64 :=
  (248, [0, 1, 2], loopBody184_105)
end InitECandidate.Proofs.FrontendStages.Loop
