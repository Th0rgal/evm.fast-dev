import InitECandidate.Proofs.FrontendStages.Loop.Translate220
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody236_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody236_1 : HolLoopProg 64 :=
.mark loopBody236_0

def loopBody236_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody236_3 : HolLoopProg 64 :=
.mark loopBody236_2

def loopBody236_4 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 75) ([]) (some (4, loopBody236_3, loopBody236_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody236_5 : HolLoopProg 64 :=
.mark loopBody236_4

def loopBody236_6 : HolLoopProg 64 :=
.seq loopBody236_5 loopBody236_1

def loopBody236_7 : HolLoopProg 64 :=
.mark loopBody236_6

def loopBody236_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody236_9 : HolLoopProg 64 :=
.mark loopBody236_8

def loopBody236_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 1)

def loopBody236_11 : HolLoopProg 64 :=
.mark loopBody236_10

def loopBody236_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody236_13 : HolLoopProg 64 :=
.mark loopBody236_12

def loopBody236_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 3)

def loopBody236_15 : HolLoopProg 64 :=
.mark loopBody236_14

def loopBody236_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody236_17 : HolLoopProg 64 :=
.mark loopBody236_16

def loopBody236_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody236_19 : HolLoopProg 64 :=
.mark loopBody236_18

def loopBody236_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody236_21 : HolLoopProg 64 :=
.mark loopBody236_20

def loopBody236_22 : HolLoopProg 64 :=
.seq loopBody236_21 loopBody236_1

def loopBody236_23 : HolLoopProg 64 :=
.mark loopBody236_22

def loopBody236_24 : HolLoopProg 64 :=
.seq loopBody236_23 loopBody236_1

def loopBody236_25 : HolLoopProg 64 :=
.mark loopBody236_24

def loopBody236_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody236_27 : HolLoopProg 64 :=
.mark loopBody236_26

def loopBody236_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody236_29 : HolLoopProg 64 :=
.mark loopBody236_28

def loopBody236_30 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 76) ([7]) (some (7, loopBody236_29, loopBody236_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody236_31 : HolLoopProg 64 :=
.mark loopBody236_30

def loopBody236_32 : HolLoopProg 64 :=
.seq loopBody236_31 loopBody236_1

def loopBody236_33 : HolLoopProg 64 :=
.mark loopBody236_32

def loopBody236_34 : HolLoopProg 64 :=
.seq loopBody236_27 loopBody236_33

def loopBody236_35 : HolLoopProg 64 :=
.mark loopBody236_34

def loopBody236_36 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_35

def loopBody236_37 : HolLoopProg 64 :=
.mark loopBody236_36

def loopBody236_38 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_37

def loopBody236_39 : HolLoopProg 64 :=
.mark loopBody236_38

def loopBody236_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 4)

def loopBody236_41 : HolLoopProg 64 :=
.mark loopBody236_40

def loopBody236_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 6)

def loopBody236_43 : HolLoopProg 64 :=
.mark loopBody236_42

def loopBody236_44 : HolLoopProg 64 :=
.seq loopBody236_43 loopBody236_1

def loopBody236_45 : HolLoopProg 64 :=
.mark loopBody236_44

def loopBody236_46 : HolLoopProg 64 :=
.seq loopBody236_45 loopBody236_1

def loopBody236_47 : HolLoopProg 64 :=
.mark loopBody236_46

def loopBody236_48 : HolLoopProg 64 :=
.seq loopBody236_41 loopBody236_47

def loopBody236_49 : HolLoopProg 64 :=
.mark loopBody236_48

def loopBody236_50 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_49

def loopBody236_51 : HolLoopProg 64 :=
.mark loopBody236_50

def loopBody236_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 1#64)

def loopBody236_53 : HolLoopProg 64 :=
.mark loopBody236_52

def loopBody236_54 : HolLoopProg 64 :=
.seq loopBody236_53 loopBody236_17

def loopBody236_55 : HolLoopProg 64 :=
.mark loopBody236_54

def loopBody236_56 : HolLoopProg 64 :=
.seq loopBody236_51 loopBody236_55

def loopBody236_57 : HolLoopProg 64 :=
.mark loopBody236_56

def loopBody236_58 : HolLoopProg 64 :=
.seq loopBody236_39 loopBody236_57

def loopBody236_59 : HolLoopProg 64 :=
.mark loopBody236_58

def loopBody236_60 : HolLoopProg 64 :=
.seq loopBody236_25 loopBody236_59

def loopBody236_61 : HolLoopProg 64 :=
.mark loopBody236_60

def loopBody236_62 : HolLoopProg 64 :=
.seq loopBody236_19 loopBody236_61

def loopBody236_63 : HolLoopProg 64 :=
.mark loopBody236_62

def loopBody236_64 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.RegImm.imm 1#64) loopBody236_17 loopBody236_63 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))

def loopBody236_65 : HolLoopProg 64 :=
.mark loopBody236_64

def loopBody236_66 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))) (some 299) ([6, 7, 8, 9]) (some (6, loopBody236_65, loopBody236_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody236_67 : HolLoopProg 64 :=
.mark loopBody236_66

def loopBody236_68 : HolLoopProg 64 :=
.seq loopBody236_67 loopBody236_1

def loopBody236_69 : HolLoopProg 64 :=
.mark loopBody236_68

def loopBody236_70 : HolLoopProg 64 :=
.seq loopBody236_15 loopBody236_69

def loopBody236_71 : HolLoopProg 64 :=
.mark loopBody236_70

def loopBody236_72 : HolLoopProg 64 :=
.seq loopBody236_13 loopBody236_71

def loopBody236_73 : HolLoopProg 64 :=
.mark loopBody236_72

def loopBody236_74 : HolLoopProg 64 :=
.seq loopBody236_11 loopBody236_73

def loopBody236_75 : HolLoopProg 64 :=
.mark loopBody236_74

def loopBody236_76 : HolLoopProg 64 :=
.seq loopBody236_9 loopBody236_75

def loopBody236_77 : HolLoopProg 64 :=
.mark loopBody236_76

def loopBody236_78 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 76) ([7]) (some (7, loopBody236_29, loopBody236_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody236_79 : HolLoopProg 64 :=
.mark loopBody236_78

def loopBody236_80 : HolLoopProg 64 :=
.seq loopBody236_79 loopBody236_1

def loopBody236_81 : HolLoopProg 64 :=
.mark loopBody236_80

def loopBody236_82 : HolLoopProg 64 :=
.seq loopBody236_27 loopBody236_81

def loopBody236_83 : HolLoopProg 64 :=
.mark loopBody236_82

def loopBody236_84 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_83

def loopBody236_85 : HolLoopProg 64 :=
.mark loopBody236_84

def loopBody236_86 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_85

def loopBody236_87 : HolLoopProg 64 :=
.mark loopBody236_86

def loopBody236_88 : HolLoopProg 64 :=
.seq loopBody236_77 loopBody236_87

def loopBody236_89 : HolLoopProg 64 :=
.mark loopBody236_88

def loopBody236_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 5)

def loopBody236_91 : HolLoopProg 64 :=
.mark loopBody236_90

def loopBody236_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody236_93 : HolLoopProg 64 :=
.mark loopBody236_92

def loopBody236_94 : HolLoopProg 64 :=
.seq loopBody236_93 loopBody236_1

def loopBody236_95 : HolLoopProg 64 :=
.mark loopBody236_94

def loopBody236_96 : HolLoopProg 64 :=
.seq loopBody236_91 loopBody236_95

def loopBody236_97 : HolLoopProg 64 :=
.mark loopBody236_96

def loopBody236_98 : HolLoopProg 64 :=
.seq loopBody236_89 loopBody236_97

def loopBody236_99 : HolLoopProg 64 :=
.mark loopBody236_98

def loopBody236_100 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_99

def loopBody236_101 : HolLoopProg 64 :=
.mark loopBody236_100

def loopBody236_102 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_101

def loopBody236_103 : HolLoopProg 64 :=
.mark loopBody236_102

def loopBody236_104 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_103

def loopBody236_105 : HolLoopProg 64 :=
.mark loopBody236_104

def loopBody236_106 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_105

def loopBody236_107 : HolLoopProg 64 :=
.mark loopBody236_106

def loopBody236_108 : HolLoopProg 64 :=
.seq loopBody236_7 loopBody236_107

def loopBody236_109 : HolLoopProg 64 :=
.mark loopBody236_108

def loopBody236_110 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_109

def loopBody236_111 : HolLoopProg 64 :=
.mark loopBody236_110

def loopBody236_112 : HolLoopProg 64 :=
.seq loopBody236_1 loopBody236_111

def loopBody236_113 : HolLoopProg 64 :=
.mark loopBody236_112

def output236 : Nat × List Nat × HolLoopProg 64 :=
  (300, [0, 1, 2], loopBody236_113)
end InitECandidate.Proofs.FrontendStages.Loop
