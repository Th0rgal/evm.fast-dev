import InitECandidate.Proofs.FrontendStages.Loop.Translate235
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody251_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody251_1 : HolLoopProg 64 :=
.mark loopBody251_0

def loopBody251_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody251_3 : HolLoopProg 64 :=
.mark loopBody251_2

def loopBody251_4 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 75) ([]) (some (5, loopBody251_3, loopBody251_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody251_5 : HolLoopProg 64 :=
.mark loopBody251_4

def loopBody251_6 : HolLoopProg 64 :=
.seq loopBody251_5 loopBody251_1

def loopBody251_7 : HolLoopProg 64 :=
.mark loopBody251_6

def loopBody251_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody251_9 : HolLoopProg 64 :=
.mark loopBody251_8

def loopBody251_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody251_11 : HolLoopProg 64 :=
.mark loopBody251_10

def loopBody251_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 2)

def loopBody251_13 : HolLoopProg 64 :=
.mark loopBody251_12

def loopBody251_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody251_15 : HolLoopProg 64 :=
.mark loopBody251_14

def loopBody251_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody251_17 : HolLoopProg 64 :=
.mark loopBody251_16

def loopBody251_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.tick

def loopBody251_19 : HolLoopProg 64 :=
.mark loopBody251_18

def loopBody251_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.lookup 0#5)

def loopBody251_21 : HolLoopProg 64 :=
.mark loopBody251_20

def loopBody251_22 : HolLoopProg 64 :=
.seq loopBody251_21 loopBody251_1

def loopBody251_23 : HolLoopProg 64 :=
.mark loopBody251_22

def loopBody251_24 : HolLoopProg 64 :=
.seq loopBody251_23 loopBody251_1

def loopBody251_25 : HolLoopProg 64 :=
.mark loopBody251_24

def loopBody251_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody251_27 : HolLoopProg 64 :=
.mark loopBody251_26

def loopBody251_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody251_29 : HolLoopProg 64 :=
.mark loopBody251_28

def loopBody251_30 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))) (some 76) ([8]) (some (8, loopBody251_29, loopBody251_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))

def loopBody251_31 : HolLoopProg 64 :=
.mark loopBody251_30

def loopBody251_32 : HolLoopProg 64 :=
.seq loopBody251_31 loopBody251_1

def loopBody251_33 : HolLoopProg 64 :=
.mark loopBody251_32

def loopBody251_34 : HolLoopProg 64 :=
.seq loopBody251_27 loopBody251_33

def loopBody251_35 : HolLoopProg 64 :=
.mark loopBody251_34

def loopBody251_36 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_35

def loopBody251_37 : HolLoopProg 64 :=
.mark loopBody251_36

def loopBody251_38 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_37

def loopBody251_39 : HolLoopProg 64 :=
.mark loopBody251_38

def loopBody251_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody251_41 : HolLoopProg 64 :=
.mark loopBody251_40

def loopBody251_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.setGlobal (0#5) (Flapjack.HolLoopExp.var 7)

def loopBody251_43 : HolLoopProg 64 :=
.mark loopBody251_42

def loopBody251_44 : HolLoopProg 64 :=
.seq loopBody251_43 loopBody251_1

def loopBody251_45 : HolLoopProg 64 :=
.mark loopBody251_44

def loopBody251_46 : HolLoopProg 64 :=
.seq loopBody251_45 loopBody251_1

def loopBody251_47 : HolLoopProg 64 :=
.mark loopBody251_46

def loopBody251_48 : HolLoopProg 64 :=
.seq loopBody251_41 loopBody251_47

def loopBody251_49 : HolLoopProg 64 :=
.mark loopBody251_48

def loopBody251_50 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_49

def loopBody251_51 : HolLoopProg 64 :=
.mark loopBody251_50

def loopBody251_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 5#64)

def loopBody251_53 : HolLoopProg 64 :=
.mark loopBody251_52

def loopBody251_54 : HolLoopProg 64 :=
.seq loopBody251_53 loopBody251_17

def loopBody251_55 : HolLoopProg 64 :=
.mark loopBody251_54

def loopBody251_56 : HolLoopProg 64 :=
.seq loopBody251_51 loopBody251_55

def loopBody251_57 : HolLoopProg 64 :=
.mark loopBody251_56

def loopBody251_58 : HolLoopProg 64 :=
.seq loopBody251_39 loopBody251_57

def loopBody251_59 : HolLoopProg 64 :=
.mark loopBody251_58

def loopBody251_60 : HolLoopProg 64 :=
.seq loopBody251_25 loopBody251_59

def loopBody251_61 : HolLoopProg 64 :=
.mark loopBody251_60

def loopBody251_62 : HolLoopProg 64 :=
.seq loopBody251_19 loopBody251_61

def loopBody251_63 : HolLoopProg 64 :=
.mark loopBody251_62

def loopBody251_64 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 5#64) loopBody251_17 loopBody251_63 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)

def loopBody251_65 : HolLoopProg 64 :=
.mark loopBody251_64

def loopBody251_66 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 314) ([7, 8, 9, 10]) (some (7, loopBody251_65, loopBody251_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody251_67 : HolLoopProg 64 :=
.mark loopBody251_66

def loopBody251_68 : HolLoopProg 64 :=
.seq loopBody251_67 loopBody251_1

def loopBody251_69 : HolLoopProg 64 :=
.mark loopBody251_68

def loopBody251_70 : HolLoopProg 64 :=
.seq loopBody251_15 loopBody251_69

def loopBody251_71 : HolLoopProg 64 :=
.mark loopBody251_70

def loopBody251_72 : HolLoopProg 64 :=
.seq loopBody251_13 loopBody251_71

def loopBody251_73 : HolLoopProg 64 :=
.mark loopBody251_72

def loopBody251_74 : HolLoopProg 64 :=
.seq loopBody251_11 loopBody251_73

def loopBody251_75 : HolLoopProg 64 :=
.mark loopBody251_74

def loopBody251_76 : HolLoopProg 64 :=
.seq loopBody251_9 loopBody251_75

def loopBody251_77 : HolLoopProg 64 :=
.mark loopBody251_76

def loopBody251_78 : HolLoopProg 64 :=
.call (some ([7], Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)) (some 76) ([8]) (some (8, loopBody251_29, loopBody251_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))

def loopBody251_79 : HolLoopProg 64 :=
.mark loopBody251_78

def loopBody251_80 : HolLoopProg 64 :=
.seq loopBody251_79 loopBody251_1

def loopBody251_81 : HolLoopProg 64 :=
.mark loopBody251_80

def loopBody251_82 : HolLoopProg 64 :=
.seq loopBody251_27 loopBody251_81

def loopBody251_83 : HolLoopProg 64 :=
.mark loopBody251_82

def loopBody251_84 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_83

def loopBody251_85 : HolLoopProg 64 :=
.mark loopBody251_84

def loopBody251_86 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_85

def loopBody251_87 : HolLoopProg 64 :=
.mark loopBody251_86

def loopBody251_88 : HolLoopProg 64 :=
.seq loopBody251_77 loopBody251_87

def loopBody251_89 : HolLoopProg 64 :=
.mark loopBody251_88

def loopBody251_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody251_91 : HolLoopProg 64 :=
.mark loopBody251_90

def loopBody251_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody251_93 : HolLoopProg 64 :=
.mark loopBody251_92

def loopBody251_94 : HolLoopProg 64 :=
.seq loopBody251_93 loopBody251_1

def loopBody251_95 : HolLoopProg 64 :=
.mark loopBody251_94

def loopBody251_96 : HolLoopProg 64 :=
.seq loopBody251_91 loopBody251_95

def loopBody251_97 : HolLoopProg 64 :=
.mark loopBody251_96

def loopBody251_98 : HolLoopProg 64 :=
.seq loopBody251_89 loopBody251_97

def loopBody251_99 : HolLoopProg 64 :=
.mark loopBody251_98

def loopBody251_100 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_99

def loopBody251_101 : HolLoopProg 64 :=
.mark loopBody251_100

def loopBody251_102 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_101

def loopBody251_103 : HolLoopProg 64 :=
.mark loopBody251_102

def loopBody251_104 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_103

def loopBody251_105 : HolLoopProg 64 :=
.mark loopBody251_104

def loopBody251_106 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_105

def loopBody251_107 : HolLoopProg 64 :=
.mark loopBody251_106

def loopBody251_108 : HolLoopProg 64 :=
.seq loopBody251_7 loopBody251_107

def loopBody251_109 : HolLoopProg 64 :=
.mark loopBody251_108

def loopBody251_110 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_109

def loopBody251_111 : HolLoopProg 64 :=
.mark loopBody251_110

def loopBody251_112 : HolLoopProg 64 :=
.seq loopBody251_1 loopBody251_111

def loopBody251_113 : HolLoopProg 64 :=
.mark loopBody251_112

def output251 : Nat × List Nat × HolLoopProg 64 :=
  (315, [0, 1, 2, 3], loopBody251_113)
end InitECandidate.Proofs.FrontendStages.Loop
