import InitECandidate.Proofs.FrontendStages.Loop.Translate498
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody514_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody514_1 : HolLoopProg 64 :=
.mark loopBody514_0

def loopBody514_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody514_3 : HolLoopProg 64 :=
.mark loopBody514_2

def loopBody514_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody514_5 : HolLoopProg 64 :=
.mark loopBody514_4

def loopBody514_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody514_5, loopBody514_1, (Flapjack.Spt.ln)))

def loopBody514_7 : HolLoopProg 64 :=
.mark loopBody514_6

def loopBody514_8 : HolLoopProg 64 :=
.seq loopBody514_7 loopBody514_1

def loopBody514_9 : HolLoopProg 64 :=
.mark loopBody514_8

def loopBody514_10 : HolLoopProg 64 :=
.seq loopBody514_3 loopBody514_9

def loopBody514_11 : HolLoopProg 64 :=
.mark loopBody514_10

def loopBody514_12 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_11

def loopBody514_13 : HolLoopProg 64 :=
.mark loopBody514_12

def loopBody514_14 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_13

def loopBody514_15 : HolLoopProg 64 :=
.mark loopBody514_14

def loopBody514_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 568) ([]) (some (2, loopBody514_5, loopBody514_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody514_17 : HolLoopProg 64 :=
.mark loopBody514_16

def loopBody514_18 : HolLoopProg 64 :=
.seq loopBody514_17 loopBody514_1

def loopBody514_19 : HolLoopProg 64 :=
.mark loopBody514_18

def loopBody514_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 88#64]))

def loopBody514_21 : HolLoopProg 64 :=
.mark loopBody514_20

def loopBody514_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 32#64)

def loopBody514_23 : HolLoopProg 64 :=
.mark loopBody514_22

def loopBody514_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody514_25 : HolLoopProg 64 :=
.mark loopBody514_24

def loopBody514_26 : HolLoopProg 64 :=
.call (some ([2, 3, 4, 5], Flapjack.Spt.ln)) (some 146) ([6, 7]) (some (6, loopBody514_25, loopBody514_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody514_27 : HolLoopProg 64 :=
.mark loopBody514_26

def loopBody514_28 : HolLoopProg 64 :=
.seq loopBody514_27 loopBody514_1

def loopBody514_29 : HolLoopProg 64 :=
.mark loopBody514_28

def loopBody514_30 : HolLoopProg 64 :=
.seq loopBody514_23 loopBody514_29

def loopBody514_31 : HolLoopProg 64 :=
.mark loopBody514_30

def loopBody514_32 : HolLoopProg 64 :=
.seq loopBody514_21 loopBody514_31

def loopBody514_33 : HolLoopProg 64 :=
.mark loopBody514_32

def loopBody514_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody514_35 : HolLoopProg 64 :=
.mark loopBody514_34

def loopBody514_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody514_37 : HolLoopProg 64 :=
.mark loopBody514_36

def loopBody514_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody514_39 : HolLoopProg 64 :=
.mark loopBody514_38

def loopBody514_40 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody514_41 : HolLoopProg 64 :=
.mark loopBody514_40

def loopBody514_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody514_43 : HolLoopProg 64 :=
.mark loopBody514_42

def loopBody514_44 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 472) ([7, 8, 9, 10]) (some (7, loopBody514_43, loopBody514_1, (Flapjack.Spt.ln)))

def loopBody514_45 : HolLoopProg 64 :=
.mark loopBody514_44

def loopBody514_46 : HolLoopProg 64 :=
.seq loopBody514_45 loopBody514_1

def loopBody514_47 : HolLoopProg 64 :=
.mark loopBody514_46

def loopBody514_48 : HolLoopProg 64 :=
.seq loopBody514_41 loopBody514_47

def loopBody514_49 : HolLoopProg 64 :=
.mark loopBody514_48

def loopBody514_50 : HolLoopProg 64 :=
.seq loopBody514_39 loopBody514_49

def loopBody514_51 : HolLoopProg 64 :=
.mark loopBody514_50

def loopBody514_52 : HolLoopProg 64 :=
.seq loopBody514_37 loopBody514_51

def loopBody514_53 : HolLoopProg 64 :=
.mark loopBody514_52

def loopBody514_54 : HolLoopProg 64 :=
.seq loopBody514_35 loopBody514_53

def loopBody514_55 : HolLoopProg 64 :=
.mark loopBody514_54

def loopBody514_56 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_55

def loopBody514_57 : HolLoopProg 64 :=
.mark loopBody514_56

def loopBody514_58 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_57

def loopBody514_59 : HolLoopProg 64 :=
.mark loopBody514_58

def loopBody514_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody514_61 : HolLoopProg 64 :=
.mark loopBody514_60

def loopBody514_62 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 486) ([7]) (some (7, loopBody514_43, loopBody514_1, (Flapjack.Spt.ln)))

def loopBody514_63 : HolLoopProg 64 :=
.mark loopBody514_62

def loopBody514_64 : HolLoopProg 64 :=
.seq loopBody514_63 loopBody514_1

def loopBody514_65 : HolLoopProg 64 :=
.mark loopBody514_64

def loopBody514_66 : HolLoopProg 64 :=
.seq loopBody514_61 loopBody514_65

def loopBody514_67 : HolLoopProg 64 :=
.mark loopBody514_66

def loopBody514_68 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_67

def loopBody514_69 : HolLoopProg 64 :=
.mark loopBody514_68

def loopBody514_70 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_69

def loopBody514_71 : HolLoopProg 64 :=
.mark loopBody514_70

def loopBody514_72 : HolLoopProg 64 :=
.seq loopBody514_59 loopBody514_71

def loopBody514_73 : HolLoopProg 64 :=
.mark loopBody514_72

def loopBody514_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody514_75 : HolLoopProg 64 :=
.mark loopBody514_74

def loopBody514_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody514_77 : HolLoopProg 64 :=
.mark loopBody514_76

def loopBody514_78 : HolLoopProg 64 :=
.seq loopBody514_77 loopBody514_1

def loopBody514_79 : HolLoopProg 64 :=
.mark loopBody514_78

def loopBody514_80 : HolLoopProg 64 :=
.seq loopBody514_75 loopBody514_79

def loopBody514_81 : HolLoopProg 64 :=
.mark loopBody514_80

def loopBody514_82 : HolLoopProg 64 :=
.seq loopBody514_73 loopBody514_81

def loopBody514_83 : HolLoopProg 64 :=
.mark loopBody514_82

def loopBody514_84 : HolLoopProg 64 :=
.seq loopBody514_33 loopBody514_83

def loopBody514_85 : HolLoopProg 64 :=
.mark loopBody514_84

def loopBody514_86 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_85

def loopBody514_87 : HolLoopProg 64 :=
.mark loopBody514_86

def loopBody514_88 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_87

def loopBody514_89 : HolLoopProg 64 :=
.mark loopBody514_88

def loopBody514_90 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_89

def loopBody514_91 : HolLoopProg 64 :=
.mark loopBody514_90

def loopBody514_92 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_91

def loopBody514_93 : HolLoopProg 64 :=
.mark loopBody514_92

def loopBody514_94 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_93

def loopBody514_95 : HolLoopProg 64 :=
.mark loopBody514_94

def loopBody514_96 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_95

def loopBody514_97 : HolLoopProg 64 :=
.mark loopBody514_96

def loopBody514_98 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_97

def loopBody514_99 : HolLoopProg 64 :=
.mark loopBody514_98

def loopBody514_100 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_99

def loopBody514_101 : HolLoopProg 64 :=
.mark loopBody514_100

def loopBody514_102 : HolLoopProg 64 :=
.seq loopBody514_19 loopBody514_101

def loopBody514_103 : HolLoopProg 64 :=
.mark loopBody514_102

def loopBody514_104 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_103

def loopBody514_105 : HolLoopProg 64 :=
.mark loopBody514_104

def loopBody514_106 : HolLoopProg 64 :=
.seq loopBody514_1 loopBody514_105

def loopBody514_107 : HolLoopProg 64 :=
.mark loopBody514_106

def loopBody514_108 : HolLoopProg 64 :=
.seq loopBody514_15 loopBody514_107

def loopBody514_109 : HolLoopProg 64 :=
.mark loopBody514_108

def output514 : Nat × List Nat × HolLoopProg 64 :=
  (578, [], loopBody514_109)
end InitECandidate.Proofs.FrontendStages.Loop
