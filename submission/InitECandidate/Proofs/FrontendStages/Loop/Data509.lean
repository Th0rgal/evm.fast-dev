import InitECandidate.Proofs.FrontendStages.Loop.Translate493
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody509_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody509_1 : HolLoopProg 64 :=
.mark loopBody509_0

def loopBody509_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody509_3 : HolLoopProg 64 :=
.mark loopBody509_2

def loopBody509_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody509_5 : HolLoopProg 64 :=
.mark loopBody509_4

def loopBody509_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody509_5, loopBody509_1, (Flapjack.Spt.ln)))

def loopBody509_7 : HolLoopProg 64 :=
.mark loopBody509_6

def loopBody509_8 : HolLoopProg 64 :=
.seq loopBody509_7 loopBody509_1

def loopBody509_9 : HolLoopProg 64 :=
.mark loopBody509_8

def loopBody509_10 : HolLoopProg 64 :=
.seq loopBody509_3 loopBody509_9

def loopBody509_11 : HolLoopProg 64 :=
.mark loopBody509_10

def loopBody509_12 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_11

def loopBody509_13 : HolLoopProg 64 :=
.mark loopBody509_12

def loopBody509_14 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_13

def loopBody509_15 : HolLoopProg 64 :=
.mark loopBody509_14

def loopBody509_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 568) ([]) (some (2, loopBody509_5, loopBody509_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody509_17 : HolLoopProg 64 :=
.mark loopBody509_16

def loopBody509_18 : HolLoopProg 64 :=
.seq loopBody509_17 loopBody509_1

def loopBody509_19 : HolLoopProg 64 :=
.mark loopBody509_18

def loopBody509_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 32#64]))

def loopBody509_21 : HolLoopProg 64 :=
.mark loopBody509_20

def loopBody509_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody509_23 : HolLoopProg 64 :=
.mark loopBody509_22

def loopBody509_24 : HolLoopProg 64 :=
.call (some ([2, 3, 4, 5], Flapjack.Spt.ln)) (some 463) ([6]) (some (6, loopBody509_23, loopBody509_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody509_25 : HolLoopProg 64 :=
.mark loopBody509_24

def loopBody509_26 : HolLoopProg 64 :=
.seq loopBody509_25 loopBody509_1

def loopBody509_27 : HolLoopProg 64 :=
.mark loopBody509_26

def loopBody509_28 : HolLoopProg 64 :=
.seq loopBody509_21 loopBody509_27

def loopBody509_29 : HolLoopProg 64 :=
.mark loopBody509_28

def loopBody509_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody509_31 : HolLoopProg 64 :=
.mark loopBody509_30

def loopBody509_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody509_33 : HolLoopProg 64 :=
.mark loopBody509_32

def loopBody509_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody509_35 : HolLoopProg 64 :=
.mark loopBody509_34

def loopBody509_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody509_37 : HolLoopProg 64 :=
.mark loopBody509_36

def loopBody509_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody509_39 : HolLoopProg 64 :=
.mark loopBody509_38

def loopBody509_40 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 472) ([7, 8, 9, 10]) (some (7, loopBody509_39, loopBody509_1, (Flapjack.Spt.ln)))

def loopBody509_41 : HolLoopProg 64 :=
.mark loopBody509_40

def loopBody509_42 : HolLoopProg 64 :=
.seq loopBody509_41 loopBody509_1

def loopBody509_43 : HolLoopProg 64 :=
.mark loopBody509_42

def loopBody509_44 : HolLoopProg 64 :=
.seq loopBody509_37 loopBody509_43

def loopBody509_45 : HolLoopProg 64 :=
.mark loopBody509_44

def loopBody509_46 : HolLoopProg 64 :=
.seq loopBody509_35 loopBody509_45

def loopBody509_47 : HolLoopProg 64 :=
.mark loopBody509_46

def loopBody509_48 : HolLoopProg 64 :=
.seq loopBody509_33 loopBody509_47

def loopBody509_49 : HolLoopProg 64 :=
.mark loopBody509_48

def loopBody509_50 : HolLoopProg 64 :=
.seq loopBody509_31 loopBody509_49

def loopBody509_51 : HolLoopProg 64 :=
.mark loopBody509_50

def loopBody509_52 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_51

def loopBody509_53 : HolLoopProg 64 :=
.mark loopBody509_52

def loopBody509_54 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_53

def loopBody509_55 : HolLoopProg 64 :=
.mark loopBody509_54

def loopBody509_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody509_57 : HolLoopProg 64 :=
.mark loopBody509_56

def loopBody509_58 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 486) ([7]) (some (7, loopBody509_39, loopBody509_1, (Flapjack.Spt.ln)))

def loopBody509_59 : HolLoopProg 64 :=
.mark loopBody509_58

def loopBody509_60 : HolLoopProg 64 :=
.seq loopBody509_59 loopBody509_1

def loopBody509_61 : HolLoopProg 64 :=
.mark loopBody509_60

def loopBody509_62 : HolLoopProg 64 :=
.seq loopBody509_57 loopBody509_61

def loopBody509_63 : HolLoopProg 64 :=
.mark loopBody509_62

def loopBody509_64 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_63

def loopBody509_65 : HolLoopProg 64 :=
.mark loopBody509_64

def loopBody509_66 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_65

def loopBody509_67 : HolLoopProg 64 :=
.mark loopBody509_66

def loopBody509_68 : HolLoopProg 64 :=
.seq loopBody509_55 loopBody509_67

def loopBody509_69 : HolLoopProg 64 :=
.mark loopBody509_68

def loopBody509_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody509_71 : HolLoopProg 64 :=
.mark loopBody509_70

def loopBody509_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody509_73 : HolLoopProg 64 :=
.mark loopBody509_72

def loopBody509_74 : HolLoopProg 64 :=
.seq loopBody509_73 loopBody509_1

def loopBody509_75 : HolLoopProg 64 :=
.mark loopBody509_74

def loopBody509_76 : HolLoopProg 64 :=
.seq loopBody509_71 loopBody509_75

def loopBody509_77 : HolLoopProg 64 :=
.mark loopBody509_76

def loopBody509_78 : HolLoopProg 64 :=
.seq loopBody509_69 loopBody509_77

def loopBody509_79 : HolLoopProg 64 :=
.mark loopBody509_78

def loopBody509_80 : HolLoopProg 64 :=
.seq loopBody509_29 loopBody509_79

def loopBody509_81 : HolLoopProg 64 :=
.mark loopBody509_80

def loopBody509_82 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_81

def loopBody509_83 : HolLoopProg 64 :=
.mark loopBody509_82

def loopBody509_84 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_83

def loopBody509_85 : HolLoopProg 64 :=
.mark loopBody509_84

def loopBody509_86 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_85

def loopBody509_87 : HolLoopProg 64 :=
.mark loopBody509_86

def loopBody509_88 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_87

def loopBody509_89 : HolLoopProg 64 :=
.mark loopBody509_88

def loopBody509_90 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_89

def loopBody509_91 : HolLoopProg 64 :=
.mark loopBody509_90

def loopBody509_92 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_91

def loopBody509_93 : HolLoopProg 64 :=
.mark loopBody509_92

def loopBody509_94 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_93

def loopBody509_95 : HolLoopProg 64 :=
.mark loopBody509_94

def loopBody509_96 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_95

def loopBody509_97 : HolLoopProg 64 :=
.mark loopBody509_96

def loopBody509_98 : HolLoopProg 64 :=
.seq loopBody509_19 loopBody509_97

def loopBody509_99 : HolLoopProg 64 :=
.mark loopBody509_98

def loopBody509_100 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_99

def loopBody509_101 : HolLoopProg 64 :=
.mark loopBody509_100

def loopBody509_102 : HolLoopProg 64 :=
.seq loopBody509_1 loopBody509_101

def loopBody509_103 : HolLoopProg 64 :=
.mark loopBody509_102

def loopBody509_104 : HolLoopProg 64 :=
.seq loopBody509_15 loopBody509_103

def loopBody509_105 : HolLoopProg 64 :=
.mark loopBody509_104

def output509 : Nat × List Nat × HolLoopProg 64 :=
  (573, [], loopBody509_105)
end InitECandidate.Proofs.FrontendStages.Loop
