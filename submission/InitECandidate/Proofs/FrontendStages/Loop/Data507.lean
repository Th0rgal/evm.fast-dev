import InitECandidate.Proofs.FrontendStages.Loop.Translate491
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody507_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody507_1 : HolLoopProg 64 :=
.mark loopBody507_0

def loopBody507_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2 (Flapjack.HolLoopExp.const 2#64)

def loopBody507_3 : HolLoopProg 64 :=
.mark loopBody507_2

def loopBody507_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody507_5 : HolLoopProg 64 :=
.mark loopBody507_4

def loopBody507_6 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 466) ([2]) (some (2, loopBody507_5, loopBody507_1, (Flapjack.Spt.ln)))

def loopBody507_7 : HolLoopProg 64 :=
.mark loopBody507_6

def loopBody507_8 : HolLoopProg 64 :=
.seq loopBody507_7 loopBody507_1

def loopBody507_9 : HolLoopProg 64 :=
.mark loopBody507_8

def loopBody507_10 : HolLoopProg 64 :=
.seq loopBody507_3 loopBody507_9

def loopBody507_11 : HolLoopProg 64 :=
.mark loopBody507_10

def loopBody507_12 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_11

def loopBody507_13 : HolLoopProg 64 :=
.mark loopBody507_12

def loopBody507_14 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_13

def loopBody507_15 : HolLoopProg 64 :=
.mark loopBody507_14

def loopBody507_16 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ln)) (some 568) ([]) (some (2, loopBody507_5, loopBody507_1, (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))

def loopBody507_17 : HolLoopProg 64 :=
.mark loopBody507_16

def loopBody507_18 : HolLoopProg 64 :=
.seq loopBody507_17 loopBody507_1

def loopBody507_19 : HolLoopProg 64 :=
.mark loopBody507_18

def loopBody507_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 96#64]))

def loopBody507_21 : HolLoopProg 64 :=
.mark loopBody507_20

def loopBody507_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody507_23 : HolLoopProg 64 :=
.mark loopBody507_22

def loopBody507_24 : HolLoopProg 64 :=
.call (some ([2, 3, 4, 5], Flapjack.Spt.ln)) (some 276) ([6]) (some (6, loopBody507_23, loopBody507_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody507_25 : HolLoopProg 64 :=
.mark loopBody507_24

def loopBody507_26 : HolLoopProg 64 :=
.seq loopBody507_25 loopBody507_1

def loopBody507_27 : HolLoopProg 64 :=
.mark loopBody507_26

def loopBody507_28 : HolLoopProg 64 :=
.seq loopBody507_21 loopBody507_27

def loopBody507_29 : HolLoopProg 64 :=
.mark loopBody507_28

def loopBody507_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody507_31 : HolLoopProg 64 :=
.mark loopBody507_30

def loopBody507_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 3)

def loopBody507_33 : HolLoopProg 64 :=
.mark loopBody507_32

def loopBody507_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 4)

def loopBody507_35 : HolLoopProg 64 :=
.mark loopBody507_34

def loopBody507_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody507_37 : HolLoopProg 64 :=
.mark loopBody507_36

def loopBody507_38 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody507_39 : HolLoopProg 64 :=
.mark loopBody507_38

def loopBody507_40 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 472) ([7, 8, 9, 10]) (some (7, loopBody507_39, loopBody507_1, (Flapjack.Spt.ln)))

def loopBody507_41 : HolLoopProg 64 :=
.mark loopBody507_40

def loopBody507_42 : HolLoopProg 64 :=
.seq loopBody507_41 loopBody507_1

def loopBody507_43 : HolLoopProg 64 :=
.mark loopBody507_42

def loopBody507_44 : HolLoopProg 64 :=
.seq loopBody507_37 loopBody507_43

def loopBody507_45 : HolLoopProg 64 :=
.mark loopBody507_44

def loopBody507_46 : HolLoopProg 64 :=
.seq loopBody507_35 loopBody507_45

def loopBody507_47 : HolLoopProg 64 :=
.mark loopBody507_46

def loopBody507_48 : HolLoopProg 64 :=
.seq loopBody507_33 loopBody507_47

def loopBody507_49 : HolLoopProg 64 :=
.mark loopBody507_48

def loopBody507_50 : HolLoopProg 64 :=
.seq loopBody507_31 loopBody507_49

def loopBody507_51 : HolLoopProg 64 :=
.mark loopBody507_50

def loopBody507_52 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_51

def loopBody507_53 : HolLoopProg 64 :=
.mark loopBody507_52

def loopBody507_54 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_53

def loopBody507_55 : HolLoopProg 64 :=
.mark loopBody507_54

def loopBody507_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody507_57 : HolLoopProg 64 :=
.mark loopBody507_56

def loopBody507_58 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 486) ([7]) (some (7, loopBody507_39, loopBody507_1, (Flapjack.Spt.ln)))

def loopBody507_59 : HolLoopProg 64 :=
.mark loopBody507_58

def loopBody507_60 : HolLoopProg 64 :=
.seq loopBody507_59 loopBody507_1

def loopBody507_61 : HolLoopProg 64 :=
.mark loopBody507_60

def loopBody507_62 : HolLoopProg 64 :=
.seq loopBody507_57 loopBody507_61

def loopBody507_63 : HolLoopProg 64 :=
.mark loopBody507_62

def loopBody507_64 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_63

def loopBody507_65 : HolLoopProg 64 :=
.mark loopBody507_64

def loopBody507_66 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_65

def loopBody507_67 : HolLoopProg 64 :=
.mark loopBody507_66

def loopBody507_68 : HolLoopProg 64 :=
.seq loopBody507_55 loopBody507_67

def loopBody507_69 : HolLoopProg 64 :=
.mark loopBody507_68

def loopBody507_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody507_71 : HolLoopProg 64 :=
.mark loopBody507_70

def loopBody507_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody507_73 : HolLoopProg 64 :=
.mark loopBody507_72

def loopBody507_74 : HolLoopProg 64 :=
.seq loopBody507_73 loopBody507_1

def loopBody507_75 : HolLoopProg 64 :=
.mark loopBody507_74

def loopBody507_76 : HolLoopProg 64 :=
.seq loopBody507_71 loopBody507_75

def loopBody507_77 : HolLoopProg 64 :=
.mark loopBody507_76

def loopBody507_78 : HolLoopProg 64 :=
.seq loopBody507_69 loopBody507_77

def loopBody507_79 : HolLoopProg 64 :=
.mark loopBody507_78

def loopBody507_80 : HolLoopProg 64 :=
.seq loopBody507_29 loopBody507_79

def loopBody507_81 : HolLoopProg 64 :=
.mark loopBody507_80

def loopBody507_82 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_81

def loopBody507_83 : HolLoopProg 64 :=
.mark loopBody507_82

def loopBody507_84 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_83

def loopBody507_85 : HolLoopProg 64 :=
.mark loopBody507_84

def loopBody507_86 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_85

def loopBody507_87 : HolLoopProg 64 :=
.mark loopBody507_86

def loopBody507_88 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_87

def loopBody507_89 : HolLoopProg 64 :=
.mark loopBody507_88

def loopBody507_90 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_89

def loopBody507_91 : HolLoopProg 64 :=
.mark loopBody507_90

def loopBody507_92 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_91

def loopBody507_93 : HolLoopProg 64 :=
.mark loopBody507_92

def loopBody507_94 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_93

def loopBody507_95 : HolLoopProg 64 :=
.mark loopBody507_94

def loopBody507_96 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_95

def loopBody507_97 : HolLoopProg 64 :=
.mark loopBody507_96

def loopBody507_98 : HolLoopProg 64 :=
.seq loopBody507_19 loopBody507_97

def loopBody507_99 : HolLoopProg 64 :=
.mark loopBody507_98

def loopBody507_100 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_99

def loopBody507_101 : HolLoopProg 64 :=
.mark loopBody507_100

def loopBody507_102 : HolLoopProg 64 :=
.seq loopBody507_1 loopBody507_101

def loopBody507_103 : HolLoopProg 64 :=
.mark loopBody507_102

def loopBody507_104 : HolLoopProg 64 :=
.seq loopBody507_15 loopBody507_103

def loopBody507_105 : HolLoopProg 64 :=
.mark loopBody507_104

def output507 : Nat × List Nat × HolLoopProg 64 :=
  (571, [], loopBody507_105)
end InitECandidate.Proofs.FrontendStages.Loop
