import InitECandidate.Proofs.FrontendStages.Loop.Translate430
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody446_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody446_1 : HolLoopProg 64 :=
.mark loopBody446_0

def loopBody446_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody446_3 : HolLoopProg 64 :=
.mark loopBody446_2

def loopBody446_4 : HolLoopProg 64 :=
.call (some ([1, 2, 3, 4], Flapjack.Spt.ln)) (some 471) ([]) (some (5, loopBody446_3, loopBody446_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody446_5 : HolLoopProg 64 :=
.mark loopBody446_4

def loopBody446_6 : HolLoopProg 64 :=
.seq loopBody446_5 loopBody446_1

def loopBody446_7 : HolLoopProg 64 :=
.mark loopBody446_6

def loopBody446_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody446_9 : HolLoopProg 64 :=
.mark loopBody446_8

def loopBody446_10 : HolLoopProg 64 :=
.call (some
  ([5, 6, 7, 8],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 471) ([]) (some (9, loopBody446_9, loopBody446_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody446_11 : HolLoopProg 64 :=
.mark loopBody446_10

def loopBody446_12 : HolLoopProg 64 :=
.seq loopBody446_11 loopBody446_1

def loopBody446_13 : HolLoopProg 64 :=
.mark loopBody446_12

def loopBody446_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 3#64)

def loopBody446_15 : HolLoopProg 64 :=
.mark loopBody446_14

def loopBody446_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody446_17 : HolLoopProg 64 :=
.mark loopBody446_16

def loopBody446_18 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 466) ([10]) (some (10, loopBody446_17, loopBody446_1, (Flapjack.Spt.bn
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody446_19 : HolLoopProg 64 :=
.mark loopBody446_18

def loopBody446_20 : HolLoopProg 64 :=
.seq loopBody446_19 loopBody446_1

def loopBody446_21 : HolLoopProg 64 :=
.mark loopBody446_20

def loopBody446_22 : HolLoopProg 64 :=
.seq loopBody446_15 loopBody446_21

def loopBody446_23 : HolLoopProg 64 :=
.mark loopBody446_22

def loopBody446_24 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_23

def loopBody446_25 : HolLoopProg 64 :=
.mark loopBody446_24

def loopBody446_26 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_25

def loopBody446_27 : HolLoopProg 64 :=
.mark loopBody446_26

def loopBody446_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 5])

def loopBody446_29 : HolLoopProg 64 :=
.mark loopBody446_28

def loopBody446_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 6])

def loopBody446_31 : HolLoopProg 64 :=
.mark loopBody446_30

def loopBody446_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.var 7])

def loopBody446_33 : HolLoopProg 64 :=
.mark loopBody446_32

def loopBody446_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.and [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 8])

def loopBody446_35 : HolLoopProg 64 :=
.mark loopBody446_34

def loopBody446_36 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 472) ([10, 11, 12, 13]) (some (10, loopBody446_17, loopBody446_1, (Flapjack.Spt.ln)))

def loopBody446_37 : HolLoopProg 64 :=
.mark loopBody446_36

def loopBody446_38 : HolLoopProg 64 :=
.seq loopBody446_37 loopBody446_1

def loopBody446_39 : HolLoopProg 64 :=
.mark loopBody446_38

def loopBody446_40 : HolLoopProg 64 :=
.seq loopBody446_35 loopBody446_39

def loopBody446_41 : HolLoopProg 64 :=
.mark loopBody446_40

def loopBody446_42 : HolLoopProg 64 :=
.seq loopBody446_33 loopBody446_41

def loopBody446_43 : HolLoopProg 64 :=
.mark loopBody446_42

def loopBody446_44 : HolLoopProg 64 :=
.seq loopBody446_31 loopBody446_43

def loopBody446_45 : HolLoopProg 64 :=
.mark loopBody446_44

def loopBody446_46 : HolLoopProg 64 :=
.seq loopBody446_29 loopBody446_45

def loopBody446_47 : HolLoopProg 64 :=
.mark loopBody446_46

def loopBody446_48 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_47

def loopBody446_49 : HolLoopProg 64 :=
.mark loopBody446_48

def loopBody446_50 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_49

def loopBody446_51 : HolLoopProg 64 :=
.mark loopBody446_50

def loopBody446_52 : HolLoopProg 64 :=
.seq loopBody446_27 loopBody446_51

def loopBody446_53 : HolLoopProg 64 :=
.mark loopBody446_52

def loopBody446_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 1#64)

def loopBody446_55 : HolLoopProg 64 :=
.mark loopBody446_54

def loopBody446_56 : HolLoopProg 64 :=
.call (some ([9], Flapjack.Spt.ln)) (some 486) ([10]) (some (10, loopBody446_17, loopBody446_1, (Flapjack.Spt.ln)))

def loopBody446_57 : HolLoopProg 64 :=
.mark loopBody446_56

def loopBody446_58 : HolLoopProg 64 :=
.seq loopBody446_57 loopBody446_1

def loopBody446_59 : HolLoopProg 64 :=
.mark loopBody446_58

def loopBody446_60 : HolLoopProg 64 :=
.seq loopBody446_55 loopBody446_59

def loopBody446_61 : HolLoopProg 64 :=
.mark loopBody446_60

def loopBody446_62 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_61

def loopBody446_63 : HolLoopProg 64 :=
.mark loopBody446_62

def loopBody446_64 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_63

def loopBody446_65 : HolLoopProg 64 :=
.mark loopBody446_64

def loopBody446_66 : HolLoopProg 64 :=
.seq loopBody446_53 loopBody446_65

def loopBody446_67 : HolLoopProg 64 :=
.mark loopBody446_66

def loopBody446_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody446_69 : HolLoopProg 64 :=
.mark loopBody446_68

def loopBody446_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [9]

def loopBody446_71 : HolLoopProg 64 :=
.mark loopBody446_70

def loopBody446_72 : HolLoopProg 64 :=
.seq loopBody446_71 loopBody446_1

def loopBody446_73 : HolLoopProg 64 :=
.mark loopBody446_72

def loopBody446_74 : HolLoopProg 64 :=
.seq loopBody446_69 loopBody446_73

def loopBody446_75 : HolLoopProg 64 :=
.mark loopBody446_74

def loopBody446_76 : HolLoopProg 64 :=
.seq loopBody446_67 loopBody446_75

def loopBody446_77 : HolLoopProg 64 :=
.mark loopBody446_76

def loopBody446_78 : HolLoopProg 64 :=
.seq loopBody446_13 loopBody446_77

def loopBody446_79 : HolLoopProg 64 :=
.mark loopBody446_78

def loopBody446_80 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_79

def loopBody446_81 : HolLoopProg 64 :=
.mark loopBody446_80

def loopBody446_82 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_81

def loopBody446_83 : HolLoopProg 64 :=
.mark loopBody446_82

def loopBody446_84 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_83

def loopBody446_85 : HolLoopProg 64 :=
.mark loopBody446_84

def loopBody446_86 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_85

def loopBody446_87 : HolLoopProg 64 :=
.mark loopBody446_86

def loopBody446_88 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_87

def loopBody446_89 : HolLoopProg 64 :=
.mark loopBody446_88

def loopBody446_90 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_89

def loopBody446_91 : HolLoopProg 64 :=
.mark loopBody446_90

def loopBody446_92 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_91

def loopBody446_93 : HolLoopProg 64 :=
.mark loopBody446_92

def loopBody446_94 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_93

def loopBody446_95 : HolLoopProg 64 :=
.mark loopBody446_94

def loopBody446_96 : HolLoopProg 64 :=
.seq loopBody446_7 loopBody446_95

def loopBody446_97 : HolLoopProg 64 :=
.mark loopBody446_96

def loopBody446_98 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_97

def loopBody446_99 : HolLoopProg 64 :=
.mark loopBody446_98

def loopBody446_100 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_99

def loopBody446_101 : HolLoopProg 64 :=
.mark loopBody446_100

def loopBody446_102 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_101

def loopBody446_103 : HolLoopProg 64 :=
.mark loopBody446_102

def loopBody446_104 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_103

def loopBody446_105 : HolLoopProg 64 :=
.mark loopBody446_104

def loopBody446_106 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_105

def loopBody446_107 : HolLoopProg 64 :=
.mark loopBody446_106

def loopBody446_108 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_107

def loopBody446_109 : HolLoopProg 64 :=
.mark loopBody446_108

def loopBody446_110 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_109

def loopBody446_111 : HolLoopProg 64 :=
.mark loopBody446_110

def loopBody446_112 : HolLoopProg 64 :=
.seq loopBody446_1 loopBody446_111

def loopBody446_113 : HolLoopProg 64 :=
.mark loopBody446_112

def output446 : Nat × List Nat × HolLoopProg 64 :=
  (510, [], loopBody446_113)
end InitECandidate.Proofs.FrontendStages.Loop
