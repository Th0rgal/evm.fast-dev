import InitECandidate.Proofs.FrontendStages.Loop.Translate400
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody416_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody416_1 : HolLoopProg 64 :=
.mark loopBody416_0

def loopBody416_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody416_3 : HolLoopProg 64 :=
.mark loopBody416_2

def loopBody416_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 2)

def loopBody416_5 : HolLoopProg 64 :=
.mark loopBody416_4

def loopBody416_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 1)

def loopBody416_7 : HolLoopProg 64 :=
.mark loopBody416_6

def loopBody416_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody416_9 : HolLoopProg 64 :=
.mark loopBody416_8

def loopBody416_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody416_11 : HolLoopProg 64 :=
.mark loopBody416_10

def loopBody416_12 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody416_9 loopBody416_11 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody416_13 : HolLoopProg 64 :=
.mark loopBody416_12

def loopBody416_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody416_15 : HolLoopProg 64 :=
.mark loopBody416_14

def loopBody416_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.var 2])

def loopBody416_17 : HolLoopProg 64 :=
.mark loopBody416_16

def loopBody416_18 : HolLoopProg 64 :=
.seq loopBody416_17 loopBody416_1

def loopBody416_19 : HolLoopProg 64 :=
.mark loopBody416_18

def loopBody416_20 : HolLoopProg 64 :=
.seq loopBody416_19 loopBody416_1

def loopBody416_21 : HolLoopProg 64 :=
.mark loopBody416_20

def loopBody416_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 3)

def loopBody416_23 : HolLoopProg 64 :=
.mark loopBody416_22

def loopBody416_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 5)

def loopBody416_25 : HolLoopProg 64 :=
.mark loopBody416_24

def loopBody416_26 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 7 (Flapjack.RegImm.reg 8) loopBody416_9 loopBody416_11 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody416_27 : HolLoopProg 64 :=
.mark loopBody416_26

def loopBody416_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 3)

def loopBody416_29 : HolLoopProg 64 :=
.mark loopBody416_28

def loopBody416_30 : HolLoopProg 64 :=
.seq loopBody416_29 loopBody416_1

def loopBody416_31 : HolLoopProg 64 :=
.mark loopBody416_30

def loopBody416_32 : HolLoopProg 64 :=
.seq loopBody416_31 loopBody416_1

def loopBody416_33 : HolLoopProg 64 :=
.mark loopBody416_32

def loopBody416_34 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody416_33 loopBody416_1 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))

def loopBody416_35 : HolLoopProg 64 :=
.mark loopBody416_34

def loopBody416_36 : HolLoopProg 64 :=
.seq loopBody416_35 loopBody416_1

def loopBody416_37 : HolLoopProg 64 :=
.mark loopBody416_36

def loopBody416_38 : HolLoopProg 64 :=
.seq loopBody416_15 loopBody416_37

def loopBody416_39 : HolLoopProg 64 :=
.mark loopBody416_38

def loopBody416_40 : HolLoopProg 64 :=
.seq loopBody416_27 loopBody416_39

def loopBody416_41 : HolLoopProg 64 :=
.mark loopBody416_40

def loopBody416_42 : HolLoopProg 64 :=
.seq loopBody416_25 loopBody416_41

def loopBody416_43 : HolLoopProg 64 :=
.mark loopBody416_42

def loopBody416_44 : HolLoopProg 64 :=
.seq loopBody416_23 loopBody416_43

def loopBody416_45 : HolLoopProg 64 :=
.mark loopBody416_44

def loopBody416_46 : HolLoopProg 64 :=
.seq loopBody416_21 loopBody416_45

def loopBody416_47 : HolLoopProg 64 :=
.mark loopBody416_46

def loopBody416_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 4)

def loopBody416_49 : HolLoopProg 64 :=
.mark loopBody416_48

def loopBody416_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.var 2])

def loopBody416_51 : HolLoopProg 64 :=
.mark loopBody416_50

def loopBody416_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 5)

def loopBody416_53 : HolLoopProg 64 :=
.mark loopBody416_52

def loopBody416_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody416_55 : HolLoopProg 64 :=
.mark loopBody416_54

def loopBody416_56 : HolLoopProg 64 :=
.call (some
  ([6],
    Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))) (some 77) ([7, 8, 9]) (some (7, loopBody416_55, loopBody416_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))

def loopBody416_57 : HolLoopProg 64 :=
.mark loopBody416_56

def loopBody416_58 : HolLoopProg 64 :=
.seq loopBody416_57 loopBody416_1

def loopBody416_59 : HolLoopProg 64 :=
.mark loopBody416_58

def loopBody416_60 : HolLoopProg 64 :=
.seq loopBody416_53 loopBody416_59

def loopBody416_61 : HolLoopProg 64 :=
.mark loopBody416_60

def loopBody416_62 : HolLoopProg 64 :=
.seq loopBody416_51 loopBody416_61

def loopBody416_63 : HolLoopProg 64 :=
.mark loopBody416_62

def loopBody416_64 : HolLoopProg 64 :=
.seq loopBody416_49 loopBody416_63

def loopBody416_65 : HolLoopProg 64 :=
.mark loopBody416_64

def loopBody416_66 : HolLoopProg 64 :=
.seq loopBody416_1 loopBody416_65

def loopBody416_67 : HolLoopProg 64 :=
.mark loopBody416_66

def loopBody416_68 : HolLoopProg 64 :=
.seq loopBody416_1 loopBody416_67

def loopBody416_69 : HolLoopProg 64 :=
.mark loopBody416_68

def loopBody416_70 : HolLoopProg 64 :=
.seq loopBody416_47 loopBody416_69

def loopBody416_71 : HolLoopProg 64 :=
.mark loopBody416_70

def loopBody416_72 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody416_71 loopBody416_1 (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))

def loopBody416_73 : HolLoopProg 64 :=
.mark loopBody416_72

def loopBody416_74 : HolLoopProg 64 :=
.seq loopBody416_73 loopBody416_1

def loopBody416_75 : HolLoopProg 64 :=
.mark loopBody416_74

def loopBody416_76 : HolLoopProg 64 :=
.seq loopBody416_15 loopBody416_75

def loopBody416_77 : HolLoopProg 64 :=
.mark loopBody416_76

def loopBody416_78 : HolLoopProg 64 :=
.seq loopBody416_13 loopBody416_77

def loopBody416_79 : HolLoopProg 64 :=
.mark loopBody416_78

def loopBody416_80 : HolLoopProg 64 :=
.seq loopBody416_7 loopBody416_79

def loopBody416_81 : HolLoopProg 64 :=
.mark loopBody416_80

def loopBody416_82 : HolLoopProg 64 :=
.seq loopBody416_5 loopBody416_81

def loopBody416_83 : HolLoopProg 64 :=
.mark loopBody416_82

def loopBody416_84 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 5])

def loopBody416_85 : HolLoopProg 64 :=
.mark loopBody416_84

def loopBody416_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.var 5])

def loopBody416_87 : HolLoopProg 64 :=
.mark loopBody416_86

def loopBody416_88 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 78) ([7, 8]) (some (7, loopBody416_55, loopBody416_1, (Flapjack.Spt.ln)))

def loopBody416_89 : HolLoopProg 64 :=
.mark loopBody416_88

def loopBody416_90 : HolLoopProg 64 :=
.seq loopBody416_89 loopBody416_1

def loopBody416_91 : HolLoopProg 64 :=
.mark loopBody416_90

def loopBody416_92 : HolLoopProg 64 :=
.seq loopBody416_87 loopBody416_91

def loopBody416_93 : HolLoopProg 64 :=
.mark loopBody416_92

def loopBody416_94 : HolLoopProg 64 :=
.seq loopBody416_85 loopBody416_93

def loopBody416_95 : HolLoopProg 64 :=
.mark loopBody416_94

def loopBody416_96 : HolLoopProg 64 :=
.seq loopBody416_1 loopBody416_95

def loopBody416_97 : HolLoopProg 64 :=
.mark loopBody416_96

def loopBody416_98 : HolLoopProg 64 :=
.seq loopBody416_1 loopBody416_97

def loopBody416_99 : HolLoopProg 64 :=
.mark loopBody416_98

def loopBody416_100 : HolLoopProg 64 :=
.seq loopBody416_83 loopBody416_99

def loopBody416_101 : HolLoopProg 64 :=
.mark loopBody416_100

def loopBody416_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody416_103 : HolLoopProg 64 :=
.mark loopBody416_102

def loopBody416_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody416_105 : HolLoopProg 64 :=
.mark loopBody416_104

def loopBody416_106 : HolLoopProg 64 :=
.seq loopBody416_105 loopBody416_1

def loopBody416_107 : HolLoopProg 64 :=
.mark loopBody416_106

def loopBody416_108 : HolLoopProg 64 :=
.seq loopBody416_103 loopBody416_107

def loopBody416_109 : HolLoopProg 64 :=
.mark loopBody416_108

def loopBody416_110 : HolLoopProg 64 :=
.seq loopBody416_101 loopBody416_109

def loopBody416_111 : HolLoopProg 64 :=
.mark loopBody416_110

def loopBody416_112 : HolLoopProg 64 :=
.seq loopBody416_3 loopBody416_111

def loopBody416_113 : HolLoopProg 64 :=
.mark loopBody416_112

def loopBody416_114 : HolLoopProg 64 :=
.seq loopBody416_1 loopBody416_113

def loopBody416_115 : HolLoopProg 64 :=
.mark loopBody416_114

def output416 : Nat × List Nat × HolLoopProg 64 :=
  (480, [0, 1, 2, 3, 4], loopBody416_115)
end InitECandidate.Proofs.FrontendStages.Loop
