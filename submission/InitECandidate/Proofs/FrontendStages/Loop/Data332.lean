import InitECandidate.Proofs.FrontendStages.Loop.Translate316
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody332_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody332_1 : HolLoopProg 64 :=
.mark loopBody332_0

def loopBody332_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 168#64]),
        Flapjack.HolLoopExp.const 32#64]))

def loopBody332_3 : HolLoopProg 64 :=
.mark loopBody332_2

def loopBody332_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 1)

def loopBody332_5 : HolLoopProg 64 :=
.mark loopBody332_4

def loopBody332_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 0)

def loopBody332_7 : HolLoopProg 64 :=
.mark loopBody332_6

def loopBody332_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody332_9 : HolLoopProg 64 :=
.mark loopBody332_8

def loopBody332_10 : HolLoopProg 64 :=
.call (some ([2, 3], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 186) ([4, 5]) (some (4, loopBody332_9, loopBody332_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody332_11 : HolLoopProg 64 :=
.mark loopBody332_10

def loopBody332_12 : HolLoopProg 64 :=
.seq loopBody332_11 loopBody332_1

def loopBody332_13 : HolLoopProg 64 :=
.mark loopBody332_12

def loopBody332_14 : HolLoopProg 64 :=
.seq loopBody332_7 loopBody332_13

def loopBody332_15 : HolLoopProg 64 :=
.mark loopBody332_14

def loopBody332_16 : HolLoopProg 64 :=
.seq loopBody332_5 loopBody332_15

def loopBody332_17 : HolLoopProg 64 :=
.mark loopBody332_16

def loopBody332_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody332_19 : HolLoopProg 64 :=
.mark loopBody332_18

def loopBody332_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody332_21 : HolLoopProg 64 :=
.mark loopBody332_20

def loopBody332_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 1#64)

def loopBody332_23 : HolLoopProg 64 :=
.mark loopBody332_22

def loopBody332_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody332_25 : HolLoopProg 64 :=
.mark loopBody332_24

def loopBody332_26 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 5 (Flapjack.RegImm.reg 6) loopBody332_23 loopBody332_25 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody332_27 : HolLoopProg 64 :=
.mark loopBody332_26

def loopBody332_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody332_29 : HolLoopProg 64 :=
.mark loopBody332_28

def loopBody332_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 1#64])

def loopBody332_31 : HolLoopProg 64 :=
.mark loopBody332_30

def loopBody332_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [4]

def loopBody332_33 : HolLoopProg 64 :=
.mark loopBody332_32

def loopBody332_34 : HolLoopProg 64 :=
.seq loopBody332_33 loopBody332_1

def loopBody332_35 : HolLoopProg 64 :=
.mark loopBody332_34

def loopBody332_36 : HolLoopProg 64 :=
.seq loopBody332_31 loopBody332_35

def loopBody332_37 : HolLoopProg 64 :=
.mark loopBody332_36

def loopBody332_38 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 7 (Flapjack.RegImm.imm 0#64) loopBody332_37 loopBody332_1 (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))

def loopBody332_39 : HolLoopProg 64 :=
.mark loopBody332_38

def loopBody332_40 : HolLoopProg 64 :=
.seq loopBody332_39 loopBody332_1

def loopBody332_41 : HolLoopProg 64 :=
.mark loopBody332_40

def loopBody332_42 : HolLoopProg 64 :=
.seq loopBody332_29 loopBody332_41

def loopBody332_43 : HolLoopProg 64 :=
.mark loopBody332_42

def loopBody332_44 : HolLoopProg 64 :=
.seq loopBody332_27 loopBody332_43

def loopBody332_45 : HolLoopProg 64 :=
.mark loopBody332_44

def loopBody332_46 : HolLoopProg 64 :=
.seq loopBody332_21 loopBody332_45

def loopBody332_47 : HolLoopProg 64 :=
.mark loopBody332_46

def loopBody332_48 : HolLoopProg 64 :=
.seq loopBody332_19 loopBody332_47

def loopBody332_49 : HolLoopProg 64 :=
.mark loopBody332_48

def loopBody332_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.load
          (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.topAddr, Flapjack.HolLoopExp.const 168#64]),
        Flapjack.HolLoopExp.const 0#64]))

def loopBody332_51 : HolLoopProg 64 :=
.mark loopBody332_50

def loopBody332_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 0)

def loopBody332_53 : HolLoopProg 64 :=
.mark loopBody332_52

def loopBody332_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody332_55 : HolLoopProg 64 :=
.mark loopBody332_54

def loopBody332_56 : HolLoopProg 64 :=
.call (some ([4], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 301) ([5, 6]) (some (5, loopBody332_55, loopBody332_1, (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody332_57 : HolLoopProg 64 :=
.mark loopBody332_56

def loopBody332_58 : HolLoopProg 64 :=
.seq loopBody332_57 loopBody332_1

def loopBody332_59 : HolLoopProg 64 :=
.mark loopBody332_58

def loopBody332_60 : HolLoopProg 64 :=
.seq loopBody332_53 loopBody332_59

def loopBody332_61 : HolLoopProg 64 :=
.mark loopBody332_60

def loopBody332_62 : HolLoopProg 64 :=
.seq loopBody332_51 loopBody332_61

def loopBody332_63 : HolLoopProg 64 :=
.mark loopBody332_62

def loopBody332_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 1)

def loopBody332_65 : HolLoopProg 64 :=
.mark loopBody332_64

def loopBody332_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody332_67 : HolLoopProg 64 :=
.mark loopBody332_66

def loopBody332_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 1#64])

def loopBody332_69 : HolLoopProg 64 :=
.mark loopBody332_68

def loopBody332_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody332_71 : HolLoopProg 64 :=
.mark loopBody332_70

def loopBody332_72 : HolLoopProg 64 :=
.call (some ([5], Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)) (some 192) ([6, 7, 8]) (some (6, loopBody332_71, loopBody332_1, (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))

def loopBody332_73 : HolLoopProg 64 :=
.mark loopBody332_72

def loopBody332_74 : HolLoopProg 64 :=
.seq loopBody332_73 loopBody332_1

def loopBody332_75 : HolLoopProg 64 :=
.mark loopBody332_74

def loopBody332_76 : HolLoopProg 64 :=
.seq loopBody332_69 loopBody332_75

def loopBody332_77 : HolLoopProg 64 :=
.mark loopBody332_76

def loopBody332_78 : HolLoopProg 64 :=
.seq loopBody332_67 loopBody332_77

def loopBody332_79 : HolLoopProg 64 :=
.mark loopBody332_78

def loopBody332_80 : HolLoopProg 64 :=
.seq loopBody332_65 loopBody332_79

def loopBody332_81 : HolLoopProg 64 :=
.mark loopBody332_80

def loopBody332_82 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_81

def loopBody332_83 : HolLoopProg 64 :=
.mark loopBody332_82

def loopBody332_84 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_83

def loopBody332_85 : HolLoopProg 64 :=
.mark loopBody332_84

def loopBody332_86 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 4)

def loopBody332_87 : HolLoopProg 64 :=
.mark loopBody332_86

def loopBody332_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [5]

def loopBody332_89 : HolLoopProg 64 :=
.mark loopBody332_88

def loopBody332_90 : HolLoopProg 64 :=
.seq loopBody332_89 loopBody332_1

def loopBody332_91 : HolLoopProg 64 :=
.mark loopBody332_90

def loopBody332_92 : HolLoopProg 64 :=
.seq loopBody332_87 loopBody332_91

def loopBody332_93 : HolLoopProg 64 :=
.mark loopBody332_92

def loopBody332_94 : HolLoopProg 64 :=
.seq loopBody332_85 loopBody332_93

def loopBody332_95 : HolLoopProg 64 :=
.mark loopBody332_94

def loopBody332_96 : HolLoopProg 64 :=
.seq loopBody332_63 loopBody332_95

def loopBody332_97 : HolLoopProg 64 :=
.mark loopBody332_96

def loopBody332_98 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_97

def loopBody332_99 : HolLoopProg 64 :=
.mark loopBody332_98

def loopBody332_100 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_99

def loopBody332_101 : HolLoopProg 64 :=
.mark loopBody332_100

def loopBody332_102 : HolLoopProg 64 :=
.seq loopBody332_49 loopBody332_101

def loopBody332_103 : HolLoopProg 64 :=
.mark loopBody332_102

def loopBody332_104 : HolLoopProg 64 :=
.seq loopBody332_17 loopBody332_103

def loopBody332_105 : HolLoopProg 64 :=
.mark loopBody332_104

def loopBody332_106 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_105

def loopBody332_107 : HolLoopProg 64 :=
.mark loopBody332_106

def loopBody332_108 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_107

def loopBody332_109 : HolLoopProg 64 :=
.mark loopBody332_108

def loopBody332_110 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_109

def loopBody332_111 : HolLoopProg 64 :=
.mark loopBody332_110

def loopBody332_112 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_111

def loopBody332_113 : HolLoopProg 64 :=
.mark loopBody332_112

def loopBody332_114 : HolLoopProg 64 :=
.seq loopBody332_3 loopBody332_113

def loopBody332_115 : HolLoopProg 64 :=
.mark loopBody332_114

def loopBody332_116 : HolLoopProg 64 :=
.seq loopBody332_1 loopBody332_115

def loopBody332_117 : HolLoopProg 64 :=
.mark loopBody332_116

def output332 : Nat × List Nat × HolLoopProg 64 :=
  (396, [0], loopBody332_117)
end InitECandidate.Proofs.FrontendStages.Loop
