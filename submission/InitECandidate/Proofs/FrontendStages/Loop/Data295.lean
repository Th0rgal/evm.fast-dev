import InitECandidate.Proofs.FrontendStages.Loop.Translate279
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody295_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody295_1 : HolLoopProg 64 :=
.mark loopBody295_0

def loopBody295_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody295_3 : HolLoopProg 64 :=
.mark loopBody295_2

def loopBody295_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody295_5 : HolLoopProg 64 :=
.mark loopBody295_4

def loopBody295_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody295_7 : HolLoopProg 64 :=
.mark loopBody295_6

def loopBody295_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody295_9 : HolLoopProg 64 :=
.mark loopBody295_8

def loopBody295_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 2

def loopBody295_11 : HolLoopProg 64 :=
.mark loopBody295_10

def loopBody295_12 : HolLoopProg 64 :=
.call (some ([1], Flapjack.Spt.ls PUnit.unit)) (some 354) ([2, 3, 4, 5]) (some (2, loopBody295_11, loopBody295_1, (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody295_13 : HolLoopProg 64 :=
.mark loopBody295_12

def loopBody295_14 : HolLoopProg 64 :=
.seq loopBody295_13 loopBody295_1

def loopBody295_15 : HolLoopProg 64 :=
.mark loopBody295_14

def loopBody295_16 : HolLoopProg 64 :=
.seq loopBody295_9 loopBody295_15

def loopBody295_17 : HolLoopProg 64 :=
.mark loopBody295_16

def loopBody295_18 : HolLoopProg 64 :=
.seq loopBody295_7 loopBody295_17

def loopBody295_19 : HolLoopProg 64 :=
.mark loopBody295_18

def loopBody295_20 : HolLoopProg 64 :=
.seq loopBody295_5 loopBody295_19

def loopBody295_21 : HolLoopProg 64 :=
.mark loopBody295_20

def loopBody295_22 : HolLoopProg 64 :=
.seq loopBody295_3 loopBody295_21

def loopBody295_23 : HolLoopProg 64 :=
.mark loopBody295_22

def loopBody295_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 40#64]))

def loopBody295_25 : HolLoopProg 64 :=
.mark loopBody295_24

def loopBody295_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 3

def loopBody295_27 : HolLoopProg 64 :=
.mark loopBody295_26

def loopBody295_28 : HolLoopProg 64 :=
.call (some ([2], Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 181) ([3]) (some (3, loopBody295_27, loopBody295_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody295_29 : HolLoopProg 64 :=
.mark loopBody295_28

def loopBody295_30 : HolLoopProg 64 :=
.seq loopBody295_29 loopBody295_1

def loopBody295_31 : HolLoopProg 64 :=
.mark loopBody295_30

def loopBody295_32 : HolLoopProg 64 :=
.seq loopBody295_25 loopBody295_31

def loopBody295_33 : HolLoopProg 64 :=
.mark loopBody295_32

def loopBody295_34 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 48#64]))

def loopBody295_35 : HolLoopProg 64 :=
.mark loopBody295_34

def loopBody295_36 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 4

def loopBody295_37 : HolLoopProg 64 :=
.mark loopBody295_36

def loopBody295_38 : HolLoopProg 64 :=
.call (some ([3], Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) (some 181) ([4]) (some (4, loopBody295_37, loopBody295_1, (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody295_39 : HolLoopProg 64 :=
.mark loopBody295_38

def loopBody295_40 : HolLoopProg 64 :=
.seq loopBody295_39 loopBody295_1

def loopBody295_41 : HolLoopProg 64 :=
.mark loopBody295_40

def loopBody295_42 : HolLoopProg 64 :=
.seq loopBody295_35 loopBody295_41

def loopBody295_43 : HolLoopProg 64 :=
.mark loopBody295_42

def loopBody295_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 56#64]))

def loopBody295_45 : HolLoopProg 64 :=
.mark loopBody295_44

def loopBody295_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 56#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody295_47 : HolLoopProg 64 :=
.mark loopBody295_46

def loopBody295_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 56#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody295_49 : HolLoopProg 64 :=
.mark loopBody295_48

def loopBody295_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 56#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody295_51 : HolLoopProg 64 :=
.mark loopBody295_50

def loopBody295_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody295_53 : HolLoopProg 64 :=
.mark loopBody295_52

def loopBody295_54 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 354) ([5, 6, 7, 8]) (some (5, loopBody295_53, loopBody295_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody295_55 : HolLoopProg 64 :=
.mark loopBody295_54

def loopBody295_56 : HolLoopProg 64 :=
.seq loopBody295_55 loopBody295_1

def loopBody295_57 : HolLoopProg 64 :=
.mark loopBody295_56

def loopBody295_58 : HolLoopProg 64 :=
.seq loopBody295_51 loopBody295_57

def loopBody295_59 : HolLoopProg 64 :=
.mark loopBody295_58

def loopBody295_60 : HolLoopProg 64 :=
.seq loopBody295_49 loopBody295_59

def loopBody295_61 : HolLoopProg 64 :=
.mark loopBody295_60

def loopBody295_62 : HolLoopProg 64 :=
.seq loopBody295_47 loopBody295_61

def loopBody295_63 : HolLoopProg 64 :=
.mark loopBody295_62

def loopBody295_64 : HolLoopProg 64 :=
.seq loopBody295_45 loopBody295_63

def loopBody295_65 : HolLoopProg 64 :=
.mark loopBody295_64

def loopBody295_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 88#64]))

def loopBody295_67 : HolLoopProg 64 :=
.mark loopBody295_66

def loopBody295_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 88#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody295_69 : HolLoopProg 64 :=
.mark loopBody295_68

def loopBody295_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 88#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody295_71 : HolLoopProg 64 :=
.mark loopBody295_70

def loopBody295_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 88#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody295_73 : HolLoopProg 64 :=
.mark loopBody295_72

def loopBody295_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 6

def loopBody295_75 : HolLoopProg 64 :=
.mark loopBody295_74

def loopBody295_76 : HolLoopProg 64 :=
.call (some
  ([5],
    Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 354) ([6, 7, 8, 9]) (some (6, loopBody295_75, loopBody295_1, (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody295_77 : HolLoopProg 64 :=
.mark loopBody295_76

def loopBody295_78 : HolLoopProg 64 :=
.seq loopBody295_77 loopBody295_1

def loopBody295_79 : HolLoopProg 64 :=
.mark loopBody295_78

def loopBody295_80 : HolLoopProg 64 :=
.seq loopBody295_73 loopBody295_79

def loopBody295_81 : HolLoopProg 64 :=
.mark loopBody295_80

def loopBody295_82 : HolLoopProg 64 :=
.seq loopBody295_71 loopBody295_81

def loopBody295_83 : HolLoopProg 64 :=
.mark loopBody295_82

def loopBody295_84 : HolLoopProg 64 :=
.seq loopBody295_69 loopBody295_83

def loopBody295_85 : HolLoopProg 64 :=
.mark loopBody295_84

def loopBody295_86 : HolLoopProg 64 :=
.seq loopBody295_67 loopBody295_85

def loopBody295_87 : HolLoopProg 64 :=
.mark loopBody295_86

def loopBody295_88 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 21#64, Flapjack.HolLoopExp.var 2, Flapjack.HolLoopExp.var 3,
      Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 5])

def loopBody295_89 : HolLoopProg 64 :=
.mark loopBody295_88

def loopBody295_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [6]

def loopBody295_91 : HolLoopProg 64 :=
.mark loopBody295_90

def loopBody295_92 : HolLoopProg 64 :=
.seq loopBody295_91 loopBody295_1

def loopBody295_93 : HolLoopProg 64 :=
.mark loopBody295_92

def loopBody295_94 : HolLoopProg 64 :=
.seq loopBody295_89 loopBody295_93

def loopBody295_95 : HolLoopProg 64 :=
.mark loopBody295_94

def loopBody295_96 : HolLoopProg 64 :=
.seq loopBody295_87 loopBody295_95

def loopBody295_97 : HolLoopProg 64 :=
.mark loopBody295_96

def loopBody295_98 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_97

def loopBody295_99 : HolLoopProg 64 :=
.mark loopBody295_98

def loopBody295_100 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_99

def loopBody295_101 : HolLoopProg 64 :=
.mark loopBody295_100

def loopBody295_102 : HolLoopProg 64 :=
.seq loopBody295_65 loopBody295_101

def loopBody295_103 : HolLoopProg 64 :=
.mark loopBody295_102

def loopBody295_104 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_103

def loopBody295_105 : HolLoopProg 64 :=
.mark loopBody295_104

def loopBody295_106 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_105

def loopBody295_107 : HolLoopProg 64 :=
.mark loopBody295_106

def loopBody295_108 : HolLoopProg 64 :=
.seq loopBody295_43 loopBody295_107

def loopBody295_109 : HolLoopProg 64 :=
.mark loopBody295_108

def loopBody295_110 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_109

def loopBody295_111 : HolLoopProg 64 :=
.mark loopBody295_110

def loopBody295_112 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_111

def loopBody295_113 : HolLoopProg 64 :=
.mark loopBody295_112

def loopBody295_114 : HolLoopProg 64 :=
.seq loopBody295_33 loopBody295_113

def loopBody295_115 : HolLoopProg 64 :=
.mark loopBody295_114

def loopBody295_116 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_115

def loopBody295_117 : HolLoopProg 64 :=
.mark loopBody295_116

def loopBody295_118 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_117

def loopBody295_119 : HolLoopProg 64 :=
.mark loopBody295_118

def loopBody295_120 : HolLoopProg 64 :=
.seq loopBody295_23 loopBody295_119

def loopBody295_121 : HolLoopProg 64 :=
.mark loopBody295_120

def loopBody295_122 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_121

def loopBody295_123 : HolLoopProg 64 :=
.mark loopBody295_122

def loopBody295_124 : HolLoopProg 64 :=
.seq loopBody295_1 loopBody295_123

def loopBody295_125 : HolLoopProg 64 :=
.mark loopBody295_124

def output295 : Nat × List Nat × HolLoopProg 64 :=
  (359, [0], loopBody295_125)
end InitECandidate.Proofs.FrontendStages.Loop
