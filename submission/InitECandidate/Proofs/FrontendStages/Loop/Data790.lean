import InitECandidate.Proofs.FrontendStages.Loop.Translate774
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody790_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody790_1 : HolLoopProg 64 :=
.mark loopBody790_0

def loopBody790_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 1
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody790_3 : HolLoopProg 64 :=
.mark loopBody790_2

def loopBody790_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 32#64]))

def loopBody790_5 : HolLoopProg 64 :=
.mark loopBody790_4

def loopBody790_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 40#64]))

def loopBody790_7 : HolLoopProg 64 :=
.mark loopBody790_6

def loopBody790_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 8#64]))

def loopBody790_9 : HolLoopProg 64 :=
.mark loopBody790_8

def loopBody790_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 16#64]))

def loopBody790_11 : HolLoopProg 64 :=
.mark loopBody790_10

def loopBody790_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_13 : HolLoopProg 64 :=
.mark loopBody790_12

def loopBody790_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_15 : HolLoopProg 64 :=
.mark loopBody790_14

def loopBody790_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody790_17 : HolLoopProg 64 :=
.mark loopBody790_16

def loopBody790_18 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 3)

def loopBody790_19 : HolLoopProg 64 :=
.mark loopBody790_18

def loopBody790_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 1#64)

def loopBody790_21 : HolLoopProg 64 :=
.mark loopBody790_20

def loopBody790_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_23 : HolLoopProg 64 :=
.mark loopBody790_22

def loopBody790_24 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 9 (Flapjack.RegImm.reg 10) loopBody790_21 loopBody790_23 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_25 : HolLoopProg 64 :=
.mark loopBody790_24

def loopBody790_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 9)

def loopBody790_27 : HolLoopProg 64 :=
.mark loopBody790_26

def loopBody790_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 2,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 4#64)]))

def loopBody790_29 : HolLoopProg 64 :=
.mark loopBody790_28

def loopBody790_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 2,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 7) (Flapjack.HolLoopExp.const 4#64),
        Flapjack.HolLoopExp.const 8#64]))

def loopBody790_31 : HolLoopProg 64 :=
.mark loopBody790_30

def loopBody790_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody790_33 : HolLoopProg 64 :=
.mark loopBody790_32

def loopBody790_34 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 342) ([9, 10]) (some (9, loopBody790_33, loopBody790_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody790_35 : HolLoopProg 64 :=
.mark loopBody790_34

def loopBody790_36 : HolLoopProg 64 :=
.seq loopBody790_35 loopBody790_1

def loopBody790_37 : HolLoopProg 64 :=
.mark loopBody790_36

def loopBody790_38 : HolLoopProg 64 :=
.seq loopBody790_31 loopBody790_37

def loopBody790_39 : HolLoopProg 64 :=
.mark loopBody790_38

def loopBody790_40 : HolLoopProg 64 :=
.seq loopBody790_29 loopBody790_39

def loopBody790_41 : HolLoopProg 64 :=
.mark loopBody790_40

def loopBody790_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 8)

def loopBody790_43 : HolLoopProg 64 :=
.mark loopBody790_42

def loopBody790_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 10

def loopBody790_45 : HolLoopProg 64 :=
.mark loopBody790_44

def loopBody790_46 : HolLoopProg 64 :=
.call (some
  ([9],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 851) ([10]) (some (10, loopBody790_45, loopBody790_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody790_47 : HolLoopProg 64 :=
.mark loopBody790_46

def loopBody790_48 : HolLoopProg 64 :=
.seq loopBody790_47 loopBody790_1

def loopBody790_49 : HolLoopProg 64 :=
.mark loopBody790_48

def loopBody790_50 : HolLoopProg 64 :=
.seq loopBody790_43 loopBody790_49

def loopBody790_51 : HolLoopProg 64 :=
.mark loopBody790_50

def loopBody790_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_53 : HolLoopProg 64 :=
.mark loopBody790_52

def loopBody790_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody790_55 : HolLoopProg 64 :=
.mark loopBody790_54

def loopBody790_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_57 : HolLoopProg 64 :=
.mark loopBody790_56

def loopBody790_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.reg 12) loopBody790_55 loopBody790_57 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_59 : HolLoopProg 64 :=
.mark loopBody790_58

def loopBody790_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody790_61 : HolLoopProg 64 :=
.mark loopBody790_60

def loopBody790_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 8, Flapjack.HolLoopExp.const 264#64]))

def loopBody790_63 : HolLoopProg 64 :=
.mark loopBody790_62

def loopBody790_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 10)

def loopBody790_65 : HolLoopProg 64 :=
.mark loopBody790_64

def loopBody790_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody790_67 : HolLoopProg 64 :=
.mark loopBody790_66

def loopBody790_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_69 : HolLoopProg 64 :=
.mark loopBody790_68

def loopBody790_70 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 13 (Flapjack.RegImm.reg 14) loopBody790_67 loopBody790_69 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_71 : HolLoopProg 64 :=
.mark loopBody790_70

def loopBody790_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 13)

def loopBody790_73 : HolLoopProg 64 :=
.mark loopBody790_72

def loopBody790_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 6)

def loopBody790_75 : HolLoopProg 64 :=
.mark loopBody790_74

def loopBody790_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 5)

def loopBody790_77 : HolLoopProg 64 :=
.mark loopBody790_76

def loopBody790_78 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notLower) 13 (Flapjack.RegImm.reg 14) loopBody790_67 loopBody790_69 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_79 : HolLoopProg 64 :=
.mark loopBody790_78

def loopBody790_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [12]

def loopBody790_81 : HolLoopProg 64 :=
.mark loopBody790_80

def loopBody790_82 : HolLoopProg 64 :=
.seq loopBody790_81 loopBody790_1

def loopBody790_83 : HolLoopProg 64 :=
.mark loopBody790_82

def loopBody790_84 : HolLoopProg 64 :=
.seq loopBody790_53 loopBody790_83

def loopBody790_85 : HolLoopProg 64 :=
.mark loopBody790_84

def loopBody790_86 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody790_85 loopBody790_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_87 : HolLoopProg 64 :=
.mark loopBody790_86

def loopBody790_88 : HolLoopProg 64 :=
.seq loopBody790_87 loopBody790_1

def loopBody790_89 : HolLoopProg 64 :=
.mark loopBody790_88

def loopBody790_90 : HolLoopProg 64 :=
.seq loopBody790_73 loopBody790_89

def loopBody790_91 : HolLoopProg 64 :=
.mark loopBody790_90

def loopBody790_92 : HolLoopProg 64 :=
.seq loopBody790_79 loopBody790_91

def loopBody790_93 : HolLoopProg 64 :=
.mark loopBody790_92

def loopBody790_94 : HolLoopProg 64 :=
.seq loopBody790_77 loopBody790_93

def loopBody790_95 : HolLoopProg 64 :=
.mark loopBody790_94

def loopBody790_96 : HolLoopProg 64 :=
.seq loopBody790_75 loopBody790_95

def loopBody790_97 : HolLoopProg 64 :=
.mark loopBody790_96

def loopBody790_98 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 8, Flapjack.HolLoopExp.const 256#64]),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 11) (Flapjack.HolLoopExp.const 5#64)])

def loopBody790_99 : HolLoopProg 64 :=
.mark loopBody790_98

def loopBody790_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 4,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 6) (Flapjack.HolLoopExp.const 5#64)])

def loopBody790_101 : HolLoopProg 64 :=
.mark loopBody790_100

def loopBody790_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 32#64)

def loopBody790_103 : HolLoopProg 64 :=
.mark loopBody790_102

def loopBody790_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody790_105 : HolLoopProg 64 :=
.mark loopBody790_104

def loopBody790_106 : HolLoopProg 64 :=
.call (some
  ([12],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 79) ([13, 14, 15]) (some (13, loopBody790_105, loopBody790_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody790_107 : HolLoopProg 64 :=
.mark loopBody790_106

def loopBody790_108 : HolLoopProg 64 :=
.seq loopBody790_107 loopBody790_1

def loopBody790_109 : HolLoopProg 64 :=
.mark loopBody790_108

def loopBody790_110 : HolLoopProg 64 :=
.seq loopBody790_103 loopBody790_109

def loopBody790_111 : HolLoopProg 64 :=
.mark loopBody790_110

def loopBody790_112 : HolLoopProg 64 :=
.seq loopBody790_101 loopBody790_111

def loopBody790_113 : HolLoopProg 64 :=
.mark loopBody790_112

def loopBody790_114 : HolLoopProg 64 :=
.seq loopBody790_99 loopBody790_113

def loopBody790_115 : HolLoopProg 64 :=
.mark loopBody790_114

def loopBody790_116 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody790_117 : HolLoopProg 64 :=
.mark loopBody790_116

def loopBody790_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_119 : HolLoopProg 64 :=
.mark loopBody790_118

def loopBody790_120 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody790_121 : HolLoopProg 64 :=
.mark loopBody790_120

def loopBody790_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_123 : HolLoopProg 64 :=
.mark loopBody790_122

def loopBody790_124 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.RegImm.reg 15) loopBody790_121 loopBody790_123 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_125 : HolLoopProg 64 :=
.mark loopBody790_124

def loopBody790_126 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 14)

def loopBody790_127 : HolLoopProg 64 :=
.mark loopBody790_126

def loopBody790_128 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [13]

def loopBody790_129 : HolLoopProg 64 :=
.mark loopBody790_128

def loopBody790_130 : HolLoopProg 64 :=
.seq loopBody790_129 loopBody790_1

def loopBody790_131 : HolLoopProg 64 :=
.mark loopBody790_130

def loopBody790_132 : HolLoopProg 64 :=
.seq loopBody790_69 loopBody790_131

def loopBody790_133 : HolLoopProg 64 :=
.mark loopBody790_132

def loopBody790_134 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.RegImm.imm 0#64) loopBody790_133 loopBody790_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_135 : HolLoopProg 64 :=
.mark loopBody790_134

def loopBody790_136 : HolLoopProg 64 :=
.seq loopBody790_135 loopBody790_1

def loopBody790_137 : HolLoopProg 64 :=
.mark loopBody790_136

def loopBody790_138 : HolLoopProg 64 :=
.seq loopBody790_127 loopBody790_137

def loopBody790_139 : HolLoopProg 64 :=
.mark loopBody790_138

def loopBody790_140 : HolLoopProg 64 :=
.seq loopBody790_125 loopBody790_139

def loopBody790_141 : HolLoopProg 64 :=
.mark loopBody790_140

def loopBody790_142 : HolLoopProg 64 :=
.seq loopBody790_119 loopBody790_141

def loopBody790_143 : HolLoopProg 64 :=
.mark loopBody790_142

def loopBody790_144 : HolLoopProg 64 :=
.seq loopBody790_117 loopBody790_143

def loopBody790_145 : HolLoopProg 64 :=
.mark loopBody790_144

def loopBody790_146 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 1#64])

def loopBody790_147 : HolLoopProg 64 :=
.mark loopBody790_146

def loopBody790_148 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 13)

def loopBody790_149 : HolLoopProg 64 :=
.mark loopBody790_148

def loopBody790_150 : HolLoopProg 64 :=
.seq loopBody790_149 loopBody790_1

def loopBody790_151 : HolLoopProg 64 :=
.mark loopBody790_150

def loopBody790_152 : HolLoopProg 64 :=
.seq loopBody790_151 loopBody790_1

def loopBody790_153 : HolLoopProg 64 :=
.mark loopBody790_152

def loopBody790_154 : HolLoopProg 64 :=
.seq loopBody790_147 loopBody790_153

def loopBody790_155 : HolLoopProg 64 :=
.mark loopBody790_154

def loopBody790_156 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_155

def loopBody790_157 : HolLoopProg 64 :=
.mark loopBody790_156

def loopBody790_158 : HolLoopProg 64 :=
.seq loopBody790_145 loopBody790_157

def loopBody790_159 : HolLoopProg 64 :=
.mark loopBody790_158

def loopBody790_160 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 11, Flapjack.HolLoopExp.const 1#64])

def loopBody790_161 : HolLoopProg 64 :=
.mark loopBody790_160

def loopBody790_162 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 13)

def loopBody790_163 : HolLoopProg 64 :=
.mark loopBody790_162

def loopBody790_164 : HolLoopProg 64 :=
.seq loopBody790_163 loopBody790_1

def loopBody790_165 : HolLoopProg 64 :=
.mark loopBody790_164

def loopBody790_166 : HolLoopProg 64 :=
.seq loopBody790_165 loopBody790_1

def loopBody790_167 : HolLoopProg 64 :=
.mark loopBody790_166

def loopBody790_168 : HolLoopProg 64 :=
.seq loopBody790_161 loopBody790_167

def loopBody790_169 : HolLoopProg 64 :=
.mark loopBody790_168

def loopBody790_170 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_169

def loopBody790_171 : HolLoopProg 64 :=
.mark loopBody790_170

def loopBody790_172 : HolLoopProg 64 :=
.seq loopBody790_159 loopBody790_171

def loopBody790_173 : HolLoopProg 64 :=
.mark loopBody790_172

def loopBody790_174 : HolLoopProg 64 :=
.seq loopBody790_115 loopBody790_173

def loopBody790_175 : HolLoopProg 64 :=
.mark loopBody790_174

def loopBody790_176 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_175

def loopBody790_177 : HolLoopProg 64 :=
.mark loopBody790_176

def loopBody790_178 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_177

def loopBody790_179 : HolLoopProg 64 :=
.mark loopBody790_178

def loopBody790_180 : HolLoopProg 64 :=
.seq loopBody790_97 loopBody790_179

def loopBody790_181 : HolLoopProg 64 :=
.mark loopBody790_180

def loopBody790_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody790_183 : HolLoopProg 64 :=
.mark loopBody790_182

def loopBody790_184 : HolLoopProg 64 :=
.seq loopBody790_181 loopBody790_183

def loopBody790_185 : HolLoopProg 64 :=
.mark loopBody790_184

def loopBody790_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody790_187 : HolLoopProg 64 :=
.mark loopBody790_186

def loopBody790_188 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody790_185 loopBody790_187 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_189 : HolLoopProg 64 :=
.mark loopBody790_188

def loopBody790_190 : HolLoopProg 64 :=
.seq loopBody790_189 loopBody790_1

def loopBody790_191 : HolLoopProg 64 :=
.mark loopBody790_190

def loopBody790_192 : HolLoopProg 64 :=
.seq loopBody790_73 loopBody790_191

def loopBody790_193 : HolLoopProg 64 :=
.mark loopBody790_192

def loopBody790_194 : HolLoopProg 64 :=
.seq loopBody790_71 loopBody790_193

def loopBody790_195 : HolLoopProg 64 :=
.mark loopBody790_194

def loopBody790_196 : HolLoopProg 64 :=
.seq loopBody790_65 loopBody790_195

def loopBody790_197 : HolLoopProg 64 :=
.mark loopBody790_196

def loopBody790_198 : HolLoopProg 64 :=
.seq loopBody790_61 loopBody790_197

def loopBody790_199 : HolLoopProg 64 :=
.mark loopBody790_198

def loopBody790_200 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody790_199 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_201 : HolLoopProg 64 :=
.seq loopBody790_57 loopBody790_200

def loopBody790_202 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_201

def loopBody790_203 : HolLoopProg 64 :=
.seq loopBody790_63 loopBody790_202

def loopBody790_204 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_203

def loopBody790_205 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody790_204 loopBody790_1 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_206 : HolLoopProg 64 :=
.seq loopBody790_205 loopBody790_1

def loopBody790_207 : HolLoopProg 64 :=
.seq loopBody790_61 loopBody790_206

def loopBody790_208 : HolLoopProg 64 :=
.seq loopBody790_59 loopBody790_207

def loopBody790_209 : HolLoopProg 64 :=
.seq loopBody790_53 loopBody790_208

def loopBody790_210 : HolLoopProg 64 :=
.seq loopBody790_27 loopBody790_209

def loopBody790_211 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 1#64])

def loopBody790_212 : HolLoopProg 64 :=
.mark loopBody790_211

def loopBody790_213 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 10)

def loopBody790_214 : HolLoopProg 64 :=
.mark loopBody790_213

def loopBody790_215 : HolLoopProg 64 :=
.seq loopBody790_214 loopBody790_1

def loopBody790_216 : HolLoopProg 64 :=
.mark loopBody790_215

def loopBody790_217 : HolLoopProg 64 :=
.seq loopBody790_216 loopBody790_1

def loopBody790_218 : HolLoopProg 64 :=
.mark loopBody790_217

def loopBody790_219 : HolLoopProg 64 :=
.seq loopBody790_212 loopBody790_218

def loopBody790_220 : HolLoopProg 64 :=
.mark loopBody790_219

def loopBody790_221 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_220

def loopBody790_222 : HolLoopProg 64 :=
.mark loopBody790_221

def loopBody790_223 : HolLoopProg 64 :=
.seq loopBody790_210 loopBody790_222

def loopBody790_224 : HolLoopProg 64 :=
.seq loopBody790_51 loopBody790_223

def loopBody790_225 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_224

def loopBody790_226 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_225

def loopBody790_227 : HolLoopProg 64 :=
.seq loopBody790_41 loopBody790_226

def loopBody790_228 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_227

def loopBody790_229 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_228

def loopBody790_230 : HolLoopProg 64 :=
.seq loopBody790_229 loopBody790_183

def loopBody790_231 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody790_230 loopBody790_187 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody790_232 : HolLoopProg 64 :=
.seq loopBody790_231 loopBody790_1

def loopBody790_233 : HolLoopProg 64 :=
.seq loopBody790_27 loopBody790_232

def loopBody790_234 : HolLoopProg 64 :=
.seq loopBody790_25 loopBody790_233

def loopBody790_235 : HolLoopProg 64 :=
.seq loopBody790_19 loopBody790_234

def loopBody790_236 : HolLoopProg 64 :=
.seq loopBody790_17 loopBody790_235

def loopBody790_237 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody790_236 (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))

def loopBody790_238 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 6)

def loopBody790_239 : HolLoopProg 64 :=
.mark loopBody790_238

def loopBody790_240 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 5)

def loopBody790_241 : HolLoopProg 64 :=
.mark loopBody790_240

def loopBody790_242 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.reg 10) loopBody790_21 loopBody790_23 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))

def loopBody790_243 : HolLoopProg 64 :=
.mark loopBody790_242

def loopBody790_244 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody790_245 : HolLoopProg 64 :=
.mark loopBody790_244

def loopBody790_246 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [8]

def loopBody790_247 : HolLoopProg 64 :=
.mark loopBody790_246

def loopBody790_248 : HolLoopProg 64 :=
.seq loopBody790_247 loopBody790_1

def loopBody790_249 : HolLoopProg 64 :=
.mark loopBody790_248

def loopBody790_250 : HolLoopProg 64 :=
.seq loopBody790_245 loopBody790_249

def loopBody790_251 : HolLoopProg 64 :=
.mark loopBody790_250

def loopBody790_252 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 11 (Flapjack.RegImm.imm 0#64) loopBody790_251 loopBody790_1 (Flapjack.Spt.ln)

def loopBody790_253 : HolLoopProg 64 :=
.mark loopBody790_252

def loopBody790_254 : HolLoopProg 64 :=
.seq loopBody790_253 loopBody790_1

def loopBody790_255 : HolLoopProg 64 :=
.mark loopBody790_254

def loopBody790_256 : HolLoopProg 64 :=
.seq loopBody790_27 loopBody790_255

def loopBody790_257 : HolLoopProg 64 :=
.mark loopBody790_256

def loopBody790_258 : HolLoopProg 64 :=
.seq loopBody790_243 loopBody790_257

def loopBody790_259 : HolLoopProg 64 :=
.mark loopBody790_258

def loopBody790_260 : HolLoopProg 64 :=
.seq loopBody790_241 loopBody790_259

def loopBody790_261 : HolLoopProg 64 :=
.mark loopBody790_260

def loopBody790_262 : HolLoopProg 64 :=
.seq loopBody790_239 loopBody790_261

def loopBody790_263 : HolLoopProg 64 :=
.mark loopBody790_262

def loopBody790_264 : HolLoopProg 64 :=
.seq loopBody790_237 loopBody790_263

def loopBody790_265 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 1#64)

def loopBody790_266 : HolLoopProg 64 :=
.mark loopBody790_265

def loopBody790_267 : HolLoopProg 64 :=
.seq loopBody790_266 loopBody790_249

def loopBody790_268 : HolLoopProg 64 :=
.mark loopBody790_267

def loopBody790_269 : HolLoopProg 64 :=
.seq loopBody790_264 loopBody790_268

def loopBody790_270 : HolLoopProg 64 :=
.seq loopBody790_15 loopBody790_269

def loopBody790_271 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_270

def loopBody790_272 : HolLoopProg 64 :=
.seq loopBody790_13 loopBody790_271

def loopBody790_273 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_272

def loopBody790_274 : HolLoopProg 64 :=
.seq loopBody790_11 loopBody790_273

def loopBody790_275 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_274

def loopBody790_276 : HolLoopProg 64 :=
.seq loopBody790_9 loopBody790_275

def loopBody790_277 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_276

def loopBody790_278 : HolLoopProg 64 :=
.seq loopBody790_7 loopBody790_277

def loopBody790_279 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_278

def loopBody790_280 : HolLoopProg 64 :=
.seq loopBody790_5 loopBody790_279

def loopBody790_281 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_280

def loopBody790_282 : HolLoopProg 64 :=
.seq loopBody790_3 loopBody790_281

def loopBody790_283 : HolLoopProg 64 :=
.seq loopBody790_1 loopBody790_282

def output790 : Nat × List Nat × HolLoopProg 64 :=
  (854, [0], loopBody790_283)
end InitECandidate.Proofs.FrontendStages.Loop
