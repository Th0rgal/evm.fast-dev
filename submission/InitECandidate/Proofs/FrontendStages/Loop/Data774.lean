import InitECandidate.Proofs.FrontendStages.Loop.Translate758
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody774_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody774_1 : HolLoopProg 64 :=
.mark loopBody774_0

def loopBody774_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 8#64]))

def loopBody774_3 : HolLoopProg 64 :=
.mark loopBody774_2

def loopBody774_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 1, Flapjack.HolLoopExp.const 0#64]))

def loopBody774_5 : HolLoopProg 64 :=
.mark loopBody774_4

def loopBody774_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 9#64])

def loopBody774_7 : HolLoopProg 64 :=
.mark loopBody774_6

def loopBody774_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.const 0#64)

def loopBody774_9 : HolLoopProg 64 :=
.mark loopBody774_8

def loopBody774_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 5)

def loopBody774_11 : HolLoopProg 64 :=
.mark loopBody774_10

def loopBody774_12 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 2)

def loopBody774_13 : HolLoopProg 64 :=
.mark loopBody774_12

def loopBody774_14 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 1#64)

def loopBody774_15 : HolLoopProg 64 :=
.mark loopBody774_14

def loopBody774_16 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.const 0#64)

def loopBody774_17 : HolLoopProg 64 :=
.mark loopBody774_16

def loopBody774_18 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 7 (Flapjack.RegImm.reg 8) loopBody774_15 loopBody774_17 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody774_19 : HolLoopProg 64 :=
.mark loopBody774_18

def loopBody774_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.var 7)

def loopBody774_21 : HolLoopProg 64 :=
.mark loopBody774_20

def loopBody774_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 3,
        Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 5) (Flapjack.HolLoopExp.const 3#64)]))

def loopBody774_23 : HolLoopProg 64 :=
.mark loopBody774_22

def loopBody774_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.const 9#64])

def loopBody774_25 : HolLoopProg 64 :=
.mark loopBody774_24

def loopBody774_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 0#64]))

def loopBody774_27 : HolLoopProg 64 :=
.mark loopBody774_26

def loopBody774_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 20#64)

def loopBody774_29 : HolLoopProg 64 :=
.mark loopBody774_28

def loopBody774_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 9

def loopBody774_31 : HolLoopProg 64 :=
.mark loopBody774_30

def loopBody774_32 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 176) ([9, 10, 11]) (some (9, loopBody774_31, loopBody774_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody774_33 : HolLoopProg 64 :=
.mark loopBody774_32

def loopBody774_34 : HolLoopProg 64 :=
.seq loopBody774_33 loopBody774_1

def loopBody774_35 : HolLoopProg 64 :=
.mark loopBody774_34

def loopBody774_36 : HolLoopProg 64 :=
.seq loopBody774_29 loopBody774_35

def loopBody774_37 : HolLoopProg 64 :=
.mark loopBody774_36

def loopBody774_38 : HolLoopProg 64 :=
.seq loopBody774_27 loopBody774_37

def loopBody774_39 : HolLoopProg 64 :=
.mark loopBody774_38

def loopBody774_40 : HolLoopProg 64 :=
.seq loopBody774_21 loopBody774_39

def loopBody774_41 : HolLoopProg 64 :=
.mark loopBody774_40

def loopBody774_42 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.var 8])

def loopBody774_43 : HolLoopProg 64 :=
.mark loopBody774_42

def loopBody774_44 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 9)

def loopBody774_45 : HolLoopProg 64 :=
.mark loopBody774_44

def loopBody774_46 : HolLoopProg 64 :=
.seq loopBody774_45 loopBody774_1

def loopBody774_47 : HolLoopProg 64 :=
.mark loopBody774_46

def loopBody774_48 : HolLoopProg 64 :=
.seq loopBody774_47 loopBody774_1

def loopBody774_49 : HolLoopProg 64 :=
.mark loopBody774_48

def loopBody774_50 : HolLoopProg 64 :=
.seq loopBody774_43 loopBody774_49

def loopBody774_51 : HolLoopProg 64 :=
.mark loopBody774_50

def loopBody774_52 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_51

def loopBody774_53 : HolLoopProg 64 :=
.mark loopBody774_52

def loopBody774_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.const 9#64])

def loopBody774_55 : HolLoopProg 64 :=
.mark loopBody774_54

def loopBody774_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 16#64]))

def loopBody774_57 : HolLoopProg 64 :=
.mark loopBody774_56

def loopBody774_58 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody774_59 : HolLoopProg 64 :=
.mark loopBody774_58

def loopBody774_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody774_61 : HolLoopProg 64 :=
.mark loopBody774_60

def loopBody774_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 11)

def loopBody774_63 : HolLoopProg 64 :=
.mark loopBody774_62

def loopBody774_64 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody774_65 : HolLoopProg 64 :=
.mark loopBody774_64

def loopBody774_66 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody774_67 : HolLoopProg 64 :=
.mark loopBody774_66

def loopBody774_68 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.less) 14 (Flapjack.RegImm.reg 15) loopBody774_65 loopBody774_67 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody774_69 : HolLoopProg 64 :=
.mark loopBody774_68

def loopBody774_70 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 14)

def loopBody774_71 : HolLoopProg 64 :=
.mark loopBody774_70

def loopBody774_72 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 10)

def loopBody774_73 : HolLoopProg 64 :=
.mark loopBody774_72

def loopBody774_74 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.load
        (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 8#64]),
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 12) (Flapjack.HolLoopExp.const 5#64)])

def loopBody774_75 : HolLoopProg 64 :=
.mark loopBody774_74

def loopBody774_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 32#64)

def loopBody774_77 : HolLoopProg 64 :=
.mark loopBody774_76

def loopBody774_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 13

def loopBody774_79 : HolLoopProg 64 :=
.mark loopBody774_78

def loopBody774_80 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 176) ([13, 14, 15]) (some (13, loopBody774_79, loopBody774_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody774_81 : HolLoopProg 64 :=
.mark loopBody774_80

def loopBody774_82 : HolLoopProg 64 :=
.seq loopBody774_81 loopBody774_1

def loopBody774_83 : HolLoopProg 64 :=
.mark loopBody774_82

def loopBody774_84 : HolLoopProg 64 :=
.seq loopBody774_77 loopBody774_83

def loopBody774_85 : HolLoopProg 64 :=
.mark loopBody774_84

def loopBody774_86 : HolLoopProg 64 :=
.seq loopBody774_75 loopBody774_85

def loopBody774_87 : HolLoopProg 64 :=
.mark loopBody774_86

def loopBody774_88 : HolLoopProg 64 :=
.seq loopBody774_73 loopBody774_87

def loopBody774_89 : HolLoopProg 64 :=
.mark loopBody774_88

def loopBody774_90 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 10, Flapjack.HolLoopExp.var 8])

def loopBody774_91 : HolLoopProg 64 :=
.mark loopBody774_90

def loopBody774_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 13)

def loopBody774_93 : HolLoopProg 64 :=
.mark loopBody774_92

def loopBody774_94 : HolLoopProg 64 :=
.seq loopBody774_93 loopBody774_1

def loopBody774_95 : HolLoopProg 64 :=
.mark loopBody774_94

def loopBody774_96 : HolLoopProg 64 :=
.seq loopBody774_95 loopBody774_1

def loopBody774_97 : HolLoopProg 64 :=
.mark loopBody774_96

def loopBody774_98 : HolLoopProg 64 :=
.seq loopBody774_91 loopBody774_97

def loopBody774_99 : HolLoopProg 64 :=
.mark loopBody774_98

def loopBody774_100 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_99

def loopBody774_101 : HolLoopProg 64 :=
.mark loopBody774_100

def loopBody774_102 : HolLoopProg 64 :=
.seq loopBody774_89 loopBody774_101

def loopBody774_103 : HolLoopProg 64 :=
.mark loopBody774_102

def loopBody774_104 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 12, Flapjack.HolLoopExp.const 1#64])

def loopBody774_105 : HolLoopProg 64 :=
.mark loopBody774_104

def loopBody774_106 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 13)

def loopBody774_107 : HolLoopProg 64 :=
.mark loopBody774_106

def loopBody774_108 : HolLoopProg 64 :=
.seq loopBody774_107 loopBody774_1

def loopBody774_109 : HolLoopProg 64 :=
.mark loopBody774_108

def loopBody774_110 : HolLoopProg 64 :=
.seq loopBody774_109 loopBody774_1

def loopBody774_111 : HolLoopProg 64 :=
.mark loopBody774_110

def loopBody774_112 : HolLoopProg 64 :=
.seq loopBody774_105 loopBody774_111

def loopBody774_113 : HolLoopProg 64 :=
.mark loopBody774_112

def loopBody774_114 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_113

def loopBody774_115 : HolLoopProg 64 :=
.mark loopBody774_114

def loopBody774_116 : HolLoopProg 64 :=
.seq loopBody774_103 loopBody774_115

def loopBody774_117 : HolLoopProg 64 :=
.mark loopBody774_116

def loopBody774_118 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody774_119 : HolLoopProg 64 :=
.mark loopBody774_118

def loopBody774_120 : HolLoopProg 64 :=
.seq loopBody774_117 loopBody774_119

def loopBody774_121 : HolLoopProg 64 :=
.mark loopBody774_120

def loopBody774_122 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody774_123 : HolLoopProg 64 :=
.mark loopBody774_122

def loopBody774_124 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.RegImm.imm 0#64) loopBody774_121 loopBody774_123 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody774_125 : HolLoopProg 64 :=
.mark loopBody774_124

def loopBody774_126 : HolLoopProg 64 :=
.seq loopBody774_125 loopBody774_1

def loopBody774_127 : HolLoopProg 64 :=
.mark loopBody774_126

def loopBody774_128 : HolLoopProg 64 :=
.seq loopBody774_71 loopBody774_127

def loopBody774_129 : HolLoopProg 64 :=
.mark loopBody774_128

def loopBody774_130 : HolLoopProg 64 :=
.seq loopBody774_69 loopBody774_129

def loopBody774_131 : HolLoopProg 64 :=
.mark loopBody774_130

def loopBody774_132 : HolLoopProg 64 :=
.seq loopBody774_63 loopBody774_131

def loopBody774_133 : HolLoopProg 64 :=
.mark loopBody774_132

def loopBody774_134 : HolLoopProg 64 :=
.seq loopBody774_61 loopBody774_133

def loopBody774_135 : HolLoopProg 64 :=
.mark loopBody774_134

def loopBody774_136 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody774_135 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))

def loopBody774_137 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 9)

def loopBody774_138 : HolLoopProg 64 :=
.mark loopBody774_137

def loopBody774_139 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 10)

def loopBody774_140 : HolLoopProg 64 :=
.mark loopBody774_139

def loopBody774_141 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))) (some 836) ([13, 14]) (some (13, loopBody774_79, loopBody774_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit)))))

def loopBody774_142 : HolLoopProg 64 :=
.mark loopBody774_141

def loopBody774_143 : HolLoopProg 64 :=
.seq loopBody774_142 loopBody774_1

def loopBody774_144 : HolLoopProg 64 :=
.mark loopBody774_143

def loopBody774_145 : HolLoopProg 64 :=
.seq loopBody774_140 loopBody774_144

def loopBody774_146 : HolLoopProg 64 :=
.mark loopBody774_145

def loopBody774_147 : HolLoopProg 64 :=
.seq loopBody774_138 loopBody774_146

def loopBody774_148 : HolLoopProg 64 :=
.mark loopBody774_147

def loopBody774_149 : HolLoopProg 64 :=
.seq loopBody774_136 loopBody774_148

def loopBody774_150 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.var 8])

def loopBody774_151 : HolLoopProg 64 :=
.mark loopBody774_150

def loopBody774_152 : HolLoopProg 64 :=
.seq loopBody774_151 loopBody774_1

def loopBody774_153 : HolLoopProg 64 :=
.mark loopBody774_152

def loopBody774_154 : HolLoopProg 64 :=
.seq loopBody774_153 loopBody774_1

def loopBody774_155 : HolLoopProg 64 :=
.mark loopBody774_154

def loopBody774_156 : HolLoopProg 64 :=
.seq loopBody774_149 loopBody774_155

def loopBody774_157 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 7)

def loopBody774_158 : HolLoopProg 64 :=
.mark loopBody774_157

def loopBody774_159 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 24#64]))

def loopBody774_160 : HolLoopProg 64 :=
.mark loopBody774_159

def loopBody774_161 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 6, Flapjack.HolLoopExp.const 32#64]))

def loopBody774_162 : HolLoopProg 64 :=
.mark loopBody774_161

def loopBody774_163 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 176) ([13, 14, 15]) (some (13, loopBody774_79, loopBody774_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody774_164 : HolLoopProg 64 :=
.mark loopBody774_163

def loopBody774_165 : HolLoopProg 64 :=
.seq loopBody774_164 loopBody774_1

def loopBody774_166 : HolLoopProg 64 :=
.mark loopBody774_165

def loopBody774_167 : HolLoopProg 64 :=
.seq loopBody774_162 loopBody774_166

def loopBody774_168 : HolLoopProg 64 :=
.mark loopBody774_167

def loopBody774_169 : HolLoopProg 64 :=
.seq loopBody774_160 loopBody774_168

def loopBody774_170 : HolLoopProg 64 :=
.mark loopBody774_169

def loopBody774_171 : HolLoopProg 64 :=
.seq loopBody774_158 loopBody774_170

def loopBody774_172 : HolLoopProg 64 :=
.mark loopBody774_171

def loopBody774_173 : HolLoopProg 64 :=
.seq loopBody774_156 loopBody774_172

def loopBody774_174 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 7, Flapjack.HolLoopExp.var 8])

def loopBody774_175 : HolLoopProg 64 :=
.mark loopBody774_174

def loopBody774_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 13)

def loopBody774_177 : HolLoopProg 64 :=
.mark loopBody774_176

def loopBody774_178 : HolLoopProg 64 :=
.seq loopBody774_177 loopBody774_1

def loopBody774_179 : HolLoopProg 64 :=
.mark loopBody774_178

def loopBody774_180 : HolLoopProg 64 :=
.seq loopBody774_179 loopBody774_1

def loopBody774_181 : HolLoopProg 64 :=
.mark loopBody774_180

def loopBody774_182 : HolLoopProg 64 :=
.seq loopBody774_175 loopBody774_181

def loopBody774_183 : HolLoopProg 64 :=
.mark loopBody774_182

def loopBody774_184 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_183

def loopBody774_185 : HolLoopProg 64 :=
.mark loopBody774_184

def loopBody774_186 : HolLoopProg 64 :=
.seq loopBody774_173 loopBody774_185

def loopBody774_187 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 4)

def loopBody774_188 : HolLoopProg 64 :=
.mark loopBody774_187

def loopBody774_189 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 7)

def loopBody774_190 : HolLoopProg 64 :=
.mark loopBody774_189

def loopBody774_191 : HolLoopProg 64 :=
.call (some
  ([8],
    Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 836) ([13, 14]) (some (13, loopBody774_79, loopBody774_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody774_192 : HolLoopProg 64 :=
.mark loopBody774_191

def loopBody774_193 : HolLoopProg 64 :=
.seq loopBody774_192 loopBody774_1

def loopBody774_194 : HolLoopProg 64 :=
.mark loopBody774_193

def loopBody774_195 : HolLoopProg 64 :=
.seq loopBody774_190 loopBody774_194

def loopBody774_196 : HolLoopProg 64 :=
.mark loopBody774_195

def loopBody774_197 : HolLoopProg 64 :=
.seq loopBody774_188 loopBody774_196

def loopBody774_198 : HolLoopProg 64 :=
.mark loopBody774_197

def loopBody774_199 : HolLoopProg 64 :=
.seq loopBody774_186 loopBody774_198

def loopBody774_200 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 4, Flapjack.HolLoopExp.var 8])

def loopBody774_201 : HolLoopProg 64 :=
.mark loopBody774_200

def loopBody774_202 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 4 (Flapjack.HolLoopExp.var 13)

def loopBody774_203 : HolLoopProg 64 :=
.mark loopBody774_202

def loopBody774_204 : HolLoopProg 64 :=
.seq loopBody774_203 loopBody774_1

def loopBody774_205 : HolLoopProg 64 :=
.mark loopBody774_204

def loopBody774_206 : HolLoopProg 64 :=
.seq loopBody774_205 loopBody774_1

def loopBody774_207 : HolLoopProg 64 :=
.mark loopBody774_206

def loopBody774_208 : HolLoopProg 64 :=
.seq loopBody774_201 loopBody774_207

def loopBody774_209 : HolLoopProg 64 :=
.mark loopBody774_208

def loopBody774_210 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_209

def loopBody774_211 : HolLoopProg 64 :=
.mark loopBody774_210

def loopBody774_212 : HolLoopProg 64 :=
.seq loopBody774_199 loopBody774_211

def loopBody774_213 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.const 1#64])

def loopBody774_214 : HolLoopProg 64 :=
.mark loopBody774_213

def loopBody774_215 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 13)

def loopBody774_216 : HolLoopProg 64 :=
.mark loopBody774_215

def loopBody774_217 : HolLoopProg 64 :=
.seq loopBody774_216 loopBody774_1

def loopBody774_218 : HolLoopProg 64 :=
.mark loopBody774_217

def loopBody774_219 : HolLoopProg 64 :=
.seq loopBody774_218 loopBody774_1

def loopBody774_220 : HolLoopProg 64 :=
.mark loopBody774_219

def loopBody774_221 : HolLoopProg 64 :=
.seq loopBody774_214 loopBody774_220

def loopBody774_222 : HolLoopProg 64 :=
.mark loopBody774_221

def loopBody774_223 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_222

def loopBody774_224 : HolLoopProg 64 :=
.mark loopBody774_223

def loopBody774_225 : HolLoopProg 64 :=
.seq loopBody774_212 loopBody774_224

def loopBody774_226 : HolLoopProg 64 :=
.seq loopBody774_59 loopBody774_225

def loopBody774_227 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_226

def loopBody774_228 : HolLoopProg 64 :=
.seq loopBody774_57 loopBody774_227

def loopBody774_229 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_228

def loopBody774_230 : HolLoopProg 64 :=
.seq loopBody774_55 loopBody774_229

def loopBody774_231 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_230

def loopBody774_232 : HolLoopProg 64 :=
.seq loopBody774_21 loopBody774_231

def loopBody774_233 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_232

def loopBody774_234 : HolLoopProg 64 :=
.seq loopBody774_53 loopBody774_233

def loopBody774_235 : HolLoopProg 64 :=
.seq loopBody774_41 loopBody774_234

def loopBody774_236 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_235

def loopBody774_237 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_236

def loopBody774_238 : HolLoopProg 64 :=
.seq loopBody774_25 loopBody774_237

def loopBody774_239 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_238

def loopBody774_240 : HolLoopProg 64 :=
.seq loopBody774_23 loopBody774_239

def loopBody774_241 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_240

def loopBody774_242 : HolLoopProg 64 :=
.seq loopBody774_241 loopBody774_119

def loopBody774_243 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 9 (Flapjack.RegImm.imm 0#64) loopBody774_242 loopBody774_123 (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))

def loopBody774_244 : HolLoopProg 64 :=
.seq loopBody774_243 loopBody774_1

def loopBody774_245 : HolLoopProg 64 :=
.seq loopBody774_21 loopBody774_244

def loopBody774_246 : HolLoopProg 64 :=
.seq loopBody774_19 loopBody774_245

def loopBody774_247 : HolLoopProg 64 :=
.seq loopBody774_13 loopBody774_246

def loopBody774_248 : HolLoopProg 64 :=
.seq loopBody774_11 loopBody774_247

def loopBody774_249 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))) loopBody774_248 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)

def loopBody774_250 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 0)

def loopBody774_251 : HolLoopProg 64 :=
.mark loopBody774_250

def loopBody774_252 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 4)

def loopBody774_253 : HolLoopProg 64 :=
.mark loopBody774_252

def loopBody774_254 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 7

def loopBody774_255 : HolLoopProg 64 :=
.mark loopBody774_254

def loopBody774_256 : HolLoopProg 64 :=
.call (some ([6], Flapjack.Spt.ln)) (some 836) ([7, 8]) (some (7, loopBody774_255, loopBody774_1, (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))

def loopBody774_257 : HolLoopProg 64 :=
.mark loopBody774_256

def loopBody774_258 : HolLoopProg 64 :=
.seq loopBody774_257 loopBody774_1

def loopBody774_259 : HolLoopProg 64 :=
.mark loopBody774_258

def loopBody774_260 : HolLoopProg 64 :=
.seq loopBody774_253 loopBody774_259

def loopBody774_261 : HolLoopProg 64 :=
.mark loopBody774_260

def loopBody774_262 : HolLoopProg 64 :=
.seq loopBody774_251 loopBody774_261

def loopBody774_263 : HolLoopProg 64 :=
.mark loopBody774_262

def loopBody774_264 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 7 (Flapjack.HolLoopExp.var 6)

def loopBody774_265 : HolLoopProg 64 :=
.mark loopBody774_264

def loopBody774_266 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [7]

def loopBody774_267 : HolLoopProg 64 :=
.mark loopBody774_266

def loopBody774_268 : HolLoopProg 64 :=
.seq loopBody774_267 loopBody774_1

def loopBody774_269 : HolLoopProg 64 :=
.mark loopBody774_268

def loopBody774_270 : HolLoopProg 64 :=
.seq loopBody774_265 loopBody774_269

def loopBody774_271 : HolLoopProg 64 :=
.mark loopBody774_270

def loopBody774_272 : HolLoopProg 64 :=
.seq loopBody774_263 loopBody774_271

def loopBody774_273 : HolLoopProg 64 :=
.mark loopBody774_272

def loopBody774_274 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_273

def loopBody774_275 : HolLoopProg 64 :=
.mark loopBody774_274

def loopBody774_276 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_275

def loopBody774_277 : HolLoopProg 64 :=
.mark loopBody774_276

def loopBody774_278 : HolLoopProg 64 :=
.seq loopBody774_249 loopBody774_277

def loopBody774_279 : HolLoopProg 64 :=
.seq loopBody774_9 loopBody774_278

def loopBody774_280 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_279

def loopBody774_281 : HolLoopProg 64 :=
.seq loopBody774_7 loopBody774_280

def loopBody774_282 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_281

def loopBody774_283 : HolLoopProg 64 :=
.seq loopBody774_5 loopBody774_282

def loopBody774_284 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_283

def loopBody774_285 : HolLoopProg 64 :=
.seq loopBody774_3 loopBody774_284

def loopBody774_286 : HolLoopProg 64 :=
.seq loopBody774_1 loopBody774_285

def output774 : Nat × List Nat × HolLoopProg 64 :=
  (838, [0, 1], loopBody774_286)
end InitECandidate.Proofs.FrontendStages.Loop
