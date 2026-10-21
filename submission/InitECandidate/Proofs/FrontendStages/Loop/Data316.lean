import InitECandidate.Proofs.FrontendStages.Loop.Translate300
import InitECandidate.Proofs.FrontendStages.Loop.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Loop
def loopBody316_0 : HolLoopProg 64 :=
Flapjack.HolLoopProg.skip

def loopBody316_1 : HolLoopProg 64 :=
.mark loopBody316_0

def loopBody316_2 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 2
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 192#64]))

def loopBody316_3 : HolLoopProg 64 :=
.mark loopBody316_2

def loopBody316_4 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 3
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 200#64]))

def loopBody316_5 : HolLoopProg 64 :=
.mark loopBody316_4

def loopBody316_6 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5 (Flapjack.HolLoopExp.var 2)

def loopBody316_7 : HolLoopProg 64 :=
.mark loopBody316_6

def loopBody316_8 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6 (Flapjack.HolLoopExp.var 3)

def loopBody316_9 : HolLoopProg 64 :=
.mark loopBody316_8

def loopBody316_10 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 5

def loopBody316_11 : HolLoopProg 64 :=
.mark loopBody316_10

def loopBody316_12 : HolLoopProg 64 :=
.call (some
  ([4],
    Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 379) ([5, 6]) (some (5, loopBody316_11, loopBody316_1, (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))

def loopBody316_13 : HolLoopProg 64 :=
.mark loopBody316_12

def loopBody316_14 : HolLoopProg 64 :=
.seq loopBody316_13 loopBody316_1

def loopBody316_15 : HolLoopProg 64 :=
.mark loopBody316_14

def loopBody316_16 : HolLoopProg 64 :=
.seq loopBody316_9 loopBody316_15

def loopBody316_17 : HolLoopProg 64 :=
.mark loopBody316_16

def loopBody316_18 : HolLoopProg 64 :=
.seq loopBody316_7 loopBody316_17

def loopBody316_19 : HolLoopProg 64 :=
.mark loopBody316_18

def loopBody316_20 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 5
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 4) (Flapjack.HolLoopExp.const 2#64))

def loopBody316_21 : HolLoopProg 64 :=
.mark loopBody316_20

def loopBody316_22 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 6
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 152#64]))

def loopBody316_23 : HolLoopProg 64 :=
.mark loopBody316_22

def loopBody316_24 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64]))

def loopBody316_25 : HolLoopProg 64 :=
.mark loopBody316_24

def loopBody316_26 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64],
        Flapjack.HolLoopExp.const 8#64]))

def loopBody316_27 : HolLoopProg 64 :=
.mark loopBody316_26

def loopBody316_28 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64],
        Flapjack.HolLoopExp.const 16#64]))

def loopBody316_29 : HolLoopProg 64 :=
.mark loopBody316_28

def loopBody316_30 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 160#64],
        Flapjack.HolLoopExp.const 24#64]))

def loopBody316_31 : HolLoopProg 64 :=
.mark loopBody316_30

def loopBody316_32 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 8

def loopBody316_33 : HolLoopProg 64 :=
.mark loopBody316_32

def loopBody316_34 : HolLoopProg 64 :=
.call (some
  ([7],
    Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) (some 102) ([8, 9, 10, 11]) (some (8, loopBody316_33, loopBody316_1, (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody316_35 : HolLoopProg 64 :=
.mark loopBody316_34

def loopBody316_36 : HolLoopProg 64 :=
.seq loopBody316_35 loopBody316_1

def loopBody316_37 : HolLoopProg 64 :=
.mark loopBody316_36

def loopBody316_38 : HolLoopProg 64 :=
.seq loopBody316_31 loopBody316_37

def loopBody316_39 : HolLoopProg 64 :=
.mark loopBody316_38

def loopBody316_40 : HolLoopProg 64 :=
.seq loopBody316_29 loopBody316_39

def loopBody316_41 : HolLoopProg 64 :=
.mark loopBody316_40

def loopBody316_42 : HolLoopProg 64 :=
.seq loopBody316_27 loopBody316_41

def loopBody316_43 : HolLoopProg 64 :=
.mark loopBody316_42

def loopBody316_44 : HolLoopProg 64 :=
.seq loopBody316_25 loopBody316_43

def loopBody316_45 : HolLoopProg 64 :=
.mark loopBody316_44

def loopBody316_46 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_47 : HolLoopProg 64 :=
.mark loopBody316_46

def loopBody316_48 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_49 : HolLoopProg 64 :=
.mark loopBody316_48

def loopBody316_50 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 6)

def loopBody316_51 : HolLoopProg 64 :=
.mark loopBody316_50

def loopBody316_52 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_53 : HolLoopProg 64 :=
.mark loopBody316_52

def loopBody316_54 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 1#64)

def loopBody316_55 : HolLoopProg 64 :=
.mark loopBody316_54

def loopBody316_56 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_57 : HolLoopProg 64 :=
.mark loopBody316_56

def loopBody316_58 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 11 (Flapjack.RegImm.reg 12) loopBody316_55 loopBody316_57 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody316_59 : HolLoopProg 64 :=
.mark loopBody316_58

def loopBody316_60 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.var 11)

def loopBody316_61 : HolLoopProg 64 :=
.mark loopBody316_60

def loopBody316_62 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 12000#64)

def loopBody316_63 : HolLoopProg 64 :=
.mark loopBody316_62

def loopBody316_64 : HolLoopProg 64 :=
.seq loopBody316_63 loopBody316_1

def loopBody316_65 : HolLoopProg 64 :=
.mark loopBody316_64

def loopBody316_66 : HolLoopProg 64 :=
.seq loopBody316_65 loopBody316_1

def loopBody316_67 : HolLoopProg 64 :=
.mark loopBody316_66

def loopBody316_68 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 9
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl
    (Flapjack.HolLoopExp.shift Flapjack.Shift.lsr
      (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 3, Flapjack.HolLoopExp.const 31#64])
      (Flapjack.HolLoopExp.const 5#64))
    (Flapjack.HolLoopExp.const 1#64))

def loopBody316_69 : HolLoopProg 64 :=
.mark loopBody316_68

def loopBody316_70 : HolLoopProg 64 :=
.seq loopBody316_69 loopBody316_1

def loopBody316_71 : HolLoopProg 64 :=
.mark loopBody316_70

def loopBody316_72 : HolLoopProg 64 :=
.seq loopBody316_71 loopBody316_1

def loopBody316_73 : HolLoopProg 64 :=
.mark loopBody316_72

def loopBody316_74 : HolLoopProg 64 :=
.seq loopBody316_67 loopBody316_73

def loopBody316_75 : HolLoopProg 64 :=
.mark loopBody316_74

def loopBody316_76 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 1)

def loopBody316_77 : HolLoopProg 64 :=
.mark loopBody316_76

def loopBody316_78 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 20#64)

def loopBody316_79 : HolLoopProg 64 :=
.mark loopBody316_78

def loopBody316_80 : HolLoopProg 64 :=
Flapjack.HolLoopProg.raise 11

def loopBody316_81 : HolLoopProg 64 :=
.mark loopBody316_80

def loopBody316_82 : HolLoopProg 64 :=
.call (some
  ([10],
    Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))) (some 79) ([11, 12, 13]) (some (11, loopBody316_81, loopBody316_1, (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))

def loopBody316_83 : HolLoopProg 64 :=
.mark loopBody316_82

def loopBody316_84 : HolLoopProg 64 :=
.seq loopBody316_83 loopBody316_1

def loopBody316_85 : HolLoopProg 64 :=
.mark loopBody316_84

def loopBody316_86 : HolLoopProg 64 :=
.seq loopBody316_79 loopBody316_85

def loopBody316_87 : HolLoopProg 64 :=
.mark loopBody316_86

def loopBody316_88 : HolLoopProg 64 :=
.seq loopBody316_77 loopBody316_87

def loopBody316_89 : HolLoopProg 64 :=
.mark loopBody316_88

def loopBody316_90 : HolLoopProg 64 :=
.seq loopBody316_51 loopBody316_89

def loopBody316_91 : HolLoopProg 64 :=
.mark loopBody316_90

def loopBody316_92 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 10)

def loopBody316_93 : HolLoopProg 64 :=
.mark loopBody316_92

def loopBody316_94 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_95 : HolLoopProg 64 :=
.mark loopBody316_94

def loopBody316_96 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.const 1#64)

def loopBody316_97 : HolLoopProg 64 :=
.mark loopBody316_96

def loopBody316_98 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.RegImm.reg 13) loopBody316_97 loopBody316_53 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody316_99 : HolLoopProg 64 :=
.mark loopBody316_98

def loopBody316_100 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 12)

def loopBody316_101 : HolLoopProg 64 :=
.mark loopBody316_100

def loopBody316_102 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.const 3000#64)

def loopBody316_103 : HolLoopProg 64 :=
.mark loopBody316_102

def loopBody316_104 : HolLoopProg 64 :=
.seq loopBody316_103 loopBody316_1

def loopBody316_105 : HolLoopProg 64 :=
.mark loopBody316_104

def loopBody316_106 : HolLoopProg 64 :=
.seq loopBody316_105 loopBody316_1

def loopBody316_107 : HolLoopProg 64 :=
.mark loopBody316_106

def loopBody316_108 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 7)

def loopBody316_109 : HolLoopProg 64 :=
.mark loopBody316_108

def loopBody316_110 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 8, Flapjack.HolLoopExp.const 6000#64])

def loopBody316_111 : HolLoopProg 64 :=
.mark loopBody316_110

def loopBody316_112 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 8 (Flapjack.HolLoopExp.var 11)

def loopBody316_113 : HolLoopProg 64 :=
.mark loopBody316_112

def loopBody316_114 : HolLoopProg 64 :=
.seq loopBody316_113 loopBody316_1

def loopBody316_115 : HolLoopProg 64 :=
.mark loopBody316_114

def loopBody316_116 : HolLoopProg 64 :=
.seq loopBody316_115 loopBody316_1

def loopBody316_117 : HolLoopProg 64 :=
.mark loopBody316_116

def loopBody316_118 : HolLoopProg 64 :=
.seq loopBody316_111 loopBody316_117

def loopBody316_119 : HolLoopProg 64 :=
.mark loopBody316_118

def loopBody316_120 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_119

def loopBody316_121 : HolLoopProg 64 :=
.mark loopBody316_120

def loopBody316_122 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody316_121 loopBody316_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody316_123 : HolLoopProg 64 :=
.mark loopBody316_122

def loopBody316_124 : HolLoopProg 64 :=
.seq loopBody316_123 loopBody316_1

def loopBody316_125 : HolLoopProg 64 :=
.mark loopBody316_124

def loopBody316_126 : HolLoopProg 64 :=
.seq loopBody316_101 loopBody316_125

def loopBody316_127 : HolLoopProg 64 :=
.mark loopBody316_126

def loopBody316_128 : HolLoopProg 64 :=
.seq loopBody316_99 loopBody316_127

def loopBody316_129 : HolLoopProg 64 :=
.mark loopBody316_128

def loopBody316_130 : HolLoopProg 64 :=
.seq loopBody316_95 loopBody316_129

def loopBody316_131 : HolLoopProg 64 :=
.mark loopBody316_130

def loopBody316_132 : HolLoopProg 64 :=
.seq loopBody316_109 loopBody316_131

def loopBody316_133 : HolLoopProg 64 :=
.mark loopBody316_132

def loopBody316_134 : HolLoopProg 64 :=
.seq loopBody316_107 loopBody316_133

def loopBody316_135 : HolLoopProg 64 :=
.mark loopBody316_134

def loopBody316_136 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.RegImm.imm 0#64) loopBody316_135 loopBody316_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody316_137 : HolLoopProg 64 :=
.mark loopBody316_136

def loopBody316_138 : HolLoopProg 64 :=
.seq loopBody316_137 loopBody316_1

def loopBody316_139 : HolLoopProg 64 :=
.mark loopBody316_138

def loopBody316_140 : HolLoopProg 64 :=
.seq loopBody316_101 loopBody316_139

def loopBody316_141 : HolLoopProg 64 :=
.mark loopBody316_140

def loopBody316_142 : HolLoopProg 64 :=
.seq loopBody316_99 loopBody316_141

def loopBody316_143 : HolLoopProg 64 :=
.mark loopBody316_142

def loopBody316_144 : HolLoopProg 64 :=
.seq loopBody316_95 loopBody316_143

def loopBody316_145 : HolLoopProg 64 :=
.mark loopBody316_144

def loopBody316_146 : HolLoopProg 64 :=
.seq loopBody316_93 loopBody316_145

def loopBody316_147 : HolLoopProg 64 :=
.mark loopBody316_146

def loopBody316_148 : HolLoopProg 64 :=
.seq loopBody316_91 loopBody316_147

def loopBody316_149 : HolLoopProg 64 :=
.mark loopBody316_148

def loopBody316_150 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_149

def loopBody316_151 : HolLoopProg 64 :=
.mark loopBody316_150

def loopBody316_152 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_151

def loopBody316_153 : HolLoopProg 64 :=
.mark loopBody316_152

def loopBody316_154 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.imm 0#64) loopBody316_75 loopBody316_153 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody316_155 : HolLoopProg 64 :=
.mark loopBody316_154

def loopBody316_156 : HolLoopProg 64 :=
.seq loopBody316_155 loopBody316_1

def loopBody316_157 : HolLoopProg 64 :=
.mark loopBody316_156

def loopBody316_158 : HolLoopProg 64 :=
.seq loopBody316_61 loopBody316_157

def loopBody316_159 : HolLoopProg 64 :=
.mark loopBody316_158

def loopBody316_160 : HolLoopProg 64 :=
.seq loopBody316_59 loopBody316_159

def loopBody316_161 : HolLoopProg 64 :=
.mark loopBody316_160

def loopBody316_162 : HolLoopProg 64 :=
.seq loopBody316_53 loopBody316_161

def loopBody316_163 : HolLoopProg 64 :=
.mark loopBody316_162

def loopBody316_164 : HolLoopProg 64 :=
.seq loopBody316_51 loopBody316_163

def loopBody316_165 : HolLoopProg 64 :=
.mark loopBody316_164

def loopBody316_166 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_167 : HolLoopProg 64 :=
.mark loopBody316_166

def loopBody316_168 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody316_169 : HolLoopProg 64 :=
.mark loopBody316_168

def loopBody316_170 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_171 : HolLoopProg 64 :=
.mark loopBody316_170

def loopBody316_172 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13 (Flapjack.HolLoopExp.const 1#64)

def loopBody316_173 : HolLoopProg 64 :=
.mark loopBody316_172

def loopBody316_174 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 13 (Flapjack.RegImm.reg 14) loopBody316_173 loopBody316_95 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody316_175 : HolLoopProg 64 :=
.mark loopBody316_174

def loopBody316_176 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 13)

def loopBody316_177 : HolLoopProg 64 :=
.mark loopBody316_176

def loopBody316_178 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 208#64]))

def loopBody316_179 : HolLoopProg 64 :=
.mark loopBody316_178

def loopBody316_180 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 216#64]))

def loopBody316_181 : HolLoopProg 64 :=
.mark loopBody316_180

def loopBody316_182 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.var 14)

def loopBody316_183 : HolLoopProg 64 :=
.mark loopBody316_182

def loopBody316_184 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17 (Flapjack.HolLoopExp.var 13)

def loopBody316_185 : HolLoopProg 64 :=
.mark loopBody316_184

def loopBody316_186 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 1#64)

def loopBody316_187 : HolLoopProg 64 :=
.mark loopBody316_186

def loopBody316_188 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_189 : HolLoopProg 64 :=
.mark loopBody316_188

def loopBody316_190 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.RegImm.reg 17) loopBody316_187 loopBody316_189 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody316_191 : HolLoopProg 64 :=
.mark loopBody316_190

def loopBody316_192 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18 (Flapjack.HolLoopExp.var 16)

def loopBody316_193 : HolLoopProg 64 :=
.mark loopBody316_192

def loopBody316_194 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.var 14)

def loopBody316_195 : HolLoopProg 64 :=
.mark loopBody316_194

def loopBody316_196 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16 (Flapjack.HolLoopExp.const 24#64)

def loopBody316_197 : HolLoopProg 64 :=
.mark loopBody316_196

def loopBody316_198 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 17 17 15 16)

def loopBody316_199 : HolLoopProg 64 :=
.mark loopBody316_198

def loopBody316_200 : HolLoopProg 64 :=
.seq loopBody316_199 loopBody316_1

def loopBody316_201 : HolLoopProg 64 :=
.mark loopBody316_200

def loopBody316_202 : HolLoopProg 64 :=
.seq loopBody316_197 loopBody316_201

def loopBody316_203 : HolLoopProg 64 :=
.mark loopBody316_202

def loopBody316_204 : HolLoopProg 64 :=
.seq loopBody316_195 loopBody316_203

def loopBody316_205 : HolLoopProg 64 :=
.mark loopBody316_204

def loopBody316_206 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 18
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add
      [Flapjack.HolLoopExp.var 12, Flapjack.HolLoopExp.var 17, Flapjack.HolLoopExp.const 16#64]))

def loopBody316_207 : HolLoopProg 64 :=
.mark loopBody316_206

def loopBody316_208 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.var 18)

def loopBody316_209 : HolLoopProg 64 :=
.mark loopBody316_208

def loopBody316_210 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20
  (Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 2100#64, Flapjack.HolLoopExp.const 100#64])

def loopBody316_211 : HolLoopProg 64 :=
.mark loopBody316_210

def loopBody316_212 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 21 21 19 20)

def loopBody316_213 : HolLoopProg 64 :=
.mark loopBody316_212

def loopBody316_214 : HolLoopProg 64 :=
.seq loopBody316_213 loopBody316_1

def loopBody316_215 : HolLoopProg 64 :=
.mark loopBody316_214

def loopBody316_216 : HolLoopProg 64 :=
.seq loopBody316_211 loopBody316_215

def loopBody316_217 : HolLoopProg 64 :=
.mark loopBody316_216

def loopBody316_218 : HolLoopProg 64 :=
.seq loopBody316_209 loopBody316_217

def loopBody316_219 : HolLoopProg 64 :=
.mark loopBody316_218

def loopBody316_220 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 22
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 10,
      Flapjack.HolLoopExp.op Flapjack.BinOp.sub [Flapjack.HolLoopExp.const 3000#64, Flapjack.HolLoopExp.const 100#64],
      Flapjack.HolLoopExp.var 21])

def loopBody316_221 : HolLoopProg 64 :=
.mark loopBody316_220

def loopBody316_222 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 22)

def loopBody316_223 : HolLoopProg 64 :=
.mark loopBody316_222

def loopBody316_224 : HolLoopProg 64 :=
.seq loopBody316_223 loopBody316_1

def loopBody316_225 : HolLoopProg 64 :=
.mark loopBody316_224

def loopBody316_226 : HolLoopProg 64 :=
.seq loopBody316_225 loopBody316_1

def loopBody316_227 : HolLoopProg 64 :=
.mark loopBody316_226

def loopBody316_228 : HolLoopProg 64 :=
.seq loopBody316_221 loopBody316_227

def loopBody316_229 : HolLoopProg 64 :=
.mark loopBody316_228

def loopBody316_230 : HolLoopProg 64 :=
.seq loopBody316_219 loopBody316_229

def loopBody316_231 : HolLoopProg 64 :=
.mark loopBody316_230

def loopBody316_232 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 11, Flapjack.HolLoopExp.const 80#64,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 18) (Flapjack.HolLoopExp.const 7#64)])

def loopBody316_233 : HolLoopProg 64 :=
.mark loopBody316_232

def loopBody316_234 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 11 (Flapjack.HolLoopExp.var 19)

def loopBody316_235 : HolLoopProg 64 :=
.mark loopBody316_234

def loopBody316_236 : HolLoopProg 64 :=
.seq loopBody316_235 loopBody316_1

def loopBody316_237 : HolLoopProg 64 :=
.mark loopBody316_236

def loopBody316_238 : HolLoopProg 64 :=
.seq loopBody316_237 loopBody316_1

def loopBody316_239 : HolLoopProg 64 :=
.mark loopBody316_238

def loopBody316_240 : HolLoopProg 64 :=
.seq loopBody316_233 loopBody316_239

def loopBody316_241 : HolLoopProg 64 :=
.mark loopBody316_240

def loopBody316_242 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_241

def loopBody316_243 : HolLoopProg 64 :=
.mark loopBody316_242

def loopBody316_244 : HolLoopProg 64 :=
.seq loopBody316_231 loopBody316_243

def loopBody316_245 : HolLoopProg 64 :=
.mark loopBody316_244

def loopBody316_246 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 14, Flapjack.HolLoopExp.const 1#64])

def loopBody316_247 : HolLoopProg 64 :=
.mark loopBody316_246

def loopBody316_248 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.var 19)

def loopBody316_249 : HolLoopProg 64 :=
.mark loopBody316_248

def loopBody316_250 : HolLoopProg 64 :=
.seq loopBody316_249 loopBody316_1

def loopBody316_251 : HolLoopProg 64 :=
.mark loopBody316_250

def loopBody316_252 : HolLoopProg 64 :=
.seq loopBody316_251 loopBody316_1

def loopBody316_253 : HolLoopProg 64 :=
.mark loopBody316_252

def loopBody316_254 : HolLoopProg 64 :=
.seq loopBody316_247 loopBody316_253

def loopBody316_255 : HolLoopProg 64 :=
.mark loopBody316_254

def loopBody316_256 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_255

def loopBody316_257 : HolLoopProg 64 :=
.mark loopBody316_256

def loopBody316_258 : HolLoopProg 64 :=
.seq loopBody316_245 loopBody316_257

def loopBody316_259 : HolLoopProg 64 :=
.mark loopBody316_258

def loopBody316_260 : HolLoopProg 64 :=
.seq loopBody316_207 loopBody316_259

def loopBody316_261 : HolLoopProg 64 :=
.mark loopBody316_260

def loopBody316_262 : HolLoopProg 64 :=
.seq loopBody316_205 loopBody316_261

def loopBody316_263 : HolLoopProg 64 :=
.mark loopBody316_262

def loopBody316_264 : HolLoopProg 64 :=
Flapjack.HolLoopProg.continue 0

def loopBody316_265 : HolLoopProg 64 :=
.mark loopBody316_264

def loopBody316_266 : HolLoopProg 64 :=
.seq loopBody316_263 loopBody316_265

def loopBody316_267 : HolLoopProg 64 :=
.mark loopBody316_266

def loopBody316_268 : HolLoopProg 64 :=
Flapjack.HolLoopProg.break 0

def loopBody316_269 : HolLoopProg 64 :=
.mark loopBody316_268

def loopBody316_270 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.RegImm.imm 0#64) loopBody316_267 loopBody316_269 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))

def loopBody316_271 : HolLoopProg 64 :=
.mark loopBody316_270

def loopBody316_272 : HolLoopProg 64 :=
.seq loopBody316_271 loopBody316_1

def loopBody316_273 : HolLoopProg 64 :=
.mark loopBody316_272

def loopBody316_274 : HolLoopProg 64 :=
.seq loopBody316_193 loopBody316_273

def loopBody316_275 : HolLoopProg 64 :=
.mark loopBody316_274

def loopBody316_276 : HolLoopProg 64 :=
.seq loopBody316_191 loopBody316_275

def loopBody316_277 : HolLoopProg 64 :=
.mark loopBody316_276

def loopBody316_278 : HolLoopProg 64 :=
.seq loopBody316_185 loopBody316_277

def loopBody316_279 : HolLoopProg 64 :=
.mark loopBody316_278

def loopBody316_280 : HolLoopProg 64 :=
.seq loopBody316_183 loopBody316_279

def loopBody316_281 : HolLoopProg 64 :=
.mark loopBody316_280

def loopBody316_282 : HolLoopProg 64 :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))) loopBody316_281 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody316_283 : HolLoopProg 64 :=
.seq loopBody316_171 loopBody316_282

def loopBody316_284 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_283

def loopBody316_285 : HolLoopProg 64 :=
.seq loopBody316_181 loopBody316_284

def loopBody316_286 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_285

def loopBody316_287 : HolLoopProg 64 :=
.seq loopBody316_179 loopBody316_286

def loopBody316_288 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_287

def loopBody316_289 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 15 (Flapjack.RegImm.imm 0#64) loopBody316_288 loopBody316_1 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody316_290 : HolLoopProg 64 :=
.seq loopBody316_289 loopBody316_1

def loopBody316_291 : HolLoopProg 64 :=
.seq loopBody316_177 loopBody316_290

def loopBody316_292 : HolLoopProg 64 :=
.seq loopBody316_175 loopBody316_291

def loopBody316_293 : HolLoopProg 64 :=
.seq loopBody316_171 loopBody316_292

def loopBody316_294 : HolLoopProg 64 :=
.seq loopBody316_169 loopBody316_293

def loopBody316_295 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 10,
      Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 11) (Flapjack.HolLoopExp.const 4#64)])

def loopBody316_296 : HolLoopProg 64 :=
.mark loopBody316_295

def loopBody316_297 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 10 (Flapjack.HolLoopExp.var 12)

def loopBody316_298 : HolLoopProg 64 :=
.mark loopBody316_297

def loopBody316_299 : HolLoopProg 64 :=
.seq loopBody316_298 loopBody316_1

def loopBody316_300 : HolLoopProg 64 :=
.mark loopBody316_299

def loopBody316_301 : HolLoopProg 64 :=
.seq loopBody316_300 loopBody316_1

def loopBody316_302 : HolLoopProg 64 :=
.mark loopBody316_301

def loopBody316_303 : HolLoopProg 64 :=
.seq loopBody316_296 loopBody316_302

def loopBody316_304 : HolLoopProg 64 :=
.mark loopBody316_303

def loopBody316_305 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_304

def loopBody316_306 : HolLoopProg 64 :=
.mark loopBody316_305

def loopBody316_307 : HolLoopProg 64 :=
.seq loopBody316_294 loopBody316_306

def loopBody316_308 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 0#64]))

def loopBody316_309 : HolLoopProg 64 :=
.mark loopBody316_308

def loopBody316_310 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15 (Flapjack.HolLoopExp.const 4#64)

def loopBody316_311 : HolLoopProg 64 :=
.mark loopBody316_310

def loopBody316_312 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 1#64)

def loopBody316_313 : HolLoopProg 64 :=
.mark loopBody316_312

def loopBody316_314 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.RegImm.reg 15) loopBody316_313 loopBody316_171 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody316_315 : HolLoopProg 64 :=
.mark loopBody316_314

def loopBody316_316 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.load
    (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 0, Flapjack.HolLoopExp.const 280#64]))

def loopBody316_317 : HolLoopProg 64 :=
.mark loopBody316_316

def loopBody316_318 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14 (Flapjack.HolLoopExp.const 7816#64)

def loopBody316_319 : HolLoopProg 64 :=
.mark loopBody316_318

def loopBody316_320 : HolLoopProg 64 :=
Flapjack.HolLoopProg.arith (Flapjack.LoopArith.longMul 15 15 13 14)

def loopBody316_321 : HolLoopProg 64 :=
.mark loopBody316_320

def loopBody316_322 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 12 (Flapjack.HolLoopExp.var 15)

def loopBody316_323 : HolLoopProg 64 :=
.mark loopBody316_322

def loopBody316_324 : HolLoopProg 64 :=
.seq loopBody316_323 loopBody316_1

def loopBody316_325 : HolLoopProg 64 :=
.mark loopBody316_324

def loopBody316_326 : HolLoopProg 64 :=
.seq loopBody316_321 loopBody316_325

def loopBody316_327 : HolLoopProg 64 :=
.mark loopBody316_326

def loopBody316_328 : HolLoopProg 64 :=
.seq loopBody316_319 loopBody316_327

def loopBody316_329 : HolLoopProg 64 :=
.mark loopBody316_328

def loopBody316_330 : HolLoopProg 64 :=
.seq loopBody316_317 loopBody316_329

def loopBody316_331 : HolLoopProg 64 :=
.mark loopBody316_330

def loopBody316_332 : HolLoopProg 64 :=
.seq loopBody316_331 loopBody316_1

def loopBody316_333 : HolLoopProg 64 :=
.mark loopBody316_332

def loopBody316_334 : HolLoopProg 64 :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.RegImm.imm 0#64) loopBody316_333 loopBody316_1 (Flapjack.Spt.bn
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))

def loopBody316_335 : HolLoopProg 64 :=
.mark loopBody316_334

def loopBody316_336 : HolLoopProg 64 :=
.seq loopBody316_335 loopBody316_1

def loopBody316_337 : HolLoopProg 64 :=
.mark loopBody316_336

def loopBody316_338 : HolLoopProg 64 :=
.seq loopBody316_183 loopBody316_337

def loopBody316_339 : HolLoopProg 64 :=
.mark loopBody316_338

def loopBody316_340 : HolLoopProg 64 :=
.seq loopBody316_315 loopBody316_339

def loopBody316_341 : HolLoopProg 64 :=
.mark loopBody316_340

def loopBody316_342 : HolLoopProg 64 :=
.seq loopBody316_311 loopBody316_341

def loopBody316_343 : HolLoopProg 64 :=
.mark loopBody316_342

def loopBody316_344 : HolLoopProg 64 :=
.seq loopBody316_309 loopBody316_343

def loopBody316_345 : HolLoopProg 64 :=
.mark loopBody316_344

def loopBody316_346 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 13
  (Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 3) (Flapjack.HolLoopExp.const 2#64))

def loopBody316_347 : HolLoopProg 64 :=
.mark loopBody316_346

def loopBody316_348 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 14
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.var 13, Flapjack.HolLoopExp.var 11])

def loopBody316_349 : HolLoopProg 64 :=
.mark loopBody316_348

def loopBody316_350 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 15
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add [Flapjack.HolLoopExp.const 12000#64, Flapjack.HolLoopExp.var 8])

def loopBody316_351 : HolLoopProg 64 :=
.mark loopBody316_350

def loopBody316_352 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 16
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.var 15, Flapjack.HolLoopExp.var 9, Flapjack.HolLoopExp.var 5, Flapjack.HolLoopExp.var 10,
      Flapjack.HolLoopExp.var 12])

def loopBody316_353 : HolLoopProg 64 :=
.mark loopBody316_352

def loopBody316_354 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 17
  (Flapjack.HolLoopExp.op Flapjack.BinOp.add
    [Flapjack.HolLoopExp.shift Flapjack.Shift.lsl (Flapjack.HolLoopExp.var 14) (Flapjack.HolLoopExp.const 4#64),
      Flapjack.HolLoopExp.var 15])

def loopBody316_355 : HolLoopProg 64 :=
.mark loopBody316_354

def loopBody316_356 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 19 (Flapjack.HolLoopExp.const 0#64)

def loopBody316_357 : HolLoopProg 64 :=
.mark loopBody316_356

def loopBody316_358 : HolLoopProg 64 :=
Flapjack.HolLoopProg.assign 20 (Flapjack.HolLoopExp.var 17)

def loopBody316_359 : HolLoopProg 64 :=
.mark loopBody316_358

def loopBody316_360 : HolLoopProg 64 :=
Flapjack.HolLoopProg.return [18, 19, 20]

def loopBody316_361 : HolLoopProg 64 :=
.mark loopBody316_360

def loopBody316_362 : HolLoopProg 64 :=
.seq loopBody316_361 loopBody316_1

def loopBody316_363 : HolLoopProg 64 :=
.mark loopBody316_362

def loopBody316_364 : HolLoopProg 64 :=
.seq loopBody316_359 loopBody316_363

def loopBody316_365 : HolLoopProg 64 :=
.mark loopBody316_364

def loopBody316_366 : HolLoopProg 64 :=
.seq loopBody316_357 loopBody316_365

def loopBody316_367 : HolLoopProg 64 :=
.mark loopBody316_366

def loopBody316_368 : HolLoopProg 64 :=
.seq loopBody316_193 loopBody316_367

def loopBody316_369 : HolLoopProg 64 :=
.mark loopBody316_368

def loopBody316_370 : HolLoopProg 64 :=
.seq loopBody316_355 loopBody316_369

def loopBody316_371 : HolLoopProg 64 :=
.mark loopBody316_370

def loopBody316_372 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_371

def loopBody316_373 : HolLoopProg 64 :=
.mark loopBody316_372

def loopBody316_374 : HolLoopProg 64 :=
.seq loopBody316_353 loopBody316_373

def loopBody316_375 : HolLoopProg 64 :=
.mark loopBody316_374

def loopBody316_376 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_375

def loopBody316_377 : HolLoopProg 64 :=
.mark loopBody316_376

def loopBody316_378 : HolLoopProg 64 :=
.seq loopBody316_351 loopBody316_377

def loopBody316_379 : HolLoopProg 64 :=
.mark loopBody316_378

def loopBody316_380 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_379

def loopBody316_381 : HolLoopProg 64 :=
.mark loopBody316_380

def loopBody316_382 : HolLoopProg 64 :=
.seq loopBody316_349 loopBody316_381

def loopBody316_383 : HolLoopProg 64 :=
.mark loopBody316_382

def loopBody316_384 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_383

def loopBody316_385 : HolLoopProg 64 :=
.mark loopBody316_384

def loopBody316_386 : HolLoopProg 64 :=
.seq loopBody316_347 loopBody316_385

def loopBody316_387 : HolLoopProg 64 :=
.mark loopBody316_386

def loopBody316_388 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_387

def loopBody316_389 : HolLoopProg 64 :=
.mark loopBody316_388

def loopBody316_390 : HolLoopProg 64 :=
.seq loopBody316_345 loopBody316_389

def loopBody316_391 : HolLoopProg 64 :=
.mark loopBody316_390

def loopBody316_392 : HolLoopProg 64 :=
.seq loopBody316_53 loopBody316_391

def loopBody316_393 : HolLoopProg 64 :=
.mark loopBody316_392

def loopBody316_394 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_393

def loopBody316_395 : HolLoopProg 64 :=
.mark loopBody316_394

def loopBody316_396 : HolLoopProg 64 :=
.seq loopBody316_307 loopBody316_395

def loopBody316_397 : HolLoopProg 64 :=
.seq loopBody316_57 loopBody316_396

def loopBody316_398 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_397

def loopBody316_399 : HolLoopProg 64 :=
.seq loopBody316_167 loopBody316_398

def loopBody316_400 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_399

def loopBody316_401 : HolLoopProg 64 :=
.seq loopBody316_165 loopBody316_400

def loopBody316_402 : HolLoopProg 64 :=
.seq loopBody316_49 loopBody316_401

def loopBody316_403 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_402

def loopBody316_404 : HolLoopProg 64 :=
.seq loopBody316_47 loopBody316_403

def loopBody316_405 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_404

def loopBody316_406 : HolLoopProg 64 :=
.seq loopBody316_45 loopBody316_405

def loopBody316_407 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_406

def loopBody316_408 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_407

def loopBody316_409 : HolLoopProg 64 :=
.seq loopBody316_23 loopBody316_408

def loopBody316_410 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_409

def loopBody316_411 : HolLoopProg 64 :=
.seq loopBody316_21 loopBody316_410

def loopBody316_412 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_411

def loopBody316_413 : HolLoopProg 64 :=
.seq loopBody316_19 loopBody316_412

def loopBody316_414 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_413

def loopBody316_415 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_414

def loopBody316_416 : HolLoopProg 64 :=
.seq loopBody316_5 loopBody316_415

def loopBody316_417 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_416

def loopBody316_418 : HolLoopProg 64 :=
.seq loopBody316_3 loopBody316_417

def loopBody316_419 : HolLoopProg 64 :=
.seq loopBody316_1 loopBody316_418

def output316 : Nat × List Nat × HolLoopProg 64 :=
  (380, [0, 1], loopBody316_419)
end InitECandidate.Proofs.FrontendStages.Loop
