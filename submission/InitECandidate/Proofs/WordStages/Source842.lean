import InitECandidate.Proofs.WordStages.Source826
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody842_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody842_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 80#64)

def sourceBody842_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody842_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody842_0, 842, 2)) (some 68) ([24]) (some (24, sourceBody842_2, 842, 3))

def sourceBody842_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody842_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_3 sourceBody842_4

def sourceBody842_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_5 sourceBody842_0

def sourceBody842_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_1 sourceBody842_6

def sourceBody842_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody842_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody842_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody842_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody842_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody842_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody842_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 14 (Flapjack.WordRegImm.reg 28) sourceBody842_12 sourceBody842_13

def sourceBody842_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_14 sourceBody842_4

def sourceBody842_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 14)

def sourceBody842_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody842_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody842_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody842_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody842_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody842_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody842_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody842_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 12) sourceBody842_22 sourceBody842_23

def sourceBody842_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_24 sourceBody842_4

def sourceBody842_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody842_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 76#64)

def sourceBody842_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_27 sourceBody842_0

def sourceBody842_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_28 sourceBody842_0

def sourceBody842_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody842_29 sourceBody842_0

def sourceBody842_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_30 sourceBody842_4

def sourceBody842_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_31 sourceBody842_0

def sourceBody842_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_26 sourceBody842_32

def sourceBody842_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_25 sourceBody842_33

def sourceBody842_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_21 sourceBody842_34

def sourceBody842_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_20 sourceBody842_35

def sourceBody842_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody842_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 116#64)

def sourceBody842_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_38 sourceBody842_0

def sourceBody842_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_39 sourceBody842_0

def sourceBody842_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody842_40 sourceBody842_0

def sourceBody842_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_41 sourceBody842_4

def sourceBody842_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_42 sourceBody842_0

def sourceBody842_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_26 sourceBody842_43

def sourceBody842_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_25 sourceBody842_44

def sourceBody842_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_37 sourceBody842_45

def sourceBody842_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_20 sourceBody842_46

def sourceBody842_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_36 sourceBody842_47

def sourceBody842_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody842_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 184#64)

def sourceBody842_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_50 sourceBody842_0

def sourceBody842_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_51 sourceBody842_0

def sourceBody842_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody842_52 sourceBody842_0

def sourceBody842_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_53 sourceBody842_4

def sourceBody842_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_54 sourceBody842_0

def sourceBody842_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_26 sourceBody842_55

def sourceBody842_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_25 sourceBody842_56

def sourceBody842_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_49 sourceBody842_57

def sourceBody842_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_20 sourceBody842_58

def sourceBody842_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_48 sourceBody842_59

def sourceBody842_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody842_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 68#64)

def sourceBody842_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_62 sourceBody842_0

def sourceBody842_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_63 sourceBody842_0

def sourceBody842_65 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody842_64 sourceBody842_0

def sourceBody842_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_65 sourceBody842_4

def sourceBody842_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_66 sourceBody842_0

def sourceBody842_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_26 sourceBody842_67

def sourceBody842_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_25 sourceBody842_68

def sourceBody842_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_61 sourceBody842_69

def sourceBody842_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_20 sourceBody842_70

def sourceBody842_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_60 sourceBody842_71

def sourceBody842_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody842_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody842_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 12) sourceBody842_22 sourceBody842_23

def sourceBody842_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_75 sourceBody842_4

def sourceBody842_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody842_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 26 26 18 12))

def sourceBody842_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody842_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody842_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody842_0, 842, 4)) (some 68) ([8]) (some (18, sourceBody842_80, 842, 5))

def sourceBody842_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_81 sourceBody842_4

def sourceBody842_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_82 sourceBody842_0

def sourceBody842_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_79 sourceBody842_83

def sourceBody842_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_78 sourceBody842_84

def sourceBody842_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_77 sourceBody842_85

def sourceBody842_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_73 sourceBody842_86

def sourceBody842_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody842_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody842_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 12 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody842_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_90 sourceBody842_0

def sourceBody842_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_89 sourceBody842_91

def sourceBody842_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_88 sourceBody842_92

def sourceBody842_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody842_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody842_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 8 8 12 26))

def sourceBody842_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody842_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody842_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody842_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody842_101 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody842_0, 842, 6)) (some 77) ([22, 16, 30]) (some (12, sourceBody842_100, 842, 7))

def sourceBody842_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_101 sourceBody842_4

def sourceBody842_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_102 sourceBody842_0

def sourceBody842_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_99 sourceBody842_103

def sourceBody842_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_98 sourceBody842_104

def sourceBody842_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_97 sourceBody842_105

def sourceBody842_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_96 sourceBody842_106

def sourceBody842_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_95 sourceBody842_107

def sourceBody842_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_94 sourceBody842_108

def sourceBody842_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_109

def sourceBody842_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_110

def sourceBody842_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_93 sourceBody842_111

def sourceBody842_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 4#64)])

def sourceBody842_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody842_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 12)

def sourceBody842_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 26

def sourceBody842_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_116 sourceBody842_0

def sourceBody842_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_115 sourceBody842_117

def sourceBody842_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_118 sourceBody842_0

def sourceBody842_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_114 sourceBody842_119

def sourceBody842_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_120

def sourceBody842_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_113 sourceBody842_121

def sourceBody842_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_122

def sourceBody842_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_112 sourceBody842_123

def sourceBody842_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody842_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_96 sourceBody842_0

def sourceBody842_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_95 sourceBody842_126

def sourceBody842_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_94 sourceBody842_127

def sourceBody842_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody842_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody842_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 16

def sourceBody842_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_131 sourceBody842_0

def sourceBody842_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_130 sourceBody842_132

def sourceBody842_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_133 sourceBody842_0

def sourceBody842_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_129 sourceBody842_134

def sourceBody842_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_128 sourceBody842_135

def sourceBody842_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_125 sourceBody842_136

def sourceBody842_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_137

def sourceBody842_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_124 sourceBody842_138

def sourceBody842_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody842_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody842_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_141 sourceBody842_0

def sourceBody842_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_142 sourceBody842_0

def sourceBody842_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_140 sourceBody842_143

def sourceBody842_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_144

def sourceBody842_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_139 sourceBody842_145

def sourceBody842_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_87 sourceBody842_146

def sourceBody842_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_147

def sourceBody842_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_148

def sourceBody842_150 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody842_149 sourceBody842_0

def sourceBody842_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_150 sourceBody842_4

def sourceBody842_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_151 sourceBody842_0

def sourceBody842_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_26 sourceBody842_152

def sourceBody842_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_76 sourceBody842_153

def sourceBody842_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_74 sourceBody842_154

def sourceBody842_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_73 sourceBody842_155

def sourceBody842_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_72 sourceBody842_156

def sourceBody842_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody842_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody842_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_159 sourceBody842_0

def sourceBody842_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_160 sourceBody842_0

def sourceBody842_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_158 sourceBody842_161

def sourceBody842_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_162

def sourceBody842_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_157 sourceBody842_163

def sourceBody842_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_19 sourceBody842_164

def sourceBody842_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_165

def sourceBody842_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_18 sourceBody842_166

def sourceBody842_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_167

def sourceBody842_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_17 sourceBody842_168

def sourceBody842_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_169

def sourceBody842_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody842_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_170 sourceBody842_171

def sourceBody842_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody842_174 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody842_172 sourceBody842_173

def sourceBody842_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_174 sourceBody842_4

def sourceBody842_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_175 sourceBody842_0

def sourceBody842_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_16 sourceBody842_176

def sourceBody842_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_15 sourceBody842_177

def sourceBody842_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_11 sourceBody842_178

def sourceBody842_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_10 sourceBody842_179

def sourceBody842_181 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody842_180 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody842_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_181 sourceBody842_4

def sourceBody842_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_4 sourceBody842_182

def sourceBody842_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody842_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody842_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20, 14]

def sourceBody842_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_186 sourceBody842_0

def sourceBody842_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_185 sourceBody842_187

def sourceBody842_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_184 sourceBody842_188

def sourceBody842_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_183 sourceBody842_189

def sourceBody842_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_9 sourceBody842_190

def sourceBody842_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_191

def sourceBody842_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_8 sourceBody842_192

def sourceBody842_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_193

def sourceBody842_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_7 sourceBody842_194

def sourceBody842_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_195

def sourceBody842_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody842_0 sourceBody842_196

def source842 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (842, 2, sourceBody842_197)
end InitECandidate.Proofs.WordStages
