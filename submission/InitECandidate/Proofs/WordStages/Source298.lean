import InitECandidate.Proofs.WordStages.Source282
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody298_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody298_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody298_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 6)

def sourceBody298_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody298_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody298_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 40) sourceBody298_11 sourceBody298_12

def sourceBody298_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_13 sourceBody298_8

def sourceBody298_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 18)

def sourceBody298_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody298_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 40) sourceBody298_11 sourceBody298_12

def sourceBody298_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_18 sourceBody298_8

def sourceBody298_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody298_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody298_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 46)

def sourceBody298_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody298_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([44, 18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody298_0, 298, 2)) (some 297) ([40, 28, 50]) (some (40, sourceBody298_23, 298, 3))

def sourceBody298_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_24 sourceBody298_8

def sourceBody298_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_25 sourceBody298_0

def sourceBody298_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_22 sourceBody298_26

def sourceBody298_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_21 sourceBody298_27

def sourceBody298_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_20 sourceBody298_28

def sourceBody298_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 44)

def sourceBody298_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 50) sourceBody298_32 sourceBody298_33

def sourceBody298_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_34 sourceBody298_8

def sourceBody298_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody298_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 18)

def sourceBody298_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_37 sourceBody298_0

def sourceBody298_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_38 sourceBody298_0

def sourceBody298_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_40 sourceBody298_0

def sourceBody298_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_41 sourceBody298_0

def sourceBody298_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_39 sourceBody298_42

def sourceBody298_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody298_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody298_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 28)

def sourceBody298_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 50

def sourceBody298_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_47 sourceBody298_0

def sourceBody298_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_46 sourceBody298_48

def sourceBody298_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_49 sourceBody298_0

def sourceBody298_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_45 sourceBody298_50

def sourceBody298_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_51

def sourceBody298_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_44 sourceBody298_52

def sourceBody298_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_53

def sourceBody298_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody298_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_55 sourceBody298_0

def sourceBody298_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_56 sourceBody298_0

def sourceBody298_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_54 sourceBody298_57

def sourceBody298_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody298_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_61 sourceBody298_0

def sourceBody298_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_62 sourceBody298_0

def sourceBody298_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_6 sourceBody298_0

def sourceBody298_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_64 sourceBody298_0

def sourceBody298_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody298_63 sourceBody298_65

def sourceBody298_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_66 sourceBody298_8

def sourceBody298_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_67 sourceBody298_0

def sourceBody298_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_36 sourceBody298_68

def sourceBody298_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_35 sourceBody298_69

def sourceBody298_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_60 sourceBody298_70

def sourceBody298_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_59 sourceBody298_71

def sourceBody298_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_58 sourceBody298_72

def sourceBody298_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody298_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_74 sourceBody298_0

def sourceBody298_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_75 sourceBody298_0

def sourceBody298_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_73 sourceBody298_76

def sourceBody298_78 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody298_43 sourceBody298_77

def sourceBody298_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_78 sourceBody298_8

def sourceBody298_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_79 sourceBody298_0

def sourceBody298_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_36 sourceBody298_80

def sourceBody298_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_35 sourceBody298_81

def sourceBody298_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_31 sourceBody298_82

def sourceBody298_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_30 sourceBody298_83

def sourceBody298_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_29 sourceBody298_84

def sourceBody298_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_85

def sourceBody298_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_86

def sourceBody298_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_87

def sourceBody298_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_88

def sourceBody298_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody298_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody298_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody298_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 44,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody298_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 44,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody298_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody298_96 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 40, 28, 50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody298_0, 298, 4)) (some 296) ([8, 30, 20]) (some (8, sourceBody298_95, 298, 5))

def sourceBody298_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_96 sourceBody298_8

def sourceBody298_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_97 sourceBody298_0

def sourceBody298_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_94 sourceBody298_98

def sourceBody298_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_93 sourceBody298_99

def sourceBody298_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_92 sourceBody298_100

def sourceBody298_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody298_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_106 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 30 (Flapjack.WordRegImm.reg 20) sourceBody298_104 sourceBody298_105

def sourceBody298_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_106 sourceBody298_8

def sourceBody298_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 30)

def sourceBody298_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody298_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody298_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 20

def sourceBody298_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_111 sourceBody298_0

def sourceBody298_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_110 sourceBody298_112

def sourceBody298_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_113 sourceBody298_0

def sourceBody298_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_105 sourceBody298_114

def sourceBody298_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_115

def sourceBody298_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_109 sourceBody298_116

def sourceBody298_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_117

def sourceBody298_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 40)

def sourceBody298_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_119 sourceBody298_0

def sourceBody298_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_120 sourceBody298_0

def sourceBody298_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_118 sourceBody298_121

def sourceBody298_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_122 sourceBody298_42

def sourceBody298_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 50)

def sourceBody298_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_124 sourceBody298_114

def sourceBody298_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_125

def sourceBody298_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_109 sourceBody298_126

def sourceBody298_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_127

def sourceBody298_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 40)

def sourceBody298_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_129 sourceBody298_0

def sourceBody298_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_130 sourceBody298_0

def sourceBody298_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_128 sourceBody298_131

def sourceBody298_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 28)

def sourceBody298_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_133 sourceBody298_0

def sourceBody298_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_134 sourceBody298_0

def sourceBody298_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_132 sourceBody298_135

def sourceBody298_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_5 sourceBody298_0

def sourceBody298_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_137 sourceBody298_0

def sourceBody298_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_136 sourceBody298_138

def sourceBody298_140 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody298_123 sourceBody298_139

def sourceBody298_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_140 sourceBody298_8

def sourceBody298_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_141 sourceBody298_0

def sourceBody298_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_108 sourceBody298_142

def sourceBody298_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_107 sourceBody298_143

def sourceBody298_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_103 sourceBody298_144

def sourceBody298_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_102 sourceBody298_145

def sourceBody298_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_101 sourceBody298_146

def sourceBody298_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_147

def sourceBody298_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_148

def sourceBody298_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_149

def sourceBody298_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_150

def sourceBody298_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_151

def sourceBody298_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_152

def sourceBody298_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_153

def sourceBody298_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_154

def sourceBody298_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_91 sourceBody298_155

def sourceBody298_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_156

def sourceBody298_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody298_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_159 sourceBody298_0

def sourceBody298_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_160 sourceBody298_0

def sourceBody298_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 80#64]))

def sourceBody298_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 44)

def sourceBody298_164 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.reg 28) sourceBody298_17 sourceBody298_10

def sourceBody298_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_164 sourceBody298_8

def sourceBody298_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 40)

def sourceBody298_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_169 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 30) sourceBody298_168 sourceBody298_166

def sourceBody298_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_169 sourceBody298_8

def sourceBody298_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 36)

def sourceBody298_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_175 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.reg 16) sourceBody298_173 sourceBody298_174

def sourceBody298_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_175 sourceBody298_8

def sourceBody298_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 42)

def sourceBody298_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_180 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 48) sourceBody298_179 sourceBody298_177

def sourceBody298_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_180 sourceBody298_8

def sourceBody298_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 26])

def sourceBody298_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody298_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 40)

def sourceBody298_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 28

def sourceBody298_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_185 sourceBody298_0

def sourceBody298_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_184 sourceBody298_186

def sourceBody298_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_187 sourceBody298_0

def sourceBody298_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_163 sourceBody298_188

def sourceBody298_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_189

def sourceBody298_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_183 sourceBody298_190

def sourceBody298_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_191

def sourceBody298_193 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody298_192 sourceBody298_0

def sourceBody298_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_193 sourceBody298_8

def sourceBody298_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_194 sourceBody298_0

def sourceBody298_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_182 sourceBody298_195

def sourceBody298_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_181 sourceBody298_196

def sourceBody298_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_178 sourceBody298_197

def sourceBody298_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_177 sourceBody298_198

def sourceBody298_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_176 sourceBody298_199

def sourceBody298_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_172 sourceBody298_200

def sourceBody298_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_171 sourceBody298_201

def sourceBody298_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_170 sourceBody298_202

def sourceBody298_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_167 sourceBody298_203

def sourceBody298_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_166 sourceBody298_204

def sourceBody298_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_165 sourceBody298_205

def sourceBody298_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_33 sourceBody298_206

def sourceBody298_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_163 sourceBody298_207

def sourceBody298_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody298_210 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 28) sourceBody298_17 sourceBody298_10

def sourceBody298_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_210 sourceBody298_8

def sourceBody298_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 40)

def sourceBody298_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 36)

def sourceBody298_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody298_215 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody298_0, 298, 6)) (some 282) ([40]) (some (40, sourceBody298_23, 298, 7))

def sourceBody298_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_215 sourceBody298_8

def sourceBody298_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_216 sourceBody298_0

def sourceBody298_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_214 sourceBody298_217

def sourceBody298_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_218

def sourceBody298_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_219

def sourceBody298_221 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.imm 0#64) sourceBody298_220 sourceBody298_0

def sourceBody298_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_221 sourceBody298_8

def sourceBody298_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_222 sourceBody298_0

def sourceBody298_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_212 sourceBody298_223

def sourceBody298_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_211 sourceBody298_224

def sourceBody298_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_33 sourceBody298_225

def sourceBody298_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_213 sourceBody298_226

def sourceBody298_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody298_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody298_230 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 50) sourceBody298_32 sourceBody298_33

def sourceBody298_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_230 sourceBody298_8

def sourceBody298_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody298_233 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 20) sourceBody298_104 sourceBody298_105

def sourceBody298_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_233 sourceBody298_8

def sourceBody298_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody298_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_238 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 38) sourceBody298_237 sourceBody298_172

def sourceBody298_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_238 sourceBody298_8

def sourceBody298_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody298_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody298_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_243 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.reg 12) sourceBody298_242 sourceBody298_240

def sourceBody298_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_243 sourceBody298_8

def sourceBody298_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 48])

def sourceBody298_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody298_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody298_248 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody298_0, 298, 8)) (some 282) ([28]) (some (28, sourceBody298_247, 298, 9))

def sourceBody298_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_248 sourceBody298_8

def sourceBody298_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_249 sourceBody298_0

def sourceBody298_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_246 sourceBody298_250

def sourceBody298_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_251

def sourceBody298_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_252

def sourceBody298_254 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody298_253 sourceBody298_0

def sourceBody298_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_254 sourceBody298_8

def sourceBody298_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_255 sourceBody298_0

def sourceBody298_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_245 sourceBody298_256

def sourceBody298_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_244 sourceBody298_257

def sourceBody298_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_241 sourceBody298_258

def sourceBody298_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_240 sourceBody298_259

def sourceBody298_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_239 sourceBody298_260

def sourceBody298_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_236 sourceBody298_261

def sourceBody298_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_235 sourceBody298_262

def sourceBody298_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_234 sourceBody298_263

def sourceBody298_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_232 sourceBody298_264

def sourceBody298_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_105 sourceBody298_265

def sourceBody298_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_231 sourceBody298_266

def sourceBody298_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_229 sourceBody298_267

def sourceBody298_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_15 sourceBody298_268

def sourceBody298_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody298_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody298_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 36)

def sourceBody298_273 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody298_0, 298, 10)) (some 293) ([28, 50, 8]) (some (28, sourceBody298_247, 298, 11))

def sourceBody298_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_273 sourceBody298_8

def sourceBody298_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_274 sourceBody298_0

def sourceBody298_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_272 sourceBody298_275

def sourceBody298_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_271 sourceBody298_276

def sourceBody298_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_270 sourceBody298_277

def sourceBody298_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody298_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody298_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 50)

def sourceBody298_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 28) 8

def sourceBody298_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_282 sourceBody298_0

def sourceBody298_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_281 sourceBody298_283

def sourceBody298_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_284 sourceBody298_0

def sourceBody298_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_280 sourceBody298_285

def sourceBody298_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_286

def sourceBody298_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_279 sourceBody298_287

def sourceBody298_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_288

def sourceBody298_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody298_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody298_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_291 sourceBody298_285

def sourceBody298_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_292

def sourceBody298_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_290 sourceBody298_293

def sourceBody298_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_294

def sourceBody298_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_289 sourceBody298_295

def sourceBody298_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody298_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 28)

def sourceBody298_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_298 sourceBody298_0

def sourceBody298_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_299 sourceBody298_0

def sourceBody298_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_297 sourceBody298_300

def sourceBody298_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_301

def sourceBody298_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_296 sourceBody298_302

def sourceBody298_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_303 sourceBody298_121

def sourceBody298_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_278 sourceBody298_304

def sourceBody298_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_305

def sourceBody298_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_306

def sourceBody298_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_269 sourceBody298_307

def sourceBody298_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_228 sourceBody298_308

def sourceBody298_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_309

def sourceBody298_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_227 sourceBody298_310

def sourceBody298_312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody298_313 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody298_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 32#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody298_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 36)

def sourceBody298_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_315 sourceBody298_285

def sourceBody298_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_316

def sourceBody298_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_314 sourceBody298_317

def sourceBody298_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_318

def sourceBody298_320 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.reg 8) sourceBody298_60 sourceBody298_31

def sourceBody298_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_320 sourceBody298_8

def sourceBody298_322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody298_323 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 40#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody298_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_323 sourceBody298_285

def sourceBody298_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_324

def sourceBody298_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_322 sourceBody298_325

def sourceBody298_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_326

def sourceBody298_328 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody298_327 sourceBody298_0

def sourceBody298_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_328 sourceBody298_8

def sourceBody298_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_329 sourceBody298_0

def sourceBody298_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_124 sourceBody298_330

def sourceBody298_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_321 sourceBody298_331

def sourceBody298_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_166 sourceBody298_332

def sourceBody298_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_315 sourceBody298_333

def sourceBody298_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_319 sourceBody298_334

def sourceBody298_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody298_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody298_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_337 sourceBody298_0

def sourceBody298_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_338 sourceBody298_0

def sourceBody298_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_336 sourceBody298_339

def sourceBody298_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_340

def sourceBody298_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_335 sourceBody298_341

def sourceBody298_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody298_344 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 50 (Flapjack.WordRegImm.reg 8) sourceBody298_60 sourceBody298_31

def sourceBody298_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_344 sourceBody298_8

def sourceBody298_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody298_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_212 sourceBody298_285

def sourceBody298_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_347

def sourceBody298_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_346 sourceBody298_348

def sourceBody298_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_349

def sourceBody298_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 40)

def sourceBody298_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_351 sourceBody298_0

def sourceBody298_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_352 sourceBody298_0

def sourceBody298_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_350 sourceBody298_353

def sourceBody298_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_354 sourceBody298_76

def sourceBody298_356 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody298_357 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody298_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 256#64, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody298_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody298_360 : WordLangProgHOL (BitVec 64) :=
.call (some (([50, 8, 30, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody298_0, 298, 12)) (some 161) ([42, 16]) (some (42, sourceBody298_359, 298, 13))

def sourceBody298_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_360 sourceBody298_8

def sourceBody298_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_361 sourceBody298_0

def sourceBody298_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_358 sourceBody298_362

def sourceBody298_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_357 sourceBody298_363

def sourceBody298_365 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody298_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 50)

def sourceBody298_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody298_368 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 38 (Flapjack.WordRegImm.reg 26) sourceBody298_367 sourceBody298_236

def sourceBody298_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_368 sourceBody298_8

def sourceBody298_370 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody298_371 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody298_372 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody298_373 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 38)

def sourceBody298_374 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 26

def sourceBody298_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_374 sourceBody298_0

def sourceBody298_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_373 sourceBody298_375

def sourceBody298_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_376 sourceBody298_0

def sourceBody298_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_372 sourceBody298_377

def sourceBody298_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_378

def sourceBody298_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_371 sourceBody298_379

def sourceBody298_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_380

def sourceBody298_382 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 168#64])

def sourceBody298_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody298_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_383 sourceBody298_377

def sourceBody298_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_384

def sourceBody298_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_382 sourceBody298_385

def sourceBody298_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_386

def sourceBody298_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_381 sourceBody298_387

def sourceBody298_389 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.reg 26) sourceBody298_367 sourceBody298_236

def sourceBody298_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_389 sourceBody298_8

def sourceBody298_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody298_392 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 16)

def sourceBody298_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_392 sourceBody298_0

def sourceBody298_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_393 sourceBody298_0

def sourceBody298_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_391 sourceBody298_394

def sourceBody298_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_395

def sourceBody298_397 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody298_396 sourceBody298_0

def sourceBody298_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_397 sourceBody298_8

def sourceBody298_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_398 sourceBody298_0

def sourceBody298_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_370 sourceBody298_399

def sourceBody298_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_390 sourceBody298_400

def sourceBody298_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_177 sourceBody298_401

def sourceBody298_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_383 sourceBody298_402

def sourceBody298_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_388 sourceBody298_403

def sourceBody298_405 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody298_404 sourceBody298_0

def sourceBody298_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_405 sourceBody298_8

def sourceBody298_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_406 sourceBody298_0

def sourceBody298_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_370 sourceBody298_407

def sourceBody298_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_369 sourceBody298_408

def sourceBody298_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_177 sourceBody298_409

def sourceBody298_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_366 sourceBody298_410

def sourceBody298_412 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 42)

def sourceBody298_413 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody298_414 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 38 (Flapjack.WordRegImm.reg 26) sourceBody298_367 sourceBody298_236

def sourceBody298_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_414 sourceBody298_8

def sourceBody298_416 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody298_417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody298_418 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody298_0, 298, 14)) (some 282) ([38]) (some (38, sourceBody298_417, 298, 15))

def sourceBody298_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_418 sourceBody298_8

def sourceBody298_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_419 sourceBody298_0

def sourceBody298_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_416 sourceBody298_420

def sourceBody298_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_421

def sourceBody298_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_422

def sourceBody298_424 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.imm 0#64) sourceBody298_423 sourceBody298_0

def sourceBody298_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_424 sourceBody298_8

def sourceBody298_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_425 sourceBody298_0

def sourceBody298_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_370 sourceBody298_426

def sourceBody298_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_415 sourceBody298_427

def sourceBody298_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_413 sourceBody298_428

def sourceBody298_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_412 sourceBody298_429

def sourceBody298_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_411 sourceBody298_430

def sourceBody298_432 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody298_433 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody298_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_433 sourceBody298_377

def sourceBody298_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_434

def sourceBody298_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_432 sourceBody298_435

def sourceBody298_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_436

def sourceBody298_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_431 sourceBody298_437

def sourceBody298_439 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody298_440 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody298_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_440 sourceBody298_377

def sourceBody298_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_441

def sourceBody298_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_439 sourceBody298_442

def sourceBody298_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_443

def sourceBody298_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_438 sourceBody298_444

def sourceBody298_446 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody298_447 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody298_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_447 sourceBody298_0

def sourceBody298_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_448 sourceBody298_0

def sourceBody298_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_446 sourceBody298_449

def sourceBody298_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_450

def sourceBody298_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_445 sourceBody298_451

def sourceBody298_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_452 sourceBody298_39

def sourceBody298_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_365 sourceBody298_453

def sourceBody298_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_454

def sourceBody298_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_364 sourceBody298_455

def sourceBody298_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_456

def sourceBody298_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_457

def sourceBody298_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_458

def sourceBody298_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_459

def sourceBody298_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_460

def sourceBody298_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_461

def sourceBody298_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_462

def sourceBody298_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_463

def sourceBody298_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_356 sourceBody298_464

def sourceBody298_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_465

def sourceBody298_467 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody298_355 sourceBody298_466

def sourceBody298_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_467 sourceBody298_8

def sourceBody298_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_468 sourceBody298_0

def sourceBody298_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_124 sourceBody298_469

def sourceBody298_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_345 sourceBody298_470

def sourceBody298_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_343 sourceBody298_471

def sourceBody298_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_212 sourceBody298_472

def sourceBody298_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_342 sourceBody298_473

def sourceBody298_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_313 sourceBody298_474

def sourceBody298_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_475

def sourceBody298_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_312 sourceBody298_476

def sourceBody298_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_477

def sourceBody298_479 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.imm 0#64) sourceBody298_311 sourceBody298_478

def sourceBody298_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_479 sourceBody298_8

def sourceBody298_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_480 sourceBody298_0

def sourceBody298_482 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_212 sourceBody298_481

def sourceBody298_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_211 sourceBody298_482

def sourceBody298_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_32 sourceBody298_483

def sourceBody298_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_209 sourceBody298_484

def sourceBody298_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_208 sourceBody298_485

def sourceBody298_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_162 sourceBody298_486

def sourceBody298_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_487

def sourceBody298_489 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody298_161 sourceBody298_488

def sourceBody298_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_489 sourceBody298_8

def sourceBody298_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_490 sourceBody298_0

def sourceBody298_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_15 sourceBody298_491

def sourceBody298_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_19 sourceBody298_492

def sourceBody298_494 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_10 sourceBody298_493

def sourceBody298_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_158 sourceBody298_494

def sourceBody298_496 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody298_157 sourceBody298_495

def sourceBody298_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_496 sourceBody298_8

def sourceBody298_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_497 sourceBody298_0

def sourceBody298_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_15 sourceBody298_498

def sourceBody298_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_19 sourceBody298_499

def sourceBody298_501 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_90 sourceBody298_500

def sourceBody298_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_16 sourceBody298_501

def sourceBody298_503 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody298_89 sourceBody298_502

def sourceBody298_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_503 sourceBody298_8

def sourceBody298_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_504 sourceBody298_0

def sourceBody298_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_15 sourceBody298_505

def sourceBody298_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_19 sourceBody298_506

def sourceBody298_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_17 sourceBody298_507

def sourceBody298_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_16 sourceBody298_508

def sourceBody298_510 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody298_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_509 sourceBody298_510

def sourceBody298_512 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody298_513 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody298_511 sourceBody298_512

def sourceBody298_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_513 sourceBody298_8

def sourceBody298_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_514 sourceBody298_0

def sourceBody298_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_15 sourceBody298_515

def sourceBody298_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_14 sourceBody298_516

def sourceBody298_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_10 sourceBody298_517

def sourceBody298_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_9 sourceBody298_518

def sourceBody298_520 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody298_519 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody298_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_520 sourceBody298_8

def sourceBody298_522 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_8 sourceBody298_521

def sourceBody298_523 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 36)

def sourceBody298_524 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [44]

def sourceBody298_525 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_524 sourceBody298_0

def sourceBody298_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_523 sourceBody298_525

def sourceBody298_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_522 sourceBody298_526

def sourceBody298_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_7 sourceBody298_527

def sourceBody298_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_528

def sourceBody298_530 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_6 sourceBody298_529

def sourceBody298_531 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_530

def sourceBody298_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_5 sourceBody298_531

def sourceBody298_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_532

def sourceBody298_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_4 sourceBody298_533

def sourceBody298_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_534

def sourceBody298_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_3 sourceBody298_535

def sourceBody298_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_536

def sourceBody298_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_2 sourceBody298_537

def sourceBody298_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_538

def sourceBody298_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_1 sourceBody298_539

def sourceBody298_541 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody298_0 sourceBody298_540

def source298 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (298, 4, sourceBody298_541)
end InitECandidate.Proofs.WordStages
