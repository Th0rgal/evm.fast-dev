import InitECandidate.Proofs.WordStages.Source357
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody373_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody373_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody373_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 8) sourceBody373_2 sourceBody373_3

def sourceBody373_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody373_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_4 sourceBody373_5

def sourceBody373_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody373_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody373_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody373_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 30]

def sourceBody373_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody373_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_10 sourceBody373_11

def sourceBody373_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_9 sourceBody373_12

def sourceBody373_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_8 sourceBody373_13

def sourceBody373_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody373_14 sourceBody373_11

def sourceBody373_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_15 sourceBody373_5

def sourceBody373_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_16 sourceBody373_11

def sourceBody373_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_7 sourceBody373_17

def sourceBody373_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_6 sourceBody373_18

def sourceBody373_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_1 sourceBody373_19

def sourceBody373_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_0 sourceBody373_20

def sourceBody373_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64]))

def sourceBody373_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody373_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody373_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody373_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 12)

def sourceBody373_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 30)

def sourceBody373_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody373_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody373_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody373_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody373_11, 373, 2)) (some 101) ([36, 6, 24, 16]) (some (36, sourceBody373_30, 373, 3))

def sourceBody373_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_31 sourceBody373_5

def sourceBody373_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_32 sourceBody373_11

def sourceBody373_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_29 sourceBody373_33

def sourceBody373_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_28 sourceBody373_34

def sourceBody373_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_27 sourceBody373_35

def sourceBody373_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_26 sourceBody373_36

def sourceBody373_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody373_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody373_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 24) sourceBody373_40 sourceBody373_41

def sourceBody373_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_42 sourceBody373_5

def sourceBody373_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody373_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody373_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 27#64)

def sourceBody373_47 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 24) sourceBody373_40 sourceBody373_41

def sourceBody373_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_47 sourceBody373_5

def sourceBody373_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody373_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 28#64)

def sourceBody373_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody373_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 10) sourceBody373_51 sourceBody373_52

def sourceBody373_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_53 sourceBody373_5

def sourceBody373_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 34])

def sourceBody373_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody373_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 38) sourceBody373_57 sourceBody373_55

def sourceBody373_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_58 sourceBody373_5

def sourceBody373_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 20)

def sourceBody373_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36, 6]

def sourceBody373_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_62 sourceBody373_11

def sourceBody373_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_41 sourceBody373_63

def sourceBody373_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_61 sourceBody373_64

def sourceBody373_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody373_65 sourceBody373_11

def sourceBody373_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_66 sourceBody373_5

def sourceBody373_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_67 sourceBody373_11

def sourceBody373_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_60 sourceBody373_68

def sourceBody373_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_59 sourceBody373_69

def sourceBody373_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_56 sourceBody373_70

def sourceBody373_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_55 sourceBody373_71

def sourceBody373_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_54 sourceBody373_72

def sourceBody373_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_50 sourceBody373_73

def sourceBody373_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_49 sourceBody373_74

def sourceBody373_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_48 sourceBody373_75

def sourceBody373_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_46 sourceBody373_76

def sourceBody373_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_45 sourceBody373_77

def sourceBody373_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 35#64)

def sourceBody373_80 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.WordRegImm.reg 24) sourceBody373_40 sourceBody373_41

def sourceBody373_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_80 sourceBody373_5

def sourceBody373_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody373_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 36)

def sourceBody373_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_83 sourceBody373_11

def sourceBody373_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_84 sourceBody373_11

def sourceBody373_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_82 sourceBody373_85

def sourceBody373_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_86

def sourceBody373_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody373_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_88 sourceBody373_30

def sourceBody373_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_87 sourceBody373_89

def sourceBody373_91 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody373_90 sourceBody373_11

def sourceBody373_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_91 sourceBody373_5

def sourceBody373_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_92 sourceBody373_11

def sourceBody373_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_44 sourceBody373_93

def sourceBody373_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_81 sourceBody373_94

def sourceBody373_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_79 sourceBody373_95

def sourceBody373_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_45 sourceBody373_96

def sourceBody373_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_78 sourceBody373_97

def sourceBody373_99 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody373_98 sourceBody373_11

def sourceBody373_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_99 sourceBody373_5

def sourceBody373_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_100 sourceBody373_11

def sourceBody373_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_44 sourceBody373_101

def sourceBody373_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_43 sourceBody373_102

def sourceBody373_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_39 sourceBody373_103

def sourceBody373_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_38 sourceBody373_104

def sourceBody373_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 30)

def sourceBody373_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody373_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody373_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 35#64)

def sourceBody373_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody373_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody373_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 6, 24, 16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody373_11, 373, 4)) (some 117) ([34, 10, 28, 20, 38, 4, 22, 14]) (some (34, sourceBody373_113, 373, 5))

def sourceBody373_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_114 sourceBody373_5

def sourceBody373_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_115 sourceBody373_11

def sourceBody373_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_112 sourceBody373_116

def sourceBody373_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_111 sourceBody373_117

def sourceBody373_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_110 sourceBody373_118

def sourceBody373_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_109 sourceBody373_119

def sourceBody373_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_108 sourceBody373_120

def sourceBody373_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_107 sourceBody373_121

def sourceBody373_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_106 sourceBody373_122

def sourceBody373_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_49 sourceBody373_123

def sourceBody373_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 36)

def sourceBody373_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody373_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody373_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody373_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody373_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody373_131 : WordLangProgHOL (BitVec 64) :=
.call (some (([34, 10, 28, 20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody373_11, 373, 6)) (some 142) ([38, 4, 22, 14, 32]) (some (38, sourceBody373_130, 373, 7))

def sourceBody373_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_131 sourceBody373_5

def sourceBody373_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_132 sourceBody373_11

def sourceBody373_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_129 sourceBody373_133

def sourceBody373_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_128 sourceBody373_134

def sourceBody373_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_127 sourceBody373_135

def sourceBody373_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_126 sourceBody373_136

def sourceBody373_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_125 sourceBody373_137

def sourceBody373_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody373_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody373_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody373_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody373_143 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody373_11, 373, 8)) (some 101) ([38, 4, 22, 14]) (some (38, sourceBody373_130, 373, 9))

def sourceBody373_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_143 sourceBody373_5

def sourceBody373_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_144 sourceBody373_11

def sourceBody373_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_142 sourceBody373_145

def sourceBody373_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_141 sourceBody373_146

def sourceBody373_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_140 sourceBody373_147

def sourceBody373_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_139 sourceBody373_148

def sourceBody373_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody373_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody373_152 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 22) sourceBody373_151 sourceBody373_110

def sourceBody373_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_152 sourceBody373_5

def sourceBody373_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody373_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 45#64)

def sourceBody373_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 38)

def sourceBody373_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_156 sourceBody373_11

def sourceBody373_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_157 sourceBody373_11

def sourceBody373_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_155 sourceBody373_158

def sourceBody373_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_159

def sourceBody373_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody373_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_161 sourceBody373_130

def sourceBody373_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_160 sourceBody373_162

def sourceBody373_164 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody373_163 sourceBody373_11

def sourceBody373_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_164 sourceBody373_5

def sourceBody373_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_165 sourceBody373_11

def sourceBody373_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_154 sourceBody373_166

def sourceBody373_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_153 sourceBody373_167

def sourceBody373_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_111 sourceBody373_168

def sourceBody373_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_150 sourceBody373_169

def sourceBody373_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_149 sourceBody373_170

def sourceBody373_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody373_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 34)

def sourceBody373_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38, 4]

def sourceBody373_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_174 sourceBody373_11

def sourceBody373_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_173 sourceBody373_175

def sourceBody373_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_172 sourceBody373_176

def sourceBody373_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_171 sourceBody373_177

def sourceBody373_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_138 sourceBody373_178

def sourceBody373_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_179

def sourceBody373_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_180

def sourceBody373_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_181

def sourceBody373_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_182

def sourceBody373_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_183

def sourceBody373_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_184

def sourceBody373_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_185

def sourceBody373_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_186

def sourceBody373_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_124 sourceBody373_187

def sourceBody373_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_188

def sourceBody373_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_189

def sourceBody373_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_190

def sourceBody373_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_191

def sourceBody373_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_192

def sourceBody373_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_193

def sourceBody373_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_194

def sourceBody373_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_195

def sourceBody373_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_105 sourceBody373_196

def sourceBody373_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_37 sourceBody373_197

def sourceBody373_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_198

def sourceBody373_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_199

def sourceBody373_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_25 sourceBody373_200

def sourceBody373_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_201

def sourceBody373_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_24 sourceBody373_202

def sourceBody373_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_203

def sourceBody373_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_23 sourceBody373_204

def sourceBody373_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_205

def sourceBody373_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_22 sourceBody373_206

def sourceBody373_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_11 sourceBody373_207

def sourceBody373_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody373_21 sourceBody373_208

def source373 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (373, 2, sourceBody373_209)
end InitECandidate.Proofs.WordStages
