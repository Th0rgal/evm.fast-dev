import InitECandidate.Proofs.WordStages.Source550
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody566_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody566_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody566_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody566_0, 566, 2)) (some 471) ([]) (some (16, sourceBody566_1, 566, 3))

def sourceBody566_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody566_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_2 sourceBody566_3

def sourceBody566_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_4 sourceBody566_0

def sourceBody566_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody566_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 28)

def sourceBody566_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody566_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody566_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody566_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody566_0, 566, 4)) (some 462) ([32, 4, 22, 14]) (some (32, sourceBody566_10, 566, 5))

def sourceBody566_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_11 sourceBody566_3

def sourceBody566_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_12 sourceBody566_0

def sourceBody566_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_9 sourceBody566_13

def sourceBody566_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_8 sourceBody566_14

def sourceBody566_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_7 sourceBody566_15

def sourceBody566_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_6 sourceBody566_16

def sourceBody566_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 16)

def sourceBody566_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody566_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody566_0, 566, 6)) (some 491) ([4]) (some (4, sourceBody566_19, 566, 7))

def sourceBody566_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_20 sourceBody566_3

def sourceBody566_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_21 sourceBody566_0

def sourceBody566_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_18 sourceBody566_22

def sourceBody566_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 32)

def sourceBody566_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody566_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody566_0, 566, 8)) (some 466) ([22]) (some (22, sourceBody566_25, 566, 9))

def sourceBody566_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_26 sourceBody566_3

def sourceBody566_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_27 sourceBody566_0

def sourceBody566_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_24 sourceBody566_28

def sourceBody566_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_29

def sourceBody566_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_30

def sourceBody566_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody566_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 32)

def sourceBody566_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody566_0, 566, 10)) (some 492) ([22, 14]) (some (22, sourceBody566_25, 566, 11))

def sourceBody566_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_34 sourceBody566_3

def sourceBody566_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_35 sourceBody566_0

def sourceBody566_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_33 sourceBody566_36

def sourceBody566_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_32 sourceBody566_37

def sourceBody566_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_38

def sourceBody566_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_39

def sourceBody566_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_31 sourceBody566_40

def sourceBody566_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody566_0, 566, 12)) (some 403) ([22]) (some (22, sourceBody566_25, 566, 13))

def sourceBody566_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_42 sourceBody566_3

def sourceBody566_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_43 sourceBody566_0

def sourceBody566_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_32 sourceBody566_44

def sourceBody566_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody566_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody566_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody566_0, 566, 14)) (some 412) ([14]) (some (14, sourceBody566_47, 566, 15))

def sourceBody566_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_48 sourceBody566_3

def sourceBody566_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_49 sourceBody566_0

def sourceBody566_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_46 sourceBody566_50

def sourceBody566_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody566_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody566_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody566_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody566_56 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 8) sourceBody566_54 sourceBody566_55

def sourceBody566_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_56 sourceBody566_3

def sourceBody566_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody566_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody566_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody566_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody566_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody566_0, 566, 16)) (some 472) ([30, 8, 26, 18]) (some (30, sourceBody566_61, 566, 17))

def sourceBody566_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_62 sourceBody566_3

def sourceBody566_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_63 sourceBody566_0

def sourceBody566_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_60 sourceBody566_64

def sourceBody566_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_59 sourceBody566_65

def sourceBody566_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_53 sourceBody566_66

def sourceBody566_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_55 sourceBody566_67

def sourceBody566_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_68

def sourceBody566_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_69

def sourceBody566_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody566_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody566_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody566_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 30, 8, 26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody566_0, 566, 18)) (some 146) ([18, 34]) (some (18, sourceBody566_73, 566, 19))

def sourceBody566_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_74 sourceBody566_3

def sourceBody566_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_75 sourceBody566_0

def sourceBody566_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_72 sourceBody566_76

def sourceBody566_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_71 sourceBody566_77

def sourceBody566_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 14)

def sourceBody566_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 30)

def sourceBody566_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody566_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody566_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody566_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody566_0, 566, 20)) (some 472) ([34, 2, 20, 12]) (some (34, sourceBody566_83, 566, 21))

def sourceBody566_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_84 sourceBody566_3

def sourceBody566_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_85 sourceBody566_0

def sourceBody566_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_82 sourceBody566_86

def sourceBody566_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_81 sourceBody566_87

def sourceBody566_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_80 sourceBody566_88

def sourceBody566_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_79 sourceBody566_89

def sourceBody566_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_90

def sourceBody566_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_91

def sourceBody566_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_78 sourceBody566_92

def sourceBody566_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_93

def sourceBody566_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_94

def sourceBody566_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_95

def sourceBody566_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_96

def sourceBody566_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_97

def sourceBody566_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_98

def sourceBody566_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_99

def sourceBody566_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_100

def sourceBody566_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody566_70 sourceBody566_101

def sourceBody566_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_102 sourceBody566_3

def sourceBody566_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_103 sourceBody566_0

def sourceBody566_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_58 sourceBody566_104

def sourceBody566_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_57 sourceBody566_105

def sourceBody566_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_53 sourceBody566_106

def sourceBody566_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_52 sourceBody566_107

def sourceBody566_109 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody566_0, 566, 22)) (some 486) ([30]) (some (30, sourceBody566_61, 566, 23))

def sourceBody566_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_109 sourceBody566_3

def sourceBody566_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_110 sourceBody566_0

def sourceBody566_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_54 sourceBody566_111

def sourceBody566_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_112

def sourceBody566_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_113

def sourceBody566_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_108 sourceBody566_114

def sourceBody566_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody566_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody566_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_117 sourceBody566_0

def sourceBody566_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_116 sourceBody566_118

def sourceBody566_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_115 sourceBody566_119

def sourceBody566_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_51 sourceBody566_120

def sourceBody566_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_121

def sourceBody566_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_122

def sourceBody566_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_45 sourceBody566_123

def sourceBody566_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_124

def sourceBody566_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_125

def sourceBody566_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_41 sourceBody566_126

def sourceBody566_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_23 sourceBody566_127

def sourceBody566_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_128

def sourceBody566_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_129

def sourceBody566_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_17 sourceBody566_130

def sourceBody566_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_131

def sourceBody566_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_132

def sourceBody566_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_5 sourceBody566_133

def sourceBody566_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_134

def sourceBody566_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_135

def sourceBody566_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_136

def sourceBody566_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_137

def sourceBody566_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_138

def sourceBody566_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_139

def sourceBody566_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_140

def sourceBody566_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody566_0 sourceBody566_141

def source566 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (566, 1, sourceBody566_142)
end InitECandidate.Proofs.WordStages
