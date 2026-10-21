import InitECandidate.Proofs.WordStages.Source678
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody694_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody694_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody694_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody694_0, 694, 2)) (some 69) ([]) (some (8, sourceBody694_1, 694, 3))

def sourceBody694_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody694_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_2 sourceBody694_3

def sourceBody694_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_4 sourceBody694_0

def sourceBody694_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody694_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody694_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody694_0, 694, 4)) (some 68) ([18]) (some (18, sourceBody694_7, 694, 5))

def sourceBody694_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_8 sourceBody694_3

def sourceBody694_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_9 sourceBody694_0

def sourceBody694_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_6 sourceBody694_10

def sourceBody694_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody694_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody694_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody694_0, 694, 6)) (some 68) ([14]) (some (14, sourceBody694_13, 694, 7))

def sourceBody694_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_14 sourceBody694_3

def sourceBody694_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_15 sourceBody694_0

def sourceBody694_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_12 sourceBody694_16

def sourceBody694_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody694_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody694_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody694_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody694_0, 694, 8)) (some 691) ([24, 6]) (some (24, sourceBody694_20, 694, 9))

def sourceBody694_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_21 sourceBody694_3

def sourceBody694_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_22 sourceBody694_0

def sourceBody694_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_19 sourceBody694_23

def sourceBody694_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_18 sourceBody694_24

def sourceBody694_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody694_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody694_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody694_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody694_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 16) sourceBody694_28 sourceBody694_29

def sourceBody694_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_30 sourceBody694_3

def sourceBody694_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody694_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody694_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody694_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody694_0, 694, 10)) (some 70) ([6]) (some (6, sourceBody694_34, 694, 11))

def sourceBody694_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_35 sourceBody694_3

def sourceBody694_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_36 sourceBody694_0

def sourceBody694_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_33 sourceBody694_37

def sourceBody694_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_38

def sourceBody694_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_39

def sourceBody694_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody694_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody694_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_42 sourceBody694_0

def sourceBody694_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_41 sourceBody694_43

def sourceBody694_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_40 sourceBody694_44

def sourceBody694_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody694_45 sourceBody694_0

def sourceBody694_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_46 sourceBody694_3

def sourceBody694_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_47 sourceBody694_0

def sourceBody694_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_32 sourceBody694_48

def sourceBody694_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_31 sourceBody694_49

def sourceBody694_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_27 sourceBody694_50

def sourceBody694_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_26 sourceBody694_51

def sourceBody694_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody694_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody694_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody694_0, 694, 12)) (some 691) ([6, 16]) (some (6, sourceBody694_34, 694, 13))

def sourceBody694_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_55 sourceBody694_3

def sourceBody694_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_56 sourceBody694_0

def sourceBody694_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_54 sourceBody694_57

def sourceBody694_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_53 sourceBody694_58

def sourceBody694_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody694_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody694_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody694_63 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 12) sourceBody694_62 sourceBody694_27

def sourceBody694_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_63 sourceBody694_3

def sourceBody694_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody694_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody694_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody694_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody694_0, 694, 14)) (some 70) ([16]) (some (16, sourceBody694_67, 694, 15))

def sourceBody694_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_68 sourceBody694_3

def sourceBody694_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_69 sourceBody694_0

def sourceBody694_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_66 sourceBody694_70

def sourceBody694_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_71

def sourceBody694_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_72

def sourceBody694_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody694_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_74 sourceBody694_0

def sourceBody694_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_28 sourceBody694_75

def sourceBody694_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_73 sourceBody694_76

def sourceBody694_78 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody694_77 sourceBody694_0

def sourceBody694_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_78 sourceBody694_3

def sourceBody694_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_79 sourceBody694_0

def sourceBody694_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_65 sourceBody694_80

def sourceBody694_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_64 sourceBody694_81

def sourceBody694_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_61 sourceBody694_82

def sourceBody694_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_60 sourceBody694_83

def sourceBody694_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody694_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody694_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody694_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody694_0, 694, 16)) (some 679) ([16, 12, 22, 10]) (some (16, sourceBody694_67, 694, 17))

def sourceBody694_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_88 sourceBody694_3

def sourceBody694_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_89 sourceBody694_0

def sourceBody694_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_87 sourceBody694_90

def sourceBody694_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_86 sourceBody694_91

def sourceBody694_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_85 sourceBody694_92

def sourceBody694_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_62 sourceBody694_93

def sourceBody694_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_94

def sourceBody694_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_95

def sourceBody694_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_84 sourceBody694_96

def sourceBody694_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody694_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody694_100 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody694_0, 694, 18)) (some 693) ([16, 12]) (some (16, sourceBody694_67, 694, 19))

def sourceBody694_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_100 sourceBody694_3

def sourceBody694_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_101 sourceBody694_0

def sourceBody694_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_99 sourceBody694_102

def sourceBody694_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_98 sourceBody694_103

def sourceBody694_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_104

def sourceBody694_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_105

def sourceBody694_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_97 sourceBody694_106

def sourceBody694_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody694_0, 694, 20)) (some 70) ([16]) (some (16, sourceBody694_67, 694, 21))

def sourceBody694_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_108 sourceBody694_3

def sourceBody694_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_109 sourceBody694_0

def sourceBody694_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_66 sourceBody694_110

def sourceBody694_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_111

def sourceBody694_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_112

def sourceBody694_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_107 sourceBody694_113

def sourceBody694_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_29 sourceBody694_75

def sourceBody694_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_114 sourceBody694_115

def sourceBody694_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_59 sourceBody694_116

def sourceBody694_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_117

def sourceBody694_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_118

def sourceBody694_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_52 sourceBody694_119

def sourceBody694_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_25 sourceBody694_120

def sourceBody694_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_121

def sourceBody694_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_122

def sourceBody694_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_17 sourceBody694_123

def sourceBody694_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_124

def sourceBody694_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_125

def sourceBody694_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_11 sourceBody694_126

def sourceBody694_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_127

def sourceBody694_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_128

def sourceBody694_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_5 sourceBody694_129

def sourceBody694_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_130

def sourceBody694_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody694_0 sourceBody694_131

def source694 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (694, 3, sourceBody694_132)
end InitECandidate.Proofs.WordStages
