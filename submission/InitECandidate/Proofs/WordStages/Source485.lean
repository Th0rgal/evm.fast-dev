import InitECandidate.Proofs.WordStages.Source469
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody485_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody485_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody485_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody485_0, 485, 2)) (some 75) ([]) (some (22, sourceBody485_1, 485, 3))

def sourceBody485_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody485_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_2 sourceBody485_3

def sourceBody485_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_4 sourceBody485_0

def sourceBody485_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody485_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 4)) (some 72) ([]) (some (6, sourceBody485_6, 485, 5))

def sourceBody485_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_7 sourceBody485_3

def sourceBody485_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_8 sourceBody485_0

def sourceBody485_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 280#64)

def sourceBody485_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody485_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 6)) (some 74) ([18]) (some (18, sourceBody485_11, 485, 7))

def sourceBody485_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_12 sourceBody485_3

def sourceBody485_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_13 sourceBody485_0

def sourceBody485_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_10 sourceBody485_14

def sourceBody485_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody485_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 280#64)

def sourceBody485_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody485_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 8)) (some 78) ([14, 26]) (some (14, sourceBody485_18, 485, 9))

def sourceBody485_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_19 sourceBody485_3

def sourceBody485_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_20 sourceBody485_0

def sourceBody485_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_17 sourceBody485_21

def sourceBody485_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_16 sourceBody485_22

def sourceBody485_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_23

def sourceBody485_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_24

def sourceBody485_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody485_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 10)) (some 74) ([14]) (some (14, sourceBody485_18, 485, 11))

def sourceBody485_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_27 sourceBody485_3

def sourceBody485_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_28 sourceBody485_0

def sourceBody485_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_26 sourceBody485_29

def sourceBody485_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 208#64])

def sourceBody485_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody485_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 26)

def sourceBody485_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 4

def sourceBody485_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_34 sourceBody485_0

def sourceBody485_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_33 sourceBody485_35

def sourceBody485_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_36 sourceBody485_0

def sourceBody485_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_32 sourceBody485_37

def sourceBody485_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_38

def sourceBody485_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_31 sourceBody485_39

def sourceBody485_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_40

def sourceBody485_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody485_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody485_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_43 sourceBody485_37

def sourceBody485_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_44

def sourceBody485_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_42 sourceBody485_45

def sourceBody485_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_46

def sourceBody485_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_41 sourceBody485_47

def sourceBody485_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 232#64])

def sourceBody485_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody485_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_50 sourceBody485_37

def sourceBody485_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_51

def sourceBody485_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_49 sourceBody485_52

def sourceBody485_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_53

def sourceBody485_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_48 sourceBody485_54

def sourceBody485_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody485_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody485_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 12)) (some 71) ([26]) (some (26, sourceBody485_57, 485, 13))

def sourceBody485_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_58 sourceBody485_3

def sourceBody485_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_59 sourceBody485_0

def sourceBody485_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_56 sourceBody485_60

def sourceBody485_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 224#64])

def sourceBody485_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 22)

def sourceBody485_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody485_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 16

def sourceBody485_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_65 sourceBody485_0

def sourceBody485_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_64 sourceBody485_66

def sourceBody485_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_67 sourceBody485_0

def sourceBody485_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_63 sourceBody485_68

def sourceBody485_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_69

def sourceBody485_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_62 sourceBody485_70

def sourceBody485_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_71

def sourceBody485_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody485_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 14)

def sourceBody485_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_74 sourceBody485_68

def sourceBody485_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_75

def sourceBody485_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_73 sourceBody485_76

def sourceBody485_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_77

def sourceBody485_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_72 sourceBody485_78

def sourceBody485_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody485_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody485_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_81 sourceBody485_68

def sourceBody485_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_82

def sourceBody485_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_80 sourceBody485_83

def sourceBody485_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_84

def sourceBody485_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_79 sourceBody485_85

def sourceBody485_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody485_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody485_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_88 sourceBody485_68

def sourceBody485_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_89

def sourceBody485_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_87 sourceBody485_90

def sourceBody485_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_91

def sourceBody485_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_86 sourceBody485_92

def sourceBody485_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody485_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody485_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_95 sourceBody485_68

def sourceBody485_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_96

def sourceBody485_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_94 sourceBody485_97

def sourceBody485_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_98

def sourceBody485_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_93 sourceBody485_99

def sourceBody485_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody485_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody485_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_102 sourceBody485_68

def sourceBody485_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_103

def sourceBody485_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_101 sourceBody485_104

def sourceBody485_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_105

def sourceBody485_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_100 sourceBody485_106

def sourceBody485_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 72#64])

def sourceBody485_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody485_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_109 sourceBody485_68

def sourceBody485_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_110

def sourceBody485_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_108 sourceBody485_111

def sourceBody485_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_112

def sourceBody485_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_107 sourceBody485_113

def sourceBody485_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody485_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody485_117 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 14)) (some 481) ([4, 16]) (some (4, sourceBody485_116, 485, 15))

def sourceBody485_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_117 sourceBody485_3

def sourceBody485_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_118 sourceBody485_0

def sourceBody485_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_115 sourceBody485_119

def sourceBody485_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_88 sourceBody485_120

def sourceBody485_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody485_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody485_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody485_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 12

def sourceBody485_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_125 sourceBody485_0

def sourceBody485_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_124 sourceBody485_126

def sourceBody485_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_127 sourceBody485_0

def sourceBody485_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_123 sourceBody485_128

def sourceBody485_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_129

def sourceBody485_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_122 sourceBody485_130

def sourceBody485_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_131

def sourceBody485_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody485_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody485_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody485_136 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 16)) (some 432) ([16, 12]) (some (16, sourceBody485_135, 485, 17))

def sourceBody485_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_136 sourceBody485_3

def sourceBody485_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_137 sourceBody485_0

def sourceBody485_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_134 sourceBody485_138

def sourceBody485_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_133 sourceBody485_139

def sourceBody485_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody485_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody485_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody485_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 24

def sourceBody485_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_144 sourceBody485_0

def sourceBody485_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_143 sourceBody485_145

def sourceBody485_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_146 sourceBody485_0

def sourceBody485_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_142 sourceBody485_147

def sourceBody485_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_148

def sourceBody485_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_141 sourceBody485_149

def sourceBody485_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_150

def sourceBody485_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 104#64])

def sourceBody485_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody485_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_153 sourceBody485_147

def sourceBody485_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_154

def sourceBody485_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_152 sourceBody485_155

def sourceBody485_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_156

def sourceBody485_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_151 sourceBody485_157

def sourceBody485_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 112#64])

def sourceBody485_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody485_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_160 sourceBody485_147

def sourceBody485_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_161

def sourceBody485_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_159 sourceBody485_162

def sourceBody485_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_163

def sourceBody485_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_158 sourceBody485_164

def sourceBody485_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody485_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody485_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody485_169 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 18)) (some 183) ([12, 24]) (some (12, sourceBody485_168, 485, 19))

def sourceBody485_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_169 sourceBody485_3

def sourceBody485_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_170 sourceBody485_0

def sourceBody485_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_167 sourceBody485_171

def sourceBody485_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_166 sourceBody485_172

def sourceBody485_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 136#64])

def sourceBody485_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody485_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 24)

def sourceBody485_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 8

def sourceBody485_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_177 sourceBody485_0

def sourceBody485_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_176 sourceBody485_178

def sourceBody485_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_179 sourceBody485_0

def sourceBody485_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_175 sourceBody485_180

def sourceBody485_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_181

def sourceBody485_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_174 sourceBody485_182

def sourceBody485_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_183

def sourceBody485_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 168#64])

def sourceBody485_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody485_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_186 sourceBody485_180

def sourceBody485_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_187

def sourceBody485_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_185 sourceBody485_188

def sourceBody485_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_189

def sourceBody485_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_184 sourceBody485_190

def sourceBody485_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 176#64])

def sourceBody485_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody485_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_193 sourceBody485_180

def sourceBody485_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_194

def sourceBody485_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_192 sourceBody485_195

def sourceBody485_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_196

def sourceBody485_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_191 sourceBody485_197

def sourceBody485_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody485_200 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 20)) (some 195) ([24]) (some (24, sourceBody485_199, 485, 21))

def sourceBody485_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_200 sourceBody485_3

def sourceBody485_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_201 sourceBody485_0

def sourceBody485_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_186 sourceBody485_202

def sourceBody485_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 264#64])

def sourceBody485_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody485_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody485_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 20

def sourceBody485_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_207 sourceBody485_0

def sourceBody485_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_206 sourceBody485_208

def sourceBody485_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_209 sourceBody485_0

def sourceBody485_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_205 sourceBody485_210

def sourceBody485_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_211

def sourceBody485_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_204 sourceBody485_212

def sourceBody485_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_213

def sourceBody485_215 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody485_0, 485, 22)) (some 195) ([24]) (some (24, sourceBody485_199, 485, 23))

def sourceBody485_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_215 sourceBody485_3

def sourceBody485_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_216 sourceBody485_0

def sourceBody485_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_193 sourceBody485_217

def sourceBody485_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_214 sourceBody485_218

def sourceBody485_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 272#64])

def sourceBody485_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_220 sourceBody485_212

def sourceBody485_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_221

def sourceBody485_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_219 sourceBody485_222

def sourceBody485_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 120#64])

def sourceBody485_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody485_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_225 sourceBody485_210

def sourceBody485_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_226

def sourceBody485_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_224 sourceBody485_227

def sourceBody485_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_228

def sourceBody485_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_223 sourceBody485_229

def sourceBody485_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 144#64])

def sourceBody485_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_231 sourceBody485_227

def sourceBody485_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_232

def sourceBody485_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_230 sourceBody485_233

def sourceBody485_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 216#64])

def sourceBody485_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody485_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_236 sourceBody485_210

def sourceBody485_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_237

def sourceBody485_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_235 sourceBody485_238

def sourceBody485_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_239

def sourceBody485_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_234 sourceBody485_240

def sourceBody485_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody485_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody485_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_243 sourceBody485_0

def sourceBody485_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_242 sourceBody485_244

def sourceBody485_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_241 sourceBody485_245

def sourceBody485_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_203 sourceBody485_246

def sourceBody485_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_247

def sourceBody485_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_248

def sourceBody485_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_198 sourceBody485_249

def sourceBody485_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_173 sourceBody485_250

def sourceBody485_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_251

def sourceBody485_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_252

def sourceBody485_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_165 sourceBody485_253

def sourceBody485_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_140 sourceBody485_254

def sourceBody485_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_255

def sourceBody485_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_256

def sourceBody485_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_132 sourceBody485_257

def sourceBody485_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_121 sourceBody485_258

def sourceBody485_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_259

def sourceBody485_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_260

def sourceBody485_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_114 sourceBody485_261

def sourceBody485_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_61 sourceBody485_262

def sourceBody485_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_263

def sourceBody485_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_264

def sourceBody485_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_55 sourceBody485_265

def sourceBody485_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_30 sourceBody485_266

def sourceBody485_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_267

def sourceBody485_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_268

def sourceBody485_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_25 sourceBody485_269

def sourceBody485_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_15 sourceBody485_270

def sourceBody485_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_271

def sourceBody485_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_272

def sourceBody485_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_9 sourceBody485_273

def sourceBody485_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_274

def sourceBody485_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_275

def sourceBody485_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_5 sourceBody485_276

def sourceBody485_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_277

def sourceBody485_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody485_0 sourceBody485_278

def source485 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (485, 2, sourceBody485_279)
end InitECandidate.Proofs.WordStages
