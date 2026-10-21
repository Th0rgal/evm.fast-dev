import InitECandidate.Proofs.WordStages.Source246
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody262_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody262_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody262_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody262_0, 262, 2)) (some 69) ([]) (some (8, sourceBody262_1, 262, 3))

def sourceBody262_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody262_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_2 sourceBody262_3

def sourceBody262_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_4 sourceBody262_0

def sourceBody262_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody262_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody262_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody262_0, 262, 4)) (some 68) ([16]) (some (16, sourceBody262_7, 262, 5))

def sourceBody262_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_8 sourceBody262_3

def sourceBody262_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_9 sourceBody262_0

def sourceBody262_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_6 sourceBody262_10

def sourceBody262_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody262_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody262_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody262_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody262_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody262_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody262_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody262_0, 262, 6)) (some 261) ([12, 20, 6, 14, 10]) (some (12, sourceBody262_17, 262, 7))

def sourceBody262_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_18 sourceBody262_3

def sourceBody262_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_19 sourceBody262_0

def sourceBody262_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_16 sourceBody262_20

def sourceBody262_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_15 sourceBody262_21

def sourceBody262_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_14 sourceBody262_22

def sourceBody262_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_13 sourceBody262_23

def sourceBody262_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_12 sourceBody262_24

def sourceBody262_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_25

def sourceBody262_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_26

def sourceBody262_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody262_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody262_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody262_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 76#64)

def sourceBody262_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody262_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody262_0, 262, 8)) (some 261) ([12, 20, 6, 14, 10]) (some (12, sourceBody262_17, 262, 9))

def sourceBody262_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_33 sourceBody262_3

def sourceBody262_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_34 sourceBody262_0

def sourceBody262_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_32 sourceBody262_35

def sourceBody262_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_31 sourceBody262_36

def sourceBody262_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_30 sourceBody262_37

def sourceBody262_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_29 sourceBody262_38

def sourceBody262_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_28 sourceBody262_39

def sourceBody262_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_40

def sourceBody262_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_41

def sourceBody262_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_27 sourceBody262_42

def sourceBody262_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody262_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody262_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody262_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 116#64)

def sourceBody262_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody262_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody262_0, 262, 10)) (some 261) ([12, 20, 6, 14, 10]) (some (12, sourceBody262_17, 262, 11))

def sourceBody262_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_49 sourceBody262_3

def sourceBody262_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_50 sourceBody262_0

def sourceBody262_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_48 sourceBody262_51

def sourceBody262_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_47 sourceBody262_52

def sourceBody262_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_46 sourceBody262_53

def sourceBody262_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_45 sourceBody262_54

def sourceBody262_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_44 sourceBody262_55

def sourceBody262_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_56

def sourceBody262_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_57

def sourceBody262_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_43 sourceBody262_58

def sourceBody262_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody262_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody262_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody262_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 184#64)

def sourceBody262_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody262_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody262_0, 262, 12)) (some 261) ([12, 20, 6, 14, 10]) (some (12, sourceBody262_17, 262, 13))

def sourceBody262_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_65 sourceBody262_3

def sourceBody262_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_66 sourceBody262_0

def sourceBody262_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_64 sourceBody262_67

def sourceBody262_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_63 sourceBody262_68

def sourceBody262_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_62 sourceBody262_69

def sourceBody262_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_61 sourceBody262_70

def sourceBody262_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_60 sourceBody262_71

def sourceBody262_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_72

def sourceBody262_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_73

def sourceBody262_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_59 sourceBody262_74

def sourceBody262_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody262_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody262_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody262_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 68#64)

def sourceBody262_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody262_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody262_0, 262, 14)) (some 261) ([12, 20, 6, 14, 10]) (some (12, sourceBody262_17, 262, 15))

def sourceBody262_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_81 sourceBody262_3

def sourceBody262_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_82 sourceBody262_0

def sourceBody262_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_80 sourceBody262_83

def sourceBody262_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_79 sourceBody262_84

def sourceBody262_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_78 sourceBody262_85

def sourceBody262_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_77 sourceBody262_86

def sourceBody262_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_76 sourceBody262_87

def sourceBody262_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_88

def sourceBody262_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_89

def sourceBody262_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_75 sourceBody262_90

def sourceBody262_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody262_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody262_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody262_95 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody262_0, 262, 16)) (some 240) ([12, 20, 6]) (some (12, sourceBody262_17, 262, 17))

def sourceBody262_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_95 sourceBody262_3

def sourceBody262_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_96 sourceBody262_0

def sourceBody262_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_94 sourceBody262_97

def sourceBody262_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_93 sourceBody262_98

def sourceBody262_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_92 sourceBody262_99

def sourceBody262_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_100

def sourceBody262_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_101

def sourceBody262_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_91 sourceBody262_102

def sourceBody262_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody262_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody262_0, 262, 18)) (some 70) ([12]) (some (12, sourceBody262_17, 262, 19))

def sourceBody262_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_105 sourceBody262_3

def sourceBody262_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_106 sourceBody262_0

def sourceBody262_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_104 sourceBody262_107

def sourceBody262_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_108

def sourceBody262_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_109

def sourceBody262_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_103 sourceBody262_110

def sourceBody262_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody262_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody262_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_113 sourceBody262_0

def sourceBody262_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_112 sourceBody262_114

def sourceBody262_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_111 sourceBody262_115

def sourceBody262_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_11 sourceBody262_116

def sourceBody262_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_117

def sourceBody262_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_118

def sourceBody262_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_5 sourceBody262_119

def sourceBody262_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_120

def sourceBody262_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody262_0 sourceBody262_121

def source262 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (262, 3, sourceBody262_122)
end InitECandidate.Proofs.WordStages
