import InitECandidate.Proofs.WordStages.Source828
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody844_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody844_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody844_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody844_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody844_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 20) sourceBody844_2 sourceBody844_3

def sourceBody844_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody844_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_4 sourceBody844_5

def sourceBody844_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody844_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody844_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 60#64)

def sourceBody844_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 12)

def sourceBody844_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_10 sourceBody844_8

def sourceBody844_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_11 sourceBody844_8

def sourceBody844_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_9 sourceBody844_12

def sourceBody844_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_13

def sourceBody844_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody844_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody844_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_15 sourceBody844_16

def sourceBody844_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_14 sourceBody844_17

def sourceBody844_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody844_18 sourceBody844_8

def sourceBody844_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_19 sourceBody844_5

def sourceBody844_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_20 sourceBody844_8

def sourceBody844_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_7 sourceBody844_21

def sourceBody844_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_6 sourceBody844_22

def sourceBody844_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_1 sourceBody844_23

def sourceBody844_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_0 sourceBody844_24

def sourceBody844_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody844_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 2)) (some 69) ([]) (some (28, sourceBody844_26, 844, 3))

def sourceBody844_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_27 sourceBody844_5

def sourceBody844_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_28 sourceBody844_8

def sourceBody844_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody844_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody844_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody844_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 4)) (some 80) ([34, 10]) (some (34, sourceBody844_32, 844, 5))

def sourceBody844_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_33 sourceBody844_5

def sourceBody844_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_34 sourceBody844_8

def sourceBody844_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_31 sourceBody844_35

def sourceBody844_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_30 sourceBody844_36

def sourceBody844_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody844_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody844_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 6)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 7))

def sourceBody844_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_40 sourceBody844_5

def sourceBody844_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_41 sourceBody844_8

def sourceBody844_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_38 sourceBody844_42

def sourceBody844_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody844_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody844_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 8)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 9))

def sourceBody844_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_46 sourceBody844_5

def sourceBody844_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_47 sourceBody844_8

def sourceBody844_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_48

def sourceBody844_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_44 sourceBody844_49

def sourceBody844_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody844_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody844_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody844_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody844_55 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 32) sourceBody844_53 sourceBody844_54

def sourceBody844_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_55 sourceBody844_5

def sourceBody844_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody844_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody844_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody844_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody844_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 22) sourceBody844_59 sourceBody844_60

def sourceBody844_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_61 sourceBody844_5

def sourceBody844_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody844_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 30])

def sourceBody844_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody844_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 24) sourceBody844_65 sourceBody844_63

def sourceBody844_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_66 sourceBody844_5

def sourceBody844_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody844_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_3 sourceBody844_8

def sourceBody844_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_69 sourceBody844_8

def sourceBody844_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody844_70 sourceBody844_8

def sourceBody844_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_71 sourceBody844_5

def sourceBody844_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_72 sourceBody844_8

def sourceBody844_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_68 sourceBody844_73

def sourceBody844_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_67 sourceBody844_74

def sourceBody844_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_64 sourceBody844_75

def sourceBody844_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_63 sourceBody844_76

def sourceBody844_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_62 sourceBody844_77

def sourceBody844_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_58 sourceBody844_78

def sourceBody844_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_79

def sourceBody844_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_80

def sourceBody844_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_81

def sourceBody844_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_82

def sourceBody844_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_50 sourceBody844_83

def sourceBody844_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody844_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 10)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 11))

def sourceBody844_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_86 sourceBody844_5

def sourceBody844_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_87 sourceBody844_8

def sourceBody844_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_88

def sourceBody844_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_85 sourceBody844_89

def sourceBody844_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_84 sourceBody844_90

def sourceBody844_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody844_93 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 12)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 13))

def sourceBody844_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_93 sourceBody844_5

def sourceBody844_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_94 sourceBody844_8

def sourceBody844_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_92 sourceBody844_95

def sourceBody844_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_91 sourceBody844_96

def sourceBody844_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody844_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_98 sourceBody844_78

def sourceBody844_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_99

def sourceBody844_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_100

def sourceBody844_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_101

def sourceBody844_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_102

def sourceBody844_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_97 sourceBody844_103

def sourceBody844_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody844_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 14)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 15))

def sourceBody844_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_106 sourceBody844_5

def sourceBody844_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_107 sourceBody844_8

def sourceBody844_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_108

def sourceBody844_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_105 sourceBody844_109

def sourceBody844_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_104 sourceBody844_110

def sourceBody844_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody844_113 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 16)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 17))

def sourceBody844_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_113 sourceBody844_5

def sourceBody844_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_114 sourceBody844_8

def sourceBody844_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_112 sourceBody844_115

def sourceBody844_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_111 sourceBody844_116

def sourceBody844_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 320#64)

def sourceBody844_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_118 sourceBody844_78

def sourceBody844_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_119

def sourceBody844_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_120

def sourceBody844_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_121

def sourceBody844_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_122

def sourceBody844_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_117 sourceBody844_123

def sourceBody844_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody844_126 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 18)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 19))

def sourceBody844_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_126 sourceBody844_5

def sourceBody844_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_127 sourceBody844_8

def sourceBody844_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_128

def sourceBody844_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_125 sourceBody844_129

def sourceBody844_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_124 sourceBody844_130

def sourceBody844_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 120#64])

def sourceBody844_133 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 20)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 21))

def sourceBody844_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_133 sourceBody844_5

def sourceBody844_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_134 sourceBody844_8

def sourceBody844_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_132 sourceBody844_135

def sourceBody844_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_131 sourceBody844_136

def sourceBody844_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody844_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_138 sourceBody844_78

def sourceBody844_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_139

def sourceBody844_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_140

def sourceBody844_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_141

def sourceBody844_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_142

def sourceBody844_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_137 sourceBody844_143

def sourceBody844_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody844_146 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 22)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 23))

def sourceBody844_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_146 sourceBody844_5

def sourceBody844_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_147 sourceBody844_8

def sourceBody844_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_148

def sourceBody844_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_145 sourceBody844_149

def sourceBody844_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_144 sourceBody844_150

def sourceBody844_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 152#64])

def sourceBody844_153 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 24)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 25))

def sourceBody844_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_153 sourceBody844_5

def sourceBody844_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_154 sourceBody844_8

def sourceBody844_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_152 sourceBody844_155

def sourceBody844_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_151 sourceBody844_156

def sourceBody844_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 512#64)

def sourceBody844_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_158 sourceBody844_78

def sourceBody844_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_159

def sourceBody844_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_160

def sourceBody844_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_161

def sourceBody844_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_162

def sourceBody844_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_157 sourceBody844_163

def sourceBody844_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody844_166 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 26)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 27))

def sourceBody844_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_166 sourceBody844_5

def sourceBody844_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_167 sourceBody844_8

def sourceBody844_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_168

def sourceBody844_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_165 sourceBody844_169

def sourceBody844_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_164 sourceBody844_170

def sourceBody844_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 184#64])

def sourceBody844_173 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 28)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 29))

def sourceBody844_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_173 sourceBody844_5

def sourceBody844_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_174 sourceBody844_8

def sourceBody844_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_172 sourceBody844_175

def sourceBody844_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_171 sourceBody844_176

def sourceBody844_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody844_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_178 sourceBody844_78

def sourceBody844_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_179

def sourceBody844_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_180

def sourceBody844_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_181

def sourceBody844_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_182

def sourceBody844_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_177 sourceBody844_183

def sourceBody844_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 256#64])

def sourceBody844_186 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 30)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 31))

def sourceBody844_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_186 sourceBody844_5

def sourceBody844_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_187 sourceBody844_8

def sourceBody844_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_188

def sourceBody844_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_185 sourceBody844_189

def sourceBody844_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_184 sourceBody844_190

def sourceBody844_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 280#64])

def sourceBody844_193 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 32)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 33))

def sourceBody844_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_193 sourceBody844_5

def sourceBody844_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_194 sourceBody844_8

def sourceBody844_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_192 sourceBody844_195

def sourceBody844_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_191 sourceBody844_196

def sourceBody844_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody844_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_198 sourceBody844_78

def sourceBody844_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_199

def sourceBody844_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_200

def sourceBody844_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_201

def sourceBody844_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_202

def sourceBody844_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_197 sourceBody844_203

def sourceBody844_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64])

def sourceBody844_206 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 34)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 35))

def sourceBody844_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_206 sourceBody844_5

def sourceBody844_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_207 sourceBody844_8

def sourceBody844_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_208

def sourceBody844_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_205 sourceBody844_209

def sourceBody844_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_204 sourceBody844_210

def sourceBody844_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 344#64])

def sourceBody844_213 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 36)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 37))

def sourceBody844_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_213 sourceBody844_5

def sourceBody844_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_214 sourceBody844_8

def sourceBody844_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_212 sourceBody844_215

def sourceBody844_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_211 sourceBody844_216

def sourceBody844_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody844_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_218 sourceBody844_78

def sourceBody844_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_219

def sourceBody844_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_220

def sourceBody844_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_221

def sourceBody844_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_222

def sourceBody844_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_217 sourceBody844_223

def sourceBody844_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody844_226 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 38)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 39))

def sourceBody844_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_226 sourceBody844_5

def sourceBody844_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_227 sourceBody844_8

def sourceBody844_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_228

def sourceBody844_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_225 sourceBody844_229

def sourceBody844_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_224 sourceBody844_230

def sourceBody844_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 408#64])

def sourceBody844_233 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 40)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 41))

def sourceBody844_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_233 sourceBody844_5

def sourceBody844_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_234 sourceBody844_8

def sourceBody844_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_232 sourceBody844_235

def sourceBody844_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_231 sourceBody844_236

def sourceBody844_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody844_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_238 sourceBody844_78

def sourceBody844_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_57 sourceBody844_239

def sourceBody844_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_240

def sourceBody844_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_241

def sourceBody844_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_51 sourceBody844_242

def sourceBody844_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_237 sourceBody844_243

def sourceBody844_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 512#64])

def sourceBody844_246 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 42)) (some 80) ([26, 18]) (some (26, sourceBody844_39, 844, 43))

def sourceBody844_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_246 sourceBody844_5

def sourceBody844_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_247 sourceBody844_8

def sourceBody844_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_45 sourceBody844_248

def sourceBody844_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_245 sourceBody844_249

def sourceBody844_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_244 sourceBody844_250

def sourceBody844_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 536#64])

def sourceBody844_253 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 44)) (some 85) ([26]) (some (26, sourceBody844_39, 844, 45))

def sourceBody844_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_253 sourceBody844_5

def sourceBody844_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_254 sourceBody844_8

def sourceBody844_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_252 sourceBody844_255

def sourceBody844_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_251 sourceBody844_256

def sourceBody844_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_257 sourceBody844_223

def sourceBody844_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody844_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody844_261 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 46)) (some 70) ([18]) (some (18, sourceBody844_260, 844, 47))

def sourceBody844_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_261 sourceBody844_5

def sourceBody844_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_262 sourceBody844_8

def sourceBody844_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_259 sourceBody844_263

def sourceBody844_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_264

def sourceBody844_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_265

def sourceBody844_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_258 sourceBody844_266

def sourceBody844_268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody844_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody844_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 61#64)

def sourceBody844_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 26)

def sourceBody844_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_271 sourceBody844_8

def sourceBody844_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_272 sourceBody844_8

def sourceBody844_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_270 sourceBody844_273

def sourceBody844_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_274

def sourceBody844_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody844_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_276 sourceBody844_39

def sourceBody844_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_275 sourceBody844_277

def sourceBody844_279 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody844_278 sourceBody844_8

def sourceBody844_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_279 sourceBody844_5

def sourceBody844_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_280 sourceBody844_8

def sourceBody844_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_269 sourceBody844_281

def sourceBody844_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_56 sourceBody844_282

def sourceBody844_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_52 sourceBody844_283

def sourceBody844_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_268 sourceBody844_284

def sourceBody844_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_267 sourceBody844_285

def sourceBody844_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody844_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody844_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody844_290 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 48)) (some 77) ([18, 32, 14]) (some (18, sourceBody844_260, 844, 49))

def sourceBody844_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_290 sourceBody844_5

def sourceBody844_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_291 sourceBody844_8

def sourceBody844_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_289 sourceBody844_292

def sourceBody844_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_288 sourceBody844_293

def sourceBody844_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_287 sourceBody844_294

def sourceBody844_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_295

def sourceBody844_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_296

def sourceBody844_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_286 sourceBody844_297

def sourceBody844_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody844_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody844_301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody844_302 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 50)) (some 77) ([18, 32, 14]) (some (18, sourceBody844_260, 844, 51))

def sourceBody844_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_302 sourceBody844_5

def sourceBody844_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_303 sourceBody844_8

def sourceBody844_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_301 sourceBody844_304

def sourceBody844_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_300 sourceBody844_305

def sourceBody844_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_299 sourceBody844_306

def sourceBody844_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_307

def sourceBody844_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_308

def sourceBody844_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_298 sourceBody844_309

def sourceBody844_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody844_312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64])

def sourceBody844_313 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody844_314 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 52)) (some 77) ([18, 32, 14]) (some (18, sourceBody844_260, 844, 53))

def sourceBody844_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_314 sourceBody844_5

def sourceBody844_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_315 sourceBody844_8

def sourceBody844_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_313 sourceBody844_316

def sourceBody844_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_312 sourceBody844_317

def sourceBody844_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_311 sourceBody844_318

def sourceBody844_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_319

def sourceBody844_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_320

def sourceBody844_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_310 sourceBody844_321

def sourceBody844_323 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody844_324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 416#64])

def sourceBody844_325 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody844_326 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody844_8, 844, 54)) (some 77) ([18, 32, 14]) (some (18, sourceBody844_260, 844, 55))

def sourceBody844_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_326 sourceBody844_5

def sourceBody844_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_327 sourceBody844_8

def sourceBody844_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_325 sourceBody844_328

def sourceBody844_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_324 sourceBody844_329

def sourceBody844_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_323 sourceBody844_330

def sourceBody844_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_331

def sourceBody844_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_332

def sourceBody844_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_322 sourceBody844_333

def sourceBody844_335 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 184#64])

def sourceBody844_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 544#64])

def sourceBody844_337 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody844_8, 844, 56)) (some 77) ([18, 32, 14]) (some (18, sourceBody844_260, 844, 57))

def sourceBody844_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_337 sourceBody844_5

def sourceBody844_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_338 sourceBody844_8

def sourceBody844_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_313 sourceBody844_339

def sourceBody844_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_336 sourceBody844_340

def sourceBody844_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_335 sourceBody844_341

def sourceBody844_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_342

def sourceBody844_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_343

def sourceBody844_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_334 sourceBody844_344

def sourceBody844_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody844_347 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody844_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_347 sourceBody844_8

def sourceBody844_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_346 sourceBody844_348

def sourceBody844_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_345 sourceBody844_349

def sourceBody844_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_43 sourceBody844_350

def sourceBody844_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_351

def sourceBody844_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_352

def sourceBody844_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_353

def sourceBody844_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_354

def sourceBody844_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_37 sourceBody844_355

def sourceBody844_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_356

def sourceBody844_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_357

def sourceBody844_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_2 sourceBody844_358

def sourceBody844_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_359

def sourceBody844_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_29 sourceBody844_360

def sourceBody844_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_361

def sourceBody844_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_8 sourceBody844_362

def sourceBody844_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody844_25 sourceBody844_363

def source844 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (844, 4, sourceBody844_364)
end InitECandidate.Proofs.WordStages
