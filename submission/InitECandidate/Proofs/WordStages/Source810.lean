import InitECandidate.Proofs.WordStages.Source794
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody810_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody810_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody810_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 2)) (some 69) ([]) (some (28, sourceBody810_1, 810, 3))

def sourceBody810_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody810_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_2 sourceBody810_3

def sourceBody810_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_4 sourceBody810_0

def sourceBody810_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody810_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody810_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 4)) (some 68) ([20]) (some (20, sourceBody810_7, 810, 5))

def sourceBody810_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_8 sourceBody810_3

def sourceBody810_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_9 sourceBody810_0

def sourceBody810_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_6 sourceBody810_10

def sourceBody810_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody810_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody810_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 6)) (some 68) ([34]) (some (34, sourceBody810_13, 810, 7))

def sourceBody810_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_14 sourceBody810_3

def sourceBody810_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_15 sourceBody810_0

def sourceBody810_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_12 sourceBody810_16

def sourceBody810_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody810_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody810_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 8)) (some 68) ([10]) (some (10, sourceBody810_19, 810, 9))

def sourceBody810_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_20 sourceBody810_3

def sourceBody810_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_21 sourceBody810_0

def sourceBody810_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_18 sourceBody810_22

def sourceBody810_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody810_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody810_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 10)) (some 752) ([26]) (some (26, sourceBody810_25, 810, 11))

def sourceBody810_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_26 sourceBody810_3

def sourceBody810_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_27 sourceBody810_0

def sourceBody810_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_24 sourceBody810_28

def sourceBody810_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_29

def sourceBody810_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_30

def sourceBody810_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody810_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody810_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 4)

def sourceBody810_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody810_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody810_37 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 18 (Flapjack.WordRegImm.reg 32) sourceBody810_35 sourceBody810_36

def sourceBody810_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_37 sourceBody810_3

def sourceBody810_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody810_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody810_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody810_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 32 32 26 18))

def sourceBody810_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_42 sourceBody810_0

def sourceBody810_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_41 sourceBody810_43

def sourceBody810_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_40 sourceBody810_44

def sourceBody810_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 32])

def sourceBody810_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody810_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 28)

def sourceBody810_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody810_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 12)) (some 771) ([22, 36]) (some (22, sourceBody810_49, 810, 13))

def sourceBody810_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_50 sourceBody810_3

def sourceBody810_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_51 sourceBody810_0

def sourceBody810_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_48 sourceBody810_52

def sourceBody810_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_47 sourceBody810_53

def sourceBody810_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 30)

def sourceBody810_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody810_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody810_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody810_59 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 36 (Flapjack.WordRegImm.reg 8) sourceBody810_57 sourceBody810_58

def sourceBody810_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_59 sourceBody810_3

def sourceBody810_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody810_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 12)

def sourceBody810_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody810_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody810_0, 810, 14)) (some 70) ([36]) (some (36, sourceBody810_63, 810, 15))

def sourceBody810_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_64 sourceBody810_3

def sourceBody810_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_65 sourceBody810_0

def sourceBody810_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_62 sourceBody810_66

def sourceBody810_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_67

def sourceBody810_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_68

def sourceBody810_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody810_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody810_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_71 sourceBody810_0

def sourceBody810_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_70 sourceBody810_72

def sourceBody810_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_69 sourceBody810_73

def sourceBody810_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody810_74 sourceBody810_0

def sourceBody810_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_75 sourceBody810_3

def sourceBody810_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_76 sourceBody810_0

def sourceBody810_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_61 sourceBody810_77

def sourceBody810_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_60 sourceBody810_78

def sourceBody810_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_56 sourceBody810_79

def sourceBody810_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_55 sourceBody810_80

def sourceBody810_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 16)) (some 773) ([36]) (some (36, sourceBody810_63, 810, 17))

def sourceBody810_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_82 sourceBody810_3

def sourceBody810_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_83 sourceBody810_0

def sourceBody810_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_48 sourceBody810_84

def sourceBody810_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 22)

def sourceBody810_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody810_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody810_89 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 24) sourceBody810_88 sourceBody810_56

def sourceBody810_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_89 sourceBody810_3

def sourceBody810_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody810_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody810_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody810_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody810_0, 810, 18)) (some 70) ([8]) (some (8, sourceBody810_93, 810, 19))

def sourceBody810_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_94 sourceBody810_3

def sourceBody810_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_95 sourceBody810_0

def sourceBody810_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_92 sourceBody810_96

def sourceBody810_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_97

def sourceBody810_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_98

def sourceBody810_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody810_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_100 sourceBody810_0

def sourceBody810_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_57 sourceBody810_101

def sourceBody810_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_99 sourceBody810_102

def sourceBody810_104 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody810_103 sourceBody810_0

def sourceBody810_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_104 sourceBody810_3

def sourceBody810_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_105 sourceBody810_0

def sourceBody810_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_91 sourceBody810_106

def sourceBody810_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_90 sourceBody810_107

def sourceBody810_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_87 sourceBody810_108

def sourceBody810_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_86 sourceBody810_109

def sourceBody810_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody810_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody810_113 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 20)) (some 783) ([36, 8]) (some (36, sourceBody810_63, 810, 21))

def sourceBody810_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_113 sourceBody810_3

def sourceBody810_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_114 sourceBody810_0

def sourceBody810_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_112 sourceBody810_115

def sourceBody810_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_111 sourceBody810_116

def sourceBody810_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_110 sourceBody810_117

def sourceBody810_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 30)

def sourceBody810_120 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody810_0, 810, 22)) (some 70) ([8]) (some (8, sourceBody810_93, 810, 23))

def sourceBody810_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_120 sourceBody810_3

def sourceBody810_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_121 sourceBody810_0

def sourceBody810_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_92 sourceBody810_122

def sourceBody810_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_123

def sourceBody810_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_124

def sourceBody810_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_125 sourceBody810_102

def sourceBody810_127 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody810_126 sourceBody810_0

def sourceBody810_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_127 sourceBody810_3

def sourceBody810_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_128 sourceBody810_0

def sourceBody810_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_91 sourceBody810_129

def sourceBody810_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_90 sourceBody810_130

def sourceBody810_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_87 sourceBody810_131

def sourceBody810_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_119 sourceBody810_132

def sourceBody810_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_118 sourceBody810_133

def sourceBody810_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody810_136 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 24)) (some 785) ([36]) (some (36, sourceBody810_63, 810, 25))

def sourceBody810_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_136 sourceBody810_3

def sourceBody810_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_137 sourceBody810_0

def sourceBody810_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_135 sourceBody810_138

def sourceBody810_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_134 sourceBody810_139

def sourceBody810_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody810_0, 810, 26)) (some 70) ([8]) (some (8, sourceBody810_93, 810, 27))

def sourceBody810_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_141 sourceBody810_3

def sourceBody810_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_142 sourceBody810_0

def sourceBody810_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_92 sourceBody810_143

def sourceBody810_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_144

def sourceBody810_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_145

def sourceBody810_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_146 sourceBody810_102

def sourceBody810_148 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody810_147 sourceBody810_0

def sourceBody810_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_148 sourceBody810_3

def sourceBody810_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_149 sourceBody810_0

def sourceBody810_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_91 sourceBody810_150

def sourceBody810_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_90 sourceBody810_151

def sourceBody810_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_87 sourceBody810_152

def sourceBody810_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_86 sourceBody810_153

def sourceBody810_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_140 sourceBody810_154

def sourceBody810_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 34)

def sourceBody810_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody810_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody810_159 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 28)) (some 790) ([8, 24, 16]) (some (8, sourceBody810_93, 810, 29))

def sourceBody810_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_159 sourceBody810_3

def sourceBody810_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_160 sourceBody810_0

def sourceBody810_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_158 sourceBody810_161

def sourceBody810_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_157 sourceBody810_162

def sourceBody810_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_156 sourceBody810_163

def sourceBody810_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_164

def sourceBody810_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_165

def sourceBody810_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_155 sourceBody810_166

def sourceBody810_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody810_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 36)

def sourceBody810_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_169 sourceBody810_0

def sourceBody810_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_170 sourceBody810_0

def sourceBody810_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_168 sourceBody810_171

def sourceBody810_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_172

def sourceBody810_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_167 sourceBody810_173

def sourceBody810_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_85 sourceBody810_174

def sourceBody810_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_175

def sourceBody810_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_176

def sourceBody810_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_81 sourceBody810_177

def sourceBody810_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_54 sourceBody810_178

def sourceBody810_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_179

def sourceBody810_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_180

def sourceBody810_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_46 sourceBody810_181

def sourceBody810_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_45 sourceBody810_182

def sourceBody810_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody810_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_183 sourceBody810_184

def sourceBody810_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody810_187 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody810_185 sourceBody810_186

def sourceBody810_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_187 sourceBody810_3

def sourceBody810_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_188 sourceBody810_0

def sourceBody810_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_39 sourceBody810_189

def sourceBody810_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_38 sourceBody810_190

def sourceBody810_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_34 sourceBody810_191

def sourceBody810_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_33 sourceBody810_192

def sourceBody810_194 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody810_193 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody810_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_194 sourceBody810_3

def sourceBody810_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_3 sourceBody810_195

def sourceBody810_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 34)

def sourceBody810_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 34)

def sourceBody810_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody810_200 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 30)) (some 761) ([18, 32]) (some (18, sourceBody810_199, 810, 31))

def sourceBody810_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_200 sourceBody810_3

def sourceBody810_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_201 sourceBody810_0

def sourceBody810_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_198 sourceBody810_202

def sourceBody810_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_197 sourceBody810_203

def sourceBody810_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_204

def sourceBody810_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_205

def sourceBody810_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_196 sourceBody810_206

def sourceBody810_208 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 32)) (some 753) ([18]) (some (18, sourceBody810_199, 810, 33))

def sourceBody810_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_208 sourceBody810_3

def sourceBody810_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_209 sourceBody810_0

def sourceBody810_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_197 sourceBody810_210

def sourceBody810_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 6)

def sourceBody810_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody810_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody810_215 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody810_0, 810, 34)) (some 78) ([32, 14]) (some (32, sourceBody810_214, 810, 35))

def sourceBody810_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_215 sourceBody810_3

def sourceBody810_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_216 sourceBody810_0

def sourceBody810_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_213 sourceBody810_217

def sourceBody810_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_212 sourceBody810_218

def sourceBody810_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_219

def sourceBody810_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_220

def sourceBody810_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 31#64])

def sourceBody810_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody810_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 32 (Flapjack.WordLangAddr.addr 18 0#64))

def sourceBody810_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_224 sourceBody810_0

def sourceBody810_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_223 sourceBody810_225

def sourceBody810_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_222 sourceBody810_226

def sourceBody810_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_221 sourceBody810_227

def sourceBody810_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody810_230 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody810_0, 810, 36)) (some 70) ([32]) (some (32, sourceBody810_214, 810, 37))

def sourceBody810_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_230 sourceBody810_3

def sourceBody810_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_231 sourceBody810_0

def sourceBody810_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_229 sourceBody810_232

def sourceBody810_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_233

def sourceBody810_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_234

def sourceBody810_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_228 sourceBody810_235

def sourceBody810_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody810_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_237 sourceBody810_0

def sourceBody810_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_36 sourceBody810_238

def sourceBody810_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_236 sourceBody810_239

def sourceBody810_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_211 sourceBody810_240

def sourceBody810_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_241

def sourceBody810_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_242

def sourceBody810_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_207 sourceBody810_243

def sourceBody810_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_32 sourceBody810_244

def sourceBody810_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_245

def sourceBody810_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_31 sourceBody810_246

def sourceBody810_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_23 sourceBody810_247

def sourceBody810_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_248

def sourceBody810_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_249

def sourceBody810_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_17 sourceBody810_250

def sourceBody810_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_251

def sourceBody810_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_252

def sourceBody810_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_11 sourceBody810_253

def sourceBody810_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_254

def sourceBody810_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_255

def sourceBody810_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_5 sourceBody810_256

def sourceBody810_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_257

def sourceBody810_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody810_0 sourceBody810_258

def source810 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (810, 4, sourceBody810_259)
end InitECandidate.Proofs.WordStages
