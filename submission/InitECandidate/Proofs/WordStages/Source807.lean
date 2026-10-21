import InitECandidate.Proofs.WordStages.Source791
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody807_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody807_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody807_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 2)) (some 69) ([]) (some (34, sourceBody807_1, 807, 3))

def sourceBody807_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody807_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_2 sourceBody807_3

def sourceBody807_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_4 sourceBody807_0

def sourceBody807_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody807_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody807_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 4)) (some 68) ([24]) (some (24, sourceBody807_7, 807, 5))

def sourceBody807_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_8 sourceBody807_3

def sourceBody807_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_9 sourceBody807_0

def sourceBody807_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_6 sourceBody807_10

def sourceBody807_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody807_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody807_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 6)) (some 68) ([44]) (some (44, sourceBody807_13, 807, 7))

def sourceBody807_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_14 sourceBody807_3

def sourceBody807_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_15 sourceBody807_0

def sourceBody807_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_12 sourceBody807_16

def sourceBody807_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody807_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody807_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 8)) (some 68) ([10]) (some (10, sourceBody807_19, 807, 9))

def sourceBody807_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_20 sourceBody807_3

def sourceBody807_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_21 sourceBody807_0

def sourceBody807_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_18 sourceBody807_22

def sourceBody807_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody807_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody807_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody807_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody807_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody807_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 22 (Flapjack.WordRegImm.reg 42) sourceBody807_27 sourceBody807_28

def sourceBody807_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_29 sourceBody807_3

def sourceBody807_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody807_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody807_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody807_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 42 42 32 22))

def sourceBody807_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_34 sourceBody807_0

def sourceBody807_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_33 sourceBody807_35

def sourceBody807_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_32 sourceBody807_36

def sourceBody807_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 42])

def sourceBody807_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 18)

def sourceBody807_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 24)

def sourceBody807_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody807_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 10)) (some 771) ([28, 48]) (some (28, sourceBody807_41, 807, 11))

def sourceBody807_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_42 sourceBody807_3

def sourceBody807_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_43 sourceBody807_0

def sourceBody807_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_40 sourceBody807_44

def sourceBody807_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_39 sourceBody807_45

def sourceBody807_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody807_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody807_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody807_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody807_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 48 (Flapjack.WordRegImm.reg 8) sourceBody807_49 sourceBody807_50

def sourceBody807_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_51 sourceBody807_3

def sourceBody807_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 48)

def sourceBody807_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 14)

def sourceBody807_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody807_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody807_0, 807, 12)) (some 70) ([48]) (some (48, sourceBody807_55, 807, 13))

def sourceBody807_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_56 sourceBody807_3

def sourceBody807_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_57 sourceBody807_0

def sourceBody807_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_54 sourceBody807_58

def sourceBody807_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_59

def sourceBody807_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_60

def sourceBody807_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody807_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody807_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_63 sourceBody807_0

def sourceBody807_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_62 sourceBody807_64

def sourceBody807_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_61 sourceBody807_65

def sourceBody807_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody807_66 sourceBody807_0

def sourceBody807_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_67 sourceBody807_3

def sourceBody807_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_68 sourceBody807_0

def sourceBody807_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_53 sourceBody807_69

def sourceBody807_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_52 sourceBody807_70

def sourceBody807_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_48 sourceBody807_71

def sourceBody807_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_47 sourceBody807_72

def sourceBody807_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 14)) (some 773) ([48]) (some (48, sourceBody807_55, 807, 15))

def sourceBody807_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_74 sourceBody807_3

def sourceBody807_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_75 sourceBody807_0

def sourceBody807_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_40 sourceBody807_76

def sourceBody807_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody807_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody807_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody807_81 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 30) sourceBody807_80 sourceBody807_48

def sourceBody807_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_81 sourceBody807_3

def sourceBody807_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody807_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody807_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody807_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody807_0, 807, 16)) (some 70) ([8]) (some (8, sourceBody807_85, 807, 17))

def sourceBody807_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_86 sourceBody807_3

def sourceBody807_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_87 sourceBody807_0

def sourceBody807_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_84 sourceBody807_88

def sourceBody807_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_89

def sourceBody807_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_90

def sourceBody807_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [48]

def sourceBody807_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_92 sourceBody807_0

def sourceBody807_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_49 sourceBody807_93

def sourceBody807_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_91 sourceBody807_94

def sourceBody807_96 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody807_95 sourceBody807_0

def sourceBody807_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_96 sourceBody807_3

def sourceBody807_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_97 sourceBody807_0

def sourceBody807_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_83 sourceBody807_98

def sourceBody807_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_82 sourceBody807_99

def sourceBody807_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_79 sourceBody807_100

def sourceBody807_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_78 sourceBody807_101

def sourceBody807_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody807_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody807_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody807_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 8, 30, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 18)) (some 146) ([40, 16]) (some (40, sourceBody807_105, 807, 19))

def sourceBody807_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_106 sourceBody807_3

def sourceBody807_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_107 sourceBody807_0

def sourceBody807_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_104 sourceBody807_108

def sourceBody807_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_103 sourceBody807_109

def sourceBody807_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 44)

def sourceBody807_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 48)

def sourceBody807_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 8)

def sourceBody807_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody807_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 20)

def sourceBody807_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody807_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 12

def sourceBody807_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_117 sourceBody807_0

def sourceBody807_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_116 sourceBody807_118

def sourceBody807_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody807_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64])
  12

def sourceBody807_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_121 sourceBody807_0

def sourceBody807_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_120 sourceBody807_122

def sourceBody807_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody807_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 16#64])
  12

def sourceBody807_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_125 sourceBody807_0

def sourceBody807_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_124 sourceBody807_126

def sourceBody807_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 46)

def sourceBody807_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 24#64])
  12

def sourceBody807_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_129 sourceBody807_0

def sourceBody807_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_128 sourceBody807_130

def sourceBody807_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_131 sourceBody807_0

def sourceBody807_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_127 sourceBody807_132

def sourceBody807_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_123 sourceBody807_133

def sourceBody807_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_119 sourceBody807_134

def sourceBody807_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_115 sourceBody807_135

def sourceBody807_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_136

def sourceBody807_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_114 sourceBody807_137

def sourceBody807_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_138

def sourceBody807_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_113 sourceBody807_139

def sourceBody807_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_140

def sourceBody807_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_112 sourceBody807_141

def sourceBody807_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_142

def sourceBody807_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_111 sourceBody807_143

def sourceBody807_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_144

def sourceBody807_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody807_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody807_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 44)

def sourceBody807_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody807_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody807_151 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 20)) (some 768) ([16, 36, 26, 46]) (some (16, sourceBody807_150, 807, 21))

def sourceBody807_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_151 sourceBody807_3

def sourceBody807_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_152 sourceBody807_0

def sourceBody807_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_149 sourceBody807_153

def sourceBody807_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_148 sourceBody807_154

def sourceBody807_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_147 sourceBody807_155

def sourceBody807_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_146 sourceBody807_156

def sourceBody807_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_157

def sourceBody807_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_158

def sourceBody807_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_145 sourceBody807_159

def sourceBody807_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody807_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody807_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody807_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody807_165 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 36) sourceBody807_163 sourceBody807_164

def sourceBody807_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_165 sourceBody807_3

def sourceBody807_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody807_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 34)

def sourceBody807_169 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 22)) (some 764) ([16, 36]) (some (16, sourceBody807_150, 807, 23))

def sourceBody807_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_169 sourceBody807_3

def sourceBody807_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_170 sourceBody807_0

def sourceBody807_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_147 sourceBody807_171

def sourceBody807_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_168 sourceBody807_172

def sourceBody807_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_173

def sourceBody807_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_174

def sourceBody807_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 34)

def sourceBody807_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody807_178 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 24)) (some 767) ([16, 36, 26]) (some (16, sourceBody807_150, 807, 25))

def sourceBody807_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_178 sourceBody807_3

def sourceBody807_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_179 sourceBody807_0

def sourceBody807_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_177 sourceBody807_180

def sourceBody807_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_176 sourceBody807_181

def sourceBody807_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_168 sourceBody807_182

def sourceBody807_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_183

def sourceBody807_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_184

def sourceBody807_186 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody807_175 sourceBody807_185

def sourceBody807_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_186 sourceBody807_3

def sourceBody807_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_187 sourceBody807_0

def sourceBody807_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_167 sourceBody807_188

def sourceBody807_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_166 sourceBody807_189

def sourceBody807_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_162 sourceBody807_190

def sourceBody807_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_161 sourceBody807_191

def sourceBody807_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_160 sourceBody807_192

def sourceBody807_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody807_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 40)

def sourceBody807_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_195 sourceBody807_0

def sourceBody807_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_196 sourceBody807_0

def sourceBody807_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_194 sourceBody807_197

def sourceBody807_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_198

def sourceBody807_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_193 sourceBody807_199

def sourceBody807_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_110 sourceBody807_200

def sourceBody807_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_201

def sourceBody807_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_202

def sourceBody807_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_203

def sourceBody807_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_204

def sourceBody807_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_205

def sourceBody807_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_206

def sourceBody807_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_207

def sourceBody807_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_208

def sourceBody807_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_102 sourceBody807_209

def sourceBody807_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_77 sourceBody807_210

def sourceBody807_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_211

def sourceBody807_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_212

def sourceBody807_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_73 sourceBody807_213

def sourceBody807_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_46 sourceBody807_214

def sourceBody807_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_215

def sourceBody807_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_216

def sourceBody807_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_38 sourceBody807_217

def sourceBody807_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_37 sourceBody807_218

def sourceBody807_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody807_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_219 sourceBody807_220

def sourceBody807_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody807_223 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody807_221 sourceBody807_222

def sourceBody807_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_223 sourceBody807_3

def sourceBody807_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_224 sourceBody807_0

def sourceBody807_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_31 sourceBody807_225

def sourceBody807_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_30 sourceBody807_226

def sourceBody807_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_26 sourceBody807_227

def sourceBody807_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_25 sourceBody807_228

def sourceBody807_230 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody807_229 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody807_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_230 sourceBody807_3

def sourceBody807_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_3 sourceBody807_231

def sourceBody807_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 34)

def sourceBody807_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 6)

def sourceBody807_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody807_236 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody807_0, 807, 26)) (some 772) ([22, 42]) (some (22, sourceBody807_235, 807, 27))

def sourceBody807_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_236 sourceBody807_3

def sourceBody807_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_237 sourceBody807_0

def sourceBody807_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_234 sourceBody807_238

def sourceBody807_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_233 sourceBody807_239

def sourceBody807_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_240

def sourceBody807_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_241

def sourceBody807_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_232 sourceBody807_242

def sourceBody807_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody807_245 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody807_0, 807, 28)) (some 70) ([22]) (some (22, sourceBody807_235, 807, 29))

def sourceBody807_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_245 sourceBody807_3

def sourceBody807_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_246 sourceBody807_0

def sourceBody807_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_244 sourceBody807_247

def sourceBody807_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_248

def sourceBody807_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_249

def sourceBody807_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_243 sourceBody807_250

def sourceBody807_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody807_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody807_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_253 sourceBody807_0

def sourceBody807_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_252 sourceBody807_254

def sourceBody807_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_251 sourceBody807_255

def sourceBody807_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_24 sourceBody807_256

def sourceBody807_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_257

def sourceBody807_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_23 sourceBody807_258

def sourceBody807_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_259

def sourceBody807_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_260

def sourceBody807_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_17 sourceBody807_261

def sourceBody807_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_262

def sourceBody807_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_263

def sourceBody807_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_11 sourceBody807_264

def sourceBody807_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_265

def sourceBody807_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_266

def sourceBody807_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_5 sourceBody807_267

def sourceBody807_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_268

def sourceBody807_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody807_0 sourceBody807_269

def source807 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (807, 4, sourceBody807_270)
end InitECandidate.Proofs.WordStages
