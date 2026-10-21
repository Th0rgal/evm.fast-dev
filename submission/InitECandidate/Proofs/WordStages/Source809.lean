import InitECandidate.Proofs.WordStages.Source793
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody809_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody809_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody809_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 2)) (some 69) ([]) (some (34, sourceBody809_1, 809, 3))

def sourceBody809_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody809_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_2 sourceBody809_3

def sourceBody809_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_4 sourceBody809_0

def sourceBody809_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody809_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody809_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 4)) (some 68) ([24]) (some (24, sourceBody809_7, 809, 5))

def sourceBody809_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_8 sourceBody809_3

def sourceBody809_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_9 sourceBody809_0

def sourceBody809_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_6 sourceBody809_10

def sourceBody809_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody809_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody809_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 6)) (some 68) ([44]) (some (44, sourceBody809_13, 809, 7))

def sourceBody809_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_14 sourceBody809_3

def sourceBody809_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_15 sourceBody809_0

def sourceBody809_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_12 sourceBody809_16

def sourceBody809_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody809_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody809_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 8)) (some 68) ([10]) (some (10, sourceBody809_19, 809, 9))

def sourceBody809_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_20 sourceBody809_3

def sourceBody809_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_21 sourceBody809_0

def sourceBody809_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_18 sourceBody809_22

def sourceBody809_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody809_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody809_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody809_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody809_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody809_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 22 (Flapjack.WordRegImm.reg 42) sourceBody809_27 sourceBody809_28

def sourceBody809_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_29 sourceBody809_3

def sourceBody809_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody809_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody809_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody809_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 42 42 32 22))

def sourceBody809_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_34 sourceBody809_0

def sourceBody809_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_33 sourceBody809_35

def sourceBody809_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_32 sourceBody809_36

def sourceBody809_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 42])

def sourceBody809_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 18)

def sourceBody809_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 24)

def sourceBody809_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody809_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 10)) (some 783) ([28, 48]) (some (28, sourceBody809_41, 809, 11))

def sourceBody809_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_42 sourceBody809_3

def sourceBody809_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_43 sourceBody809_0

def sourceBody809_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_40 sourceBody809_44

def sourceBody809_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_39 sourceBody809_45

def sourceBody809_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 38)

def sourceBody809_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody809_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody809_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody809_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 48 (Flapjack.WordRegImm.reg 8) sourceBody809_49 sourceBody809_50

def sourceBody809_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_51 sourceBody809_3

def sourceBody809_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 48)

def sourceBody809_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 14)

def sourceBody809_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody809_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody809_0, 809, 12)) (some 70) ([48]) (some (48, sourceBody809_55, 809, 13))

def sourceBody809_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_56 sourceBody809_3

def sourceBody809_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_57 sourceBody809_0

def sourceBody809_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_54 sourceBody809_58

def sourceBody809_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_59

def sourceBody809_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_60

def sourceBody809_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody809_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody809_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_63 sourceBody809_0

def sourceBody809_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_62 sourceBody809_64

def sourceBody809_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_61 sourceBody809_65

def sourceBody809_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody809_66 sourceBody809_0

def sourceBody809_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_67 sourceBody809_3

def sourceBody809_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_68 sourceBody809_0

def sourceBody809_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_53 sourceBody809_69

def sourceBody809_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_52 sourceBody809_70

def sourceBody809_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_48 sourceBody809_71

def sourceBody809_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_47 sourceBody809_72

def sourceBody809_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 14)) (some 785) ([48]) (some (48, sourceBody809_55, 809, 15))

def sourceBody809_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_74 sourceBody809_3

def sourceBody809_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_75 sourceBody809_0

def sourceBody809_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_40 sourceBody809_76

def sourceBody809_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody809_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody809_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody809_81 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 30) sourceBody809_80 sourceBody809_48

def sourceBody809_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_81 sourceBody809_3

def sourceBody809_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody809_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody809_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody809_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody809_0, 809, 16)) (some 70) ([8]) (some (8, sourceBody809_85, 809, 17))

def sourceBody809_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_86 sourceBody809_3

def sourceBody809_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_87 sourceBody809_0

def sourceBody809_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_84 sourceBody809_88

def sourceBody809_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_89

def sourceBody809_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_90

def sourceBody809_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [48]

def sourceBody809_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_92 sourceBody809_0

def sourceBody809_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_49 sourceBody809_93

def sourceBody809_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_91 sourceBody809_94

def sourceBody809_96 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody809_95 sourceBody809_0

def sourceBody809_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_96 sourceBody809_3

def sourceBody809_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_97 sourceBody809_0

def sourceBody809_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_83 sourceBody809_98

def sourceBody809_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_82 sourceBody809_99

def sourceBody809_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_79 sourceBody809_100

def sourceBody809_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_78 sourceBody809_101

def sourceBody809_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 256#64])

def sourceBody809_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody809_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody809_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 8, 30, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 18)) (some 146) ([40, 16]) (some (40, sourceBody809_105, 809, 19))

def sourceBody809_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_106 sourceBody809_3

def sourceBody809_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_107 sourceBody809_0

def sourceBody809_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_104 sourceBody809_108

def sourceBody809_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_103 sourceBody809_109

def sourceBody809_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 44)

def sourceBody809_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 48)

def sourceBody809_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 8)

def sourceBody809_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody809_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 20)

def sourceBody809_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody809_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 12

def sourceBody809_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_117 sourceBody809_0

def sourceBody809_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_116 sourceBody809_118

def sourceBody809_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody809_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64])
  12

def sourceBody809_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_121 sourceBody809_0

def sourceBody809_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_120 sourceBody809_122

def sourceBody809_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody809_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 16#64])
  12

def sourceBody809_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_125 sourceBody809_0

def sourceBody809_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_124 sourceBody809_126

def sourceBody809_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 46)

def sourceBody809_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 24#64])
  12

def sourceBody809_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_129 sourceBody809_0

def sourceBody809_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_128 sourceBody809_130

def sourceBody809_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_131 sourceBody809_0

def sourceBody809_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_127 sourceBody809_132

def sourceBody809_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_123 sourceBody809_133

def sourceBody809_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_119 sourceBody809_134

def sourceBody809_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_115 sourceBody809_135

def sourceBody809_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_136

def sourceBody809_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_114 sourceBody809_137

def sourceBody809_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_138

def sourceBody809_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_113 sourceBody809_139

def sourceBody809_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_140

def sourceBody809_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_112 sourceBody809_141

def sourceBody809_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_142

def sourceBody809_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_111 sourceBody809_143

def sourceBody809_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_144

def sourceBody809_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody809_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody809_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 44)

def sourceBody809_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody809_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody809_151 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 20)) (some 780) ([16, 36, 26, 46]) (some (16, sourceBody809_150, 809, 21))

def sourceBody809_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_151 sourceBody809_3

def sourceBody809_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_152 sourceBody809_0

def sourceBody809_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_149 sourceBody809_153

def sourceBody809_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_148 sourceBody809_154

def sourceBody809_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_147 sourceBody809_155

def sourceBody809_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_146 sourceBody809_156

def sourceBody809_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_157

def sourceBody809_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_158

def sourceBody809_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_145 sourceBody809_159

def sourceBody809_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody809_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody809_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody809_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody809_165 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 36) sourceBody809_163 sourceBody809_164

def sourceBody809_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_165 sourceBody809_3

def sourceBody809_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody809_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 34)

def sourceBody809_169 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 22)) (some 776) ([16, 36]) (some (16, sourceBody809_150, 809, 23))

def sourceBody809_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_169 sourceBody809_3

def sourceBody809_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_170 sourceBody809_0

def sourceBody809_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_147 sourceBody809_171

def sourceBody809_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_168 sourceBody809_172

def sourceBody809_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_173

def sourceBody809_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_174

def sourceBody809_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 34)

def sourceBody809_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody809_178 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 24)) (some 779) ([16, 36, 26]) (some (16, sourceBody809_150, 809, 25))

def sourceBody809_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_178 sourceBody809_3

def sourceBody809_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_179 sourceBody809_0

def sourceBody809_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_177 sourceBody809_180

def sourceBody809_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_176 sourceBody809_181

def sourceBody809_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_168 sourceBody809_182

def sourceBody809_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_183

def sourceBody809_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_184

def sourceBody809_186 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody809_175 sourceBody809_185

def sourceBody809_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_186 sourceBody809_3

def sourceBody809_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_187 sourceBody809_0

def sourceBody809_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_167 sourceBody809_188

def sourceBody809_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_166 sourceBody809_189

def sourceBody809_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_162 sourceBody809_190

def sourceBody809_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_161 sourceBody809_191

def sourceBody809_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_160 sourceBody809_192

def sourceBody809_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody809_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 40)

def sourceBody809_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_195 sourceBody809_0

def sourceBody809_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_196 sourceBody809_0

def sourceBody809_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_194 sourceBody809_197

def sourceBody809_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_198

def sourceBody809_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_193 sourceBody809_199

def sourceBody809_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_110 sourceBody809_200

def sourceBody809_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_201

def sourceBody809_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_202

def sourceBody809_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_203

def sourceBody809_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_204

def sourceBody809_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_205

def sourceBody809_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_206

def sourceBody809_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_207

def sourceBody809_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_208

def sourceBody809_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_102 sourceBody809_209

def sourceBody809_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_77 sourceBody809_210

def sourceBody809_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_211

def sourceBody809_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_212

def sourceBody809_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_73 sourceBody809_213

def sourceBody809_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_46 sourceBody809_214

def sourceBody809_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_215

def sourceBody809_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_216

def sourceBody809_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_38 sourceBody809_217

def sourceBody809_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_37 sourceBody809_218

def sourceBody809_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody809_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_219 sourceBody809_220

def sourceBody809_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody809_223 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody809_221 sourceBody809_222

def sourceBody809_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_223 sourceBody809_3

def sourceBody809_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_224 sourceBody809_0

def sourceBody809_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_31 sourceBody809_225

def sourceBody809_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_30 sourceBody809_226

def sourceBody809_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_26 sourceBody809_227

def sourceBody809_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_25 sourceBody809_228

def sourceBody809_230 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody809_229 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody809_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_230 sourceBody809_3

def sourceBody809_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_3 sourceBody809_231

def sourceBody809_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 34)

def sourceBody809_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 6)

def sourceBody809_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody809_236 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody809_0, 809, 26)) (some 784) ([22, 42]) (some (22, sourceBody809_235, 809, 27))

def sourceBody809_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_236 sourceBody809_3

def sourceBody809_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_237 sourceBody809_0

def sourceBody809_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_234 sourceBody809_238

def sourceBody809_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_233 sourceBody809_239

def sourceBody809_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_240

def sourceBody809_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_241

def sourceBody809_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_232 sourceBody809_242

def sourceBody809_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody809_245 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody809_0, 809, 28)) (some 70) ([22]) (some (22, sourceBody809_235, 809, 29))

def sourceBody809_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_245 sourceBody809_3

def sourceBody809_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_246 sourceBody809_0

def sourceBody809_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_244 sourceBody809_247

def sourceBody809_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_248

def sourceBody809_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_249

def sourceBody809_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_243 sourceBody809_250

def sourceBody809_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody809_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody809_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_253 sourceBody809_0

def sourceBody809_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_252 sourceBody809_254

def sourceBody809_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_251 sourceBody809_255

def sourceBody809_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_24 sourceBody809_256

def sourceBody809_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_257

def sourceBody809_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_23 sourceBody809_258

def sourceBody809_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_259

def sourceBody809_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_260

def sourceBody809_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_17 sourceBody809_261

def sourceBody809_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_262

def sourceBody809_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_263

def sourceBody809_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_11 sourceBody809_264

def sourceBody809_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_265

def sourceBody809_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_266

def sourceBody809_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_5 sourceBody809_267

def sourceBody809_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_268

def sourceBody809_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody809_0 sourceBody809_269

def source809 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (809, 4, sourceBody809_270)
end InitECandidate.Proofs.WordStages
