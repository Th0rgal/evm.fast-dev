import InitECandidate.Proofs.WordStages.Source381
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody397_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody397_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody397_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody397_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody397_0, 397, 2)) (some 395) ([10]) (some (10, sourceBody397_2, 397, 3))

def sourceBody397_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody397_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_3 sourceBody397_4

def sourceBody397_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_5 sourceBody397_0

def sourceBody397_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_1 sourceBody397_6

def sourceBody397_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody397_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody397_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody397_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody397_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody397_0, 397, 4)) (some 79) ([30, 20, 42]) (some (30, sourceBody397_11, 397, 5))

def sourceBody397_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_12 sourceBody397_4

def sourceBody397_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_13 sourceBody397_0

def sourceBody397_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_10 sourceBody397_14

def sourceBody397_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_9 sourceBody397_15

def sourceBody397_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_8 sourceBody397_16

def sourceBody397_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody397_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody397_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 42) sourceBody397_20 sourceBody397_21

def sourceBody397_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_22 sourceBody397_4

def sourceBody397_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody397_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30, 20, 42, 8]

def sourceBody397_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_27 sourceBody397_0

def sourceBody397_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_26 sourceBody397_28

def sourceBody397_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_19 sourceBody397_29

def sourceBody397_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_21 sourceBody397_30

def sourceBody397_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_25 sourceBody397_31

def sourceBody397_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody397_32 sourceBody397_0

def sourceBody397_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_33 sourceBody397_4

def sourceBody397_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_34 sourceBody397_0

def sourceBody397_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_24 sourceBody397_35

def sourceBody397_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_23 sourceBody397_36

def sourceBody397_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_19 sourceBody397_37

def sourceBody397_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_18 sourceBody397_38

def sourceBody397_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 36)

def sourceBody397_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody397_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody397_0, 397, 6)) (some 396) ([20]) (some (20, sourceBody397_41, 397, 7))

def sourceBody397_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_42 sourceBody397_4

def sourceBody397_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_43 sourceBody397_0

def sourceBody397_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_40 sourceBody397_44

def sourceBody397_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody397_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody397_0, 397, 8)) (some 69) ([]) (some (42, sourceBody397_46, 397, 9))

def sourceBody397_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_47 sourceBody397_4

def sourceBody397_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_48 sourceBody397_0

def sourceBody397_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody397_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody397_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody397_0, 397, 10)) (some 68) ([8]) (some (8, sourceBody397_51, 397, 11))

def sourceBody397_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_52 sourceBody397_4

def sourceBody397_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_53 sourceBody397_0

def sourceBody397_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_50 sourceBody397_54

def sourceBody397_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody397_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody397_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 42)

def sourceBody397_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody397_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody397_0, 397, 12)) (some 158) ([28, 18, 40]) (some (28, sourceBody397_59, 397, 13))

def sourceBody397_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_60 sourceBody397_4

def sourceBody397_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_61 sourceBody397_0

def sourceBody397_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_58 sourceBody397_62

def sourceBody397_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_57 sourceBody397_63

def sourceBody397_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_56 sourceBody397_64

def sourceBody397_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_65

def sourceBody397_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_66

def sourceBody397_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 30)

def sourceBody397_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 42)

def sourceBody397_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody397_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 28, 18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody397_0, 397, 14)) (some 303) ([40, 14]) (some (40, sourceBody397_70, 397, 15))

def sourceBody397_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_71 sourceBody397_4

def sourceBody397_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_72 sourceBody397_0

def sourceBody397_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_69 sourceBody397_73

def sourceBody397_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_68 sourceBody397_74

def sourceBody397_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody397_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody397_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody397_0, 397, 16)) (some 70) ([14]) (some (14, sourceBody397_77, 397, 17))

def sourceBody397_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_78 sourceBody397_4

def sourceBody397_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_79 sourceBody397_0

def sourceBody397_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_76 sourceBody397_80

def sourceBody397_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_81

def sourceBody397_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_82

def sourceBody397_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody397_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody397_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_88 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 34) sourceBody397_86 sourceBody397_87

def sourceBody397_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_88 sourceBody397_4

def sourceBody397_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody397_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [40, 14, 34, 24]

def sourceBody397_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_93 sourceBody397_0

def sourceBody397_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_92 sourceBody397_94

def sourceBody397_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_85 sourceBody397_95

def sourceBody397_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_87 sourceBody397_96

def sourceBody397_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_91 sourceBody397_97

def sourceBody397_99 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody397_98 sourceBody397_0

def sourceBody397_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_99 sourceBody397_4

def sourceBody397_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_100 sourceBody397_0

def sourceBody397_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_90 sourceBody397_101

def sourceBody397_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_89 sourceBody397_102

def sourceBody397_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_85 sourceBody397_103

def sourceBody397_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_84 sourceBody397_104

def sourceBody397_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_83 sourceBody397_105

def sourceBody397_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 28)

def sourceBody397_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody397_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody397_110 : WordLangProgHOL (BitVec 64) :=
.call (some (([40, 14, 34, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody397_0, 397, 18)) (some 162) ([44, 6]) (some (44, sourceBody397_109, 397, 19))

def sourceBody397_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_110 sourceBody397_4

def sourceBody397_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_111 sourceBody397_0

def sourceBody397_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_108 sourceBody397_112

def sourceBody397_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_107 sourceBody397_113

def sourceBody397_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 40)

def sourceBody397_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody397_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody397_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_119 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 26) sourceBody397_117 sourceBody397_118

def sourceBody397_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_119 sourceBody397_4

def sourceBody397_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody397_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody397_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [44, 6, 26, 16]

def sourceBody397_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_125 sourceBody397_0

def sourceBody397_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_124 sourceBody397_126

def sourceBody397_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_123 sourceBody397_127

def sourceBody397_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_118 sourceBody397_128

def sourceBody397_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_122 sourceBody397_129

def sourceBody397_131 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody397_130 sourceBody397_0

def sourceBody397_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_131 sourceBody397_4

def sourceBody397_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_132 sourceBody397_0

def sourceBody397_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_121 sourceBody397_133

def sourceBody397_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_120 sourceBody397_134

def sourceBody397_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_116 sourceBody397_135

def sourceBody397_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_115 sourceBody397_136

def sourceBody397_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody397_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody397_140 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.WordRegImm.reg 26) sourceBody397_117 sourceBody397_118

def sourceBody397_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_140 sourceBody397_4

def sourceBody397_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody397_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 44)

def sourceBody397_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_143 sourceBody397_0

def sourceBody397_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_144 sourceBody397_0

def sourceBody397_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_142 sourceBody397_145

def sourceBody397_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_146

def sourceBody397_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody397_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_148 sourceBody397_109

def sourceBody397_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_147 sourceBody397_149

def sourceBody397_151 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody397_150 sourceBody397_0

def sourceBody397_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_151 sourceBody397_4

def sourceBody397_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_152 sourceBody397_0

def sourceBody397_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_121 sourceBody397_153

def sourceBody397_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_141 sourceBody397_154

def sourceBody397_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_139 sourceBody397_155

def sourceBody397_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_138 sourceBody397_156

def sourceBody397_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_137 sourceBody397_157

def sourceBody397_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 14)

def sourceBody397_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 34)

def sourceBody397_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody397_162 : WordLangProgHOL (BitVec 64) :=
.call (some (([44, 6, 26, 16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody397_0, 397, 20)) (some 146) ([38, 12]) (some (38, sourceBody397_161, 397, 21))

def sourceBody397_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_162 sourceBody397_4

def sourceBody397_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_163 sourceBody397_0

def sourceBody397_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_160 sourceBody397_164

def sourceBody397_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_159 sourceBody397_165

def sourceBody397_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody397_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody397_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody397_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody397_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38, 12, 32, 22]

def sourceBody397_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_171 sourceBody397_0

def sourceBody397_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_170 sourceBody397_172

def sourceBody397_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_169 sourceBody397_173

def sourceBody397_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_168 sourceBody397_174

def sourceBody397_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_167 sourceBody397_175

def sourceBody397_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_166 sourceBody397_176

def sourceBody397_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_177

def sourceBody397_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_178

def sourceBody397_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_179

def sourceBody397_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_180

def sourceBody397_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_181

def sourceBody397_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_182

def sourceBody397_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_183

def sourceBody397_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_184

def sourceBody397_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_158 sourceBody397_185

def sourceBody397_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_114 sourceBody397_186

def sourceBody397_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_187

def sourceBody397_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_188

def sourceBody397_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_189

def sourceBody397_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_190

def sourceBody397_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_191

def sourceBody397_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_192

def sourceBody397_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_193

def sourceBody397_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_194

def sourceBody397_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_106 sourceBody397_195

def sourceBody397_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_75 sourceBody397_196

def sourceBody397_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_197

def sourceBody397_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_198

def sourceBody397_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_199

def sourceBody397_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_200

def sourceBody397_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_201

def sourceBody397_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_202

def sourceBody397_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_67 sourceBody397_203

def sourceBody397_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_55 sourceBody397_204

def sourceBody397_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_205

def sourceBody397_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_206

def sourceBody397_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_49 sourceBody397_207

def sourceBody397_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_208

def sourceBody397_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_209

def sourceBody397_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_45 sourceBody397_210

def sourceBody397_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_211

def sourceBody397_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_212

def sourceBody397_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_39 sourceBody397_213

def sourceBody397_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_17 sourceBody397_214

def sourceBody397_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_215

def sourceBody397_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_216

def sourceBody397_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_7 sourceBody397_217

def sourceBody397_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_218

def sourceBody397_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody397_0 sourceBody397_219

def source397 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (397, 3, sourceBody397_220)
end InitECandidate.Proofs.WordStages
