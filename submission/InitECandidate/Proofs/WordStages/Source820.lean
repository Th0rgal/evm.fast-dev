import InitECandidate.Proofs.WordStages.Source804
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody820_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody820_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody820_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody820_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody820_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody820_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody820_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody820_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 14) sourceBody820_5 sourceBody820_6

def sourceBody820_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody820_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_7 sourceBody820_8

def sourceBody820_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody820_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody820_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 6)

def sourceBody820_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_12 sourceBody820_0

def sourceBody820_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_13 sourceBody820_0

def sourceBody820_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_11 sourceBody820_14

def sourceBody820_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_15

def sourceBody820_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody820_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody820_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_17 sourceBody820_18

def sourceBody820_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_16 sourceBody820_19

def sourceBody820_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody820_20 sourceBody820_0

def sourceBody820_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_21 sourceBody820_8

def sourceBody820_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_22 sourceBody820_0

def sourceBody820_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_10 sourceBody820_23

def sourceBody820_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_9 sourceBody820_24

def sourceBody820_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_4 sourceBody820_25

def sourceBody820_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_3 sourceBody820_26

def sourceBody820_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 26)

def sourceBody820_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody820_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody820_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 22]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody820_0, 820, 2)) (some 94) ([14, 30]) (some (14, sourceBody820_30, 820, 3))

def sourceBody820_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_31 sourceBody820_8

def sourceBody820_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_32 sourceBody820_0

def sourceBody820_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_29 sourceBody820_33

def sourceBody820_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_28 sourceBody820_34

def sourceBody820_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody820_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody820_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody820_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 4) sourceBody820_37 sourceBody820_38

def sourceBody820_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_39 sourceBody820_8

def sourceBody820_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody820_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody820_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 14)

def sourceBody820_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_43 sourceBody820_0

def sourceBody820_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_44 sourceBody820_0

def sourceBody820_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_42 sourceBody820_45

def sourceBody820_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_46

def sourceBody820_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody820_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_48 sourceBody820_30

def sourceBody820_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_47 sourceBody820_49

def sourceBody820_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody820_50 sourceBody820_0

def sourceBody820_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_51 sourceBody820_8

def sourceBody820_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_52 sourceBody820_0

def sourceBody820_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_41 sourceBody820_53

def sourceBody820_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_40 sourceBody820_54

def sourceBody820_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_36 sourceBody820_55

def sourceBody820_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_10 sourceBody820_56

def sourceBody820_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody820_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 14)

def sourceBody820_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody820_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody820_0, 820, 4)) (some 816) ([4]) (some (4, sourceBody820_60, 820, 5))

def sourceBody820_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_61 sourceBody820_8

def sourceBody820_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_62 sourceBody820_0

def sourceBody820_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_59 sourceBody820_63

def sourceBody820_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody820_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 22500#64)

def sourceBody820_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 8 8 12 28))

def sourceBody820_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody820_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody820_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 32 32 24 16))

def sourceBody820_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody820_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1000#64)

def sourceBody820_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody820_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([4, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody820_0, 820, 6)) (some 94) ([2, 18]) (some (12, sourceBody820_73, 820, 7))

def sourceBody820_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_74 sourceBody820_8

def sourceBody820_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_75 sourceBody820_0

def sourceBody820_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_72 sourceBody820_76

def sourceBody820_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_71 sourceBody820_77

def sourceBody820_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_70 sourceBody820_78

def sourceBody820_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_69 sourceBody820_79

def sourceBody820_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_68 sourceBody820_80

def sourceBody820_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_67 sourceBody820_81

def sourceBody820_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_66 sourceBody820_82

def sourceBody820_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_65 sourceBody820_83

def sourceBody820_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody820_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody820_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody820_0, 820, 8)) (some 466) ([28]) (some (28, sourceBody820_86, 820, 9))

def sourceBody820_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_87 sourceBody820_8

def sourceBody820_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_88 sourceBody820_0

def sourceBody820_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_85 sourceBody820_89

def sourceBody820_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_90

def sourceBody820_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_91

def sourceBody820_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody820_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody820_0, 820, 10)) (some 68) ([28]) (some (28, sourceBody820_86, 820, 11))

def sourceBody820_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_94 sourceBody820_8

def sourceBody820_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_95 sourceBody820_0

def sourceBody820_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_93 sourceBody820_96

def sourceBody820_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody820_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody820_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody820_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody820_102 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody820_0, 820, 12)) (some 809) ([8, 24, 16]) (some (8, sourceBody820_101, 820, 13))

def sourceBody820_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_102 sourceBody820_8

def sourceBody820_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_103 sourceBody820_0

def sourceBody820_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_100 sourceBody820_104

def sourceBody820_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_99 sourceBody820_105

def sourceBody820_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_98 sourceBody820_106

def sourceBody820_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody820_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody820_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody820_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody820_112 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 16) sourceBody820_110 sourceBody820_111

def sourceBody820_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_112 sourceBody820_8

def sourceBody820_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody820_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody820_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody820_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_116 sourceBody820_0

def sourceBody820_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_117 sourceBody820_0

def sourceBody820_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_115 sourceBody820_118

def sourceBody820_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_119

def sourceBody820_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody820_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_121 sourceBody820_101

def sourceBody820_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_120 sourceBody820_122

def sourceBody820_124 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody820_123 sourceBody820_0

def sourceBody820_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_124 sourceBody820_8

def sourceBody820_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_125 sourceBody820_0

def sourceBody820_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_114 sourceBody820_126

def sourceBody820_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_113 sourceBody820_127

def sourceBody820_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_109 sourceBody820_128

def sourceBody820_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_108 sourceBody820_129

def sourceBody820_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody820_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody820_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody820_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 16

def sourceBody820_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_134 sourceBody820_0

def sourceBody820_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_133 sourceBody820_135

def sourceBody820_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_136 sourceBody820_0

def sourceBody820_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_132 sourceBody820_137

def sourceBody820_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_138

def sourceBody820_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_131 sourceBody820_139

def sourceBody820_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_140

def sourceBody820_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_130 sourceBody820_141

def sourceBody820_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody820_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody820_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_144 sourceBody820_137

def sourceBody820_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_145

def sourceBody820_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_143 sourceBody820_146

def sourceBody820_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_147

def sourceBody820_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_142 sourceBody820_148

def sourceBody820_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody820_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody820_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_151 sourceBody820_0

def sourceBody820_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_150 sourceBody820_152

def sourceBody820_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_149 sourceBody820_153

def sourceBody820_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_107 sourceBody820_154

def sourceBody820_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_155

def sourceBody820_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_156

def sourceBody820_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_97 sourceBody820_157

def sourceBody820_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_158

def sourceBody820_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_159

def sourceBody820_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_92 sourceBody820_160

def sourceBody820_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_84 sourceBody820_161

def sourceBody820_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_162

def sourceBody820_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_163

def sourceBody820_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_164

def sourceBody820_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_165

def sourceBody820_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_64 sourceBody820_166

def sourceBody820_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_167

def sourceBody820_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_168

def sourceBody820_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_58 sourceBody820_169

def sourceBody820_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_170

def sourceBody820_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_57 sourceBody820_171

def sourceBody820_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_35 sourceBody820_172

def sourceBody820_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_173

def sourceBody820_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_174

def sourceBody820_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_175

def sourceBody820_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_176

def sourceBody820_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_27 sourceBody820_177

def sourceBody820_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_2 sourceBody820_178

def sourceBody820_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_179

def sourceBody820_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_1 sourceBody820_180

def sourceBody820_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody820_0 sourceBody820_181

def source820 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (820, 1, sourceBody820_182)
end InitECandidate.Proofs.WordStages
