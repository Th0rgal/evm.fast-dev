import InitECandidate.Proofs.WordStages.Source802
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody818_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody818_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody818_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody818_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody818_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody818_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody818_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody818_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 14) sourceBody818_5 sourceBody818_6

def sourceBody818_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody818_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_7 sourceBody818_8

def sourceBody818_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody818_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody818_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 6)

def sourceBody818_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_12 sourceBody818_0

def sourceBody818_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_13 sourceBody818_0

def sourceBody818_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_11 sourceBody818_14

def sourceBody818_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_15

def sourceBody818_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody818_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody818_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_17 sourceBody818_18

def sourceBody818_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_16 sourceBody818_19

def sourceBody818_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody818_20 sourceBody818_0

def sourceBody818_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_21 sourceBody818_8

def sourceBody818_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_22 sourceBody818_0

def sourceBody818_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_10 sourceBody818_23

def sourceBody818_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_9 sourceBody818_24

def sourceBody818_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_4 sourceBody818_25

def sourceBody818_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_3 sourceBody818_26

def sourceBody818_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 26)

def sourceBody818_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody818_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody818_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 22]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody818_0, 818, 2)) (some 94) ([14, 30]) (some (14, sourceBody818_30, 818, 3))

def sourceBody818_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_31 sourceBody818_8

def sourceBody818_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_32 sourceBody818_0

def sourceBody818_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_29 sourceBody818_33

def sourceBody818_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_28 sourceBody818_34

def sourceBody818_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody818_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody818_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody818_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 4) sourceBody818_37 sourceBody818_38

def sourceBody818_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_39 sourceBody818_8

def sourceBody818_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody818_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody818_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 14)

def sourceBody818_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_43 sourceBody818_0

def sourceBody818_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_44 sourceBody818_0

def sourceBody818_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_42 sourceBody818_45

def sourceBody818_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_46

def sourceBody818_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody818_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_48 sourceBody818_30

def sourceBody818_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_47 sourceBody818_49

def sourceBody818_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody818_50 sourceBody818_0

def sourceBody818_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_51 sourceBody818_8

def sourceBody818_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_52 sourceBody818_0

def sourceBody818_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_41 sourceBody818_53

def sourceBody818_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_40 sourceBody818_54

def sourceBody818_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_36 sourceBody818_55

def sourceBody818_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_10 sourceBody818_56

def sourceBody818_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody818_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 14)

def sourceBody818_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody818_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody818_0, 818, 4)) (some 815) ([4]) (some (4, sourceBody818_60, 818, 5))

def sourceBody818_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_61 sourceBody818_8

def sourceBody818_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_62 sourceBody818_0

def sourceBody818_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_59 sourceBody818_63

def sourceBody818_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody818_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 12000#64)

def sourceBody818_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 8 8 12 28))

def sourceBody818_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody818_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody818_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 32 32 24 16))

def sourceBody818_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody818_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1000#64)

def sourceBody818_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody818_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([4, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody818_0, 818, 6)) (some 94) ([2, 18]) (some (12, sourceBody818_73, 818, 7))

def sourceBody818_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_74 sourceBody818_8

def sourceBody818_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_75 sourceBody818_0

def sourceBody818_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_72 sourceBody818_76

def sourceBody818_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_71 sourceBody818_77

def sourceBody818_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_70 sourceBody818_78

def sourceBody818_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_69 sourceBody818_79

def sourceBody818_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_68 sourceBody818_80

def sourceBody818_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_67 sourceBody818_81

def sourceBody818_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_66 sourceBody818_82

def sourceBody818_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_65 sourceBody818_83

def sourceBody818_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody818_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody818_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody818_0, 818, 8)) (some 466) ([28]) (some (28, sourceBody818_86, 818, 9))

def sourceBody818_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_87 sourceBody818_8

def sourceBody818_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_88 sourceBody818_0

def sourceBody818_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_85 sourceBody818_89

def sourceBody818_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_90

def sourceBody818_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_91

def sourceBody818_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody818_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody818_0, 818, 10)) (some 68) ([28]) (some (28, sourceBody818_86, 818, 11))

def sourceBody818_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_94 sourceBody818_8

def sourceBody818_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_95 sourceBody818_0

def sourceBody818_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_93 sourceBody818_96

def sourceBody818_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody818_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody818_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody818_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody818_102 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody818_0, 818, 12)) (some 807) ([8, 24, 16]) (some (8, sourceBody818_101, 818, 13))

def sourceBody818_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_102 sourceBody818_8

def sourceBody818_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_103 sourceBody818_0

def sourceBody818_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_100 sourceBody818_104

def sourceBody818_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_99 sourceBody818_105

def sourceBody818_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_98 sourceBody818_106

def sourceBody818_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody818_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody818_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody818_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody818_112 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 16) sourceBody818_110 sourceBody818_111

def sourceBody818_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_112 sourceBody818_8

def sourceBody818_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody818_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody818_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody818_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_116 sourceBody818_0

def sourceBody818_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_117 sourceBody818_0

def sourceBody818_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_115 sourceBody818_118

def sourceBody818_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_119

def sourceBody818_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody818_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_121 sourceBody818_101

def sourceBody818_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_120 sourceBody818_122

def sourceBody818_124 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody818_123 sourceBody818_0

def sourceBody818_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_124 sourceBody818_8

def sourceBody818_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_125 sourceBody818_0

def sourceBody818_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_114 sourceBody818_126

def sourceBody818_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_113 sourceBody818_127

def sourceBody818_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_109 sourceBody818_128

def sourceBody818_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_108 sourceBody818_129

def sourceBody818_131 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody818_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody818_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody818_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 16

def sourceBody818_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_134 sourceBody818_0

def sourceBody818_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_133 sourceBody818_135

def sourceBody818_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_136 sourceBody818_0

def sourceBody818_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_132 sourceBody818_137

def sourceBody818_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_138

def sourceBody818_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_131 sourceBody818_139

def sourceBody818_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_140

def sourceBody818_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_130 sourceBody818_141

def sourceBody818_143 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody818_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody818_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_144 sourceBody818_137

def sourceBody818_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_145

def sourceBody818_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_143 sourceBody818_146

def sourceBody818_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_147

def sourceBody818_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_142 sourceBody818_148

def sourceBody818_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody818_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody818_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_151 sourceBody818_0

def sourceBody818_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_150 sourceBody818_152

def sourceBody818_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_149 sourceBody818_153

def sourceBody818_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_107 sourceBody818_154

def sourceBody818_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_155

def sourceBody818_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_156

def sourceBody818_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_97 sourceBody818_157

def sourceBody818_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_158

def sourceBody818_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_159

def sourceBody818_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_92 sourceBody818_160

def sourceBody818_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_84 sourceBody818_161

def sourceBody818_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_162

def sourceBody818_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_163

def sourceBody818_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_164

def sourceBody818_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_165

def sourceBody818_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_64 sourceBody818_166

def sourceBody818_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_167

def sourceBody818_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_168

def sourceBody818_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_58 sourceBody818_169

def sourceBody818_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_170

def sourceBody818_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_57 sourceBody818_171

def sourceBody818_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_35 sourceBody818_172

def sourceBody818_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_173

def sourceBody818_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_174

def sourceBody818_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_175

def sourceBody818_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_176

def sourceBody818_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_27 sourceBody818_177

def sourceBody818_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_2 sourceBody818_178

def sourceBody818_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_179

def sourceBody818_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_1 sourceBody818_180

def sourceBody818_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody818_0 sourceBody818_181

def source818 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (818, 1, sourceBody818_182)
end InitECandidate.Proofs.WordStages
