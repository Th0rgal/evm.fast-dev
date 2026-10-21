import InitECandidate.Proofs.WordStages.Source683
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody699_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody699_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
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

def sourceBody699_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody699_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody699_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody699_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody699_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([4, 14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody699_0, 699, 2)) (some 94) ([10, 18]) (some (10, sourceBody699_5, 699, 3))

def sourceBody699_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody699_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_6 sourceBody699_7

def sourceBody699_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_8 sourceBody699_0

def sourceBody699_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_4 sourceBody699_9

def sourceBody699_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_3 sourceBody699_10

def sourceBody699_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody699_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 34000#64)

def sourceBody699_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 12 12 18 2))

def sourceBody699_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 45000#64])

def sourceBody699_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody699_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody699_0, 699, 4)) (some 466) ([8]) (some (18, sourceBody699_16, 699, 5))

def sourceBody699_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_17 sourceBody699_7

def sourceBody699_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_18 sourceBody699_0

def sourceBody699_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_15 sourceBody699_19

def sourceBody699_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_14 sourceBody699_20

def sourceBody699_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_13 sourceBody699_21

def sourceBody699_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_12 sourceBody699_22

def sourceBody699_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_23

def sourceBody699_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_24

def sourceBody699_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody699_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody699_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody699_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody699_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 2) sourceBody699_28 sourceBody699_29

def sourceBody699_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_30 sourceBody699_7

def sourceBody699_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody699_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody699_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody699_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_34 sourceBody699_0

def sourceBody699_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_35 sourceBody699_0

def sourceBody699_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_33 sourceBody699_36

def sourceBody699_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_37

def sourceBody699_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody699_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_39 sourceBody699_5

def sourceBody699_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_38 sourceBody699_40

def sourceBody699_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody699_41 sourceBody699_0

def sourceBody699_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_42 sourceBody699_7

def sourceBody699_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_43 sourceBody699_0

def sourceBody699_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_32 sourceBody699_44

def sourceBody699_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_31 sourceBody699_45

def sourceBody699_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_27 sourceBody699_46

def sourceBody699_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_26 sourceBody699_47

def sourceBody699_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_25 sourceBody699_48

def sourceBody699_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody699_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody699_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody699_0, 699, 6)) (some 696) ([18, 2]) (some (18, sourceBody699_16, 699, 7))

def sourceBody699_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_52 sourceBody699_7

def sourceBody699_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_53 sourceBody699_0

def sourceBody699_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_51 sourceBody699_54

def sourceBody699_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_50 sourceBody699_55

def sourceBody699_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody699_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody699_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody699_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.WordRegImm.reg 12) sourceBody699_59 sourceBody699_27

def sourceBody699_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_60 sourceBody699_7

def sourceBody699_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody699_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody699_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 18)

def sourceBody699_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_64 sourceBody699_0

def sourceBody699_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_65 sourceBody699_0

def sourceBody699_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_63 sourceBody699_66

def sourceBody699_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_67

def sourceBody699_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody699_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_69 sourceBody699_16

def sourceBody699_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_68 sourceBody699_70

def sourceBody699_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody699_71 sourceBody699_0

def sourceBody699_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_72 sourceBody699_7

def sourceBody699_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_73 sourceBody699_0

def sourceBody699_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_62 sourceBody699_74

def sourceBody699_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_61 sourceBody699_75

def sourceBody699_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_58 sourceBody699_76

def sourceBody699_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_57 sourceBody699_77

def sourceBody699_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody699_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody699_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody699_0, 699, 8)) (some 68) ([2]) (some (2, sourceBody699_80, 699, 9))

def sourceBody699_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_81 sourceBody699_7

def sourceBody699_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_82 sourceBody699_0

def sourceBody699_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_79 sourceBody699_83

def sourceBody699_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody699_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody699_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody699_0, 699, 10)) (some 78) ([12, 8]) (some (12, sourceBody699_86, 699, 11))

def sourceBody699_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_87 sourceBody699_7

def sourceBody699_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_88 sourceBody699_0

def sourceBody699_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_85 sourceBody699_89

def sourceBody699_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_32 sourceBody699_90

def sourceBody699_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_91

def sourceBody699_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_92

def sourceBody699_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 31#64])

def sourceBody699_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody699_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 12 (Flapjack.WordLangAddr.addr 2 0#64))

def sourceBody699_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_96 sourceBody699_0

def sourceBody699_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_95 sourceBody699_97

def sourceBody699_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_94 sourceBody699_98

def sourceBody699_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_93 sourceBody699_99

def sourceBody699_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody699_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody699_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 2) 8

def sourceBody699_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_103 sourceBody699_0

def sourceBody699_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_102 sourceBody699_104

def sourceBody699_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_105 sourceBody699_0

def sourceBody699_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_32 sourceBody699_106

def sourceBody699_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_107

def sourceBody699_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_101 sourceBody699_108

def sourceBody699_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_109

def sourceBody699_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_100 sourceBody699_110

def sourceBody699_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody699_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody699_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_113 sourceBody699_106

def sourceBody699_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_114

def sourceBody699_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_112 sourceBody699_115

def sourceBody699_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_116

def sourceBody699_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_111 sourceBody699_117

def sourceBody699_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody699_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_119 sourceBody699_0

def sourceBody699_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_27 sourceBody699_120

def sourceBody699_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_118 sourceBody699_121

def sourceBody699_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_84 sourceBody699_122

def sourceBody699_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_123

def sourceBody699_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_124

def sourceBody699_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_78 sourceBody699_125

def sourceBody699_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_56 sourceBody699_126

def sourceBody699_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_127

def sourceBody699_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_128

def sourceBody699_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_49 sourceBody699_129

def sourceBody699_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_11 sourceBody699_130

def sourceBody699_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_131

def sourceBody699_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_132

def sourceBody699_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_133

def sourceBody699_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_134

def sourceBody699_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_2 sourceBody699_135

def sourceBody699_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_136

def sourceBody699_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_1 sourceBody699_137

def sourceBody699_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody699_0 sourceBody699_138

def source699 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (699, 1, sourceBody699_139)
end InitECandidate.Proofs.WordStages
