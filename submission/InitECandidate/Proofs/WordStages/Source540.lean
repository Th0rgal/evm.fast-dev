import InitECandidate.Proofs.WordStages.Source524
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody540_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody540_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody540_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody540_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody540_0, 540, 2)) (some 466) ([22]) (some (22, sourceBody540_2, 540, 3))

def sourceBody540_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody540_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_3 sourceBody540_4

def sourceBody540_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_5 sourceBody540_0

def sourceBody540_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_1 sourceBody540_6

def sourceBody540_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_7

def sourceBody540_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_8

def sourceBody540_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody540_0, 540, 4)) (some 536) ([]) (some (22, sourceBody540_2, 540, 5))

def sourceBody540_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_10 sourceBody540_4

def sourceBody540_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_11 sourceBody540_0

def sourceBody540_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 81#64)

def sourceBody540_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody540_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody540_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody540_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 4 (Flapjack.WordRegImm.reg 18) sourceBody540_15 sourceBody540_16

def sourceBody540_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_17 sourceBody540_4

def sourceBody540_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody540_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody540_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody540_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 2) sourceBody540_21 sourceBody540_19

def sourceBody540_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_22 sourceBody540_4

def sourceBody540_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody540_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody540_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody540_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody540_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 24) sourceBody540_26 sourceBody540_27

def sourceBody540_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_28 sourceBody540_4

def sourceBody540_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody540_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody540_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody540_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 14) sourceBody540_32 sourceBody540_30

def sourceBody540_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_33 sourceBody540_4

def sourceBody540_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.var 20])

def sourceBody540_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody540_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 22)

def sourceBody540_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_37 sourceBody540_0

def sourceBody540_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_38 sourceBody540_0

def sourceBody540_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_36 sourceBody540_39

def sourceBody540_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_40

def sourceBody540_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody540_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_42 sourceBody540_2

def sourceBody540_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_41 sourceBody540_43

def sourceBody540_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody540_44 sourceBody540_0

def sourceBody540_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_45 sourceBody540_4

def sourceBody540_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_46 sourceBody540_0

def sourceBody540_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_35 sourceBody540_47

def sourceBody540_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_34 sourceBody540_48

def sourceBody540_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_31 sourceBody540_49

def sourceBody540_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_30 sourceBody540_50

def sourceBody540_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_29 sourceBody540_51

def sourceBody540_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_25 sourceBody540_52

def sourceBody540_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_24 sourceBody540_53

def sourceBody540_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_23 sourceBody540_54

def sourceBody540_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_20 sourceBody540_55

def sourceBody540_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_19 sourceBody540_56

def sourceBody540_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_18 sourceBody540_57

def sourceBody540_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_14 sourceBody540_58

def sourceBody540_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_13 sourceBody540_59

def sourceBody540_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 143#64])

def sourceBody540_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 22)
    (Flapjack.WordLangExpHOL.const 4#64))

def sourceBody540_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 15#64])

def sourceBody540_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody540_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody540_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody540_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody540_68 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 10) sourceBody540_66 sourceBody540_67

def sourceBody540_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_68 sourceBody540_4

def sourceBody540_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody540_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody540_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_71 sourceBody540_0

def sourceBody540_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_72 sourceBody540_0

def sourceBody540_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody540_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_74 sourceBody540_0

def sourceBody540_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_75 sourceBody540_0

def sourceBody540_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_73 sourceBody540_76

def sourceBody540_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody540_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_78 sourceBody540_0

def sourceBody540_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_79 sourceBody540_0

def sourceBody540_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.const 29#64, Flapjack.WordLangExpHOL.var 4])

def sourceBody540_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_81 sourceBody540_0

def sourceBody540_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_82 sourceBody540_0

def sourceBody540_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_80 sourceBody540_83

def sourceBody540_85 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody540_77 sourceBody540_84

def sourceBody540_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_85 sourceBody540_4

def sourceBody540_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_86 sourceBody540_0

def sourceBody540_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_70 sourceBody540_87

def sourceBody540_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_69 sourceBody540_88

def sourceBody540_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_65 sourceBody540_89

def sourceBody540_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_64 sourceBody540_90

def sourceBody540_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody540_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 26)

def sourceBody540_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody540_95 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody540_0, 540, 6)) (some 93) ([16, 10]) (some (16, sourceBody540_94, 540, 7))

def sourceBody540_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_95 sourceBody540_4

def sourceBody540_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_96 sourceBody540_0

def sourceBody540_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_93 sourceBody540_97

def sourceBody540_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_92 sourceBody540_98

def sourceBody540_100 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody540_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody540_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody540_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody540_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def sourceBody540_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_104 sourceBody540_0

def sourceBody540_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_105 sourceBody540_0

def sourceBody540_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_103 sourceBody540_106

def sourceBody540_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_107

def sourceBody540_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody540_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_109 sourceBody540_94

def sourceBody540_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_108 sourceBody540_110

def sourceBody540_112 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody540_111 sourceBody540_0

def sourceBody540_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_112 sourceBody540_4

def sourceBody540_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_113 sourceBody540_0

def sourceBody540_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_102 sourceBody540_114

def sourceBody540_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_29 sourceBody540_115

def sourceBody540_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_101 sourceBody540_116

def sourceBody540_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_100 sourceBody540_117

def sourceBody540_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody540_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody540_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody540_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody540_0, 540, 8)) (some 534) ([10, 24]) (some (10, sourceBody540_121, 540, 9))

def sourceBody540_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_122 sourceBody540_4

def sourceBody540_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_123 sourceBody540_0

def sourceBody540_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_120 sourceBody540_124

def sourceBody540_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_119 sourceBody540_125

def sourceBody540_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_126

def sourceBody540_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_127

def sourceBody540_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_118 sourceBody540_128

def sourceBody540_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody540_131 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody540_0, 540, 10)) (some 486) ([10]) (some (10, sourceBody540_121, 540, 11))

def sourceBody540_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_131 sourceBody540_4

def sourceBody540_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_132 sourceBody540_0

def sourceBody540_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_130 sourceBody540_133

def sourceBody540_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_134

def sourceBody540_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_135

def sourceBody540_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_129 sourceBody540_136

def sourceBody540_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody540_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_138 sourceBody540_0

def sourceBody540_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_67 sourceBody540_139

def sourceBody540_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_137 sourceBody540_140

def sourceBody540_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_99 sourceBody540_141

def sourceBody540_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_142

def sourceBody540_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_143

def sourceBody540_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_91 sourceBody540_144

def sourceBody540_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_145

def sourceBody540_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_146

def sourceBody540_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_147

def sourceBody540_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_148

def sourceBody540_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_63 sourceBody540_149

def sourceBody540_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_150

def sourceBody540_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_62 sourceBody540_151

def sourceBody540_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_152

def sourceBody540_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_61 sourceBody540_153

def sourceBody540_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_154

def sourceBody540_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_60 sourceBody540_155

def sourceBody540_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_12 sourceBody540_156

def sourceBody540_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_157

def sourceBody540_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_0 sourceBody540_158

def sourceBody540_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody540_9 sourceBody540_159

def source540 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (540, 1, sourceBody540_160)
end InitECandidate.Proofs.WordStages
