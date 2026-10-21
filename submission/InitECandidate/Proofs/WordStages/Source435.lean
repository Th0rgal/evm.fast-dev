import InitECandidate.Proofs.WordStages.Source419
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody435_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody435_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody435_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody435_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody435_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 18]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody435_0, 435, 2)) (some 186) ([6, 16]) (some (6, sourceBody435_3, 435, 3))

def sourceBody435_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody435_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_4 sourceBody435_5

def sourceBody435_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_6 sourceBody435_0

def sourceBody435_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_2 sourceBody435_7

def sourceBody435_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_1 sourceBody435_8

def sourceBody435_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody435_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody435_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody435_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody435_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 12) sourceBody435_12 sourceBody435_13

def sourceBody435_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_14 sourceBody435_5

def sourceBody435_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody435_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody435_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody435_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_18 sourceBody435_0

def sourceBody435_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_17 sourceBody435_19

def sourceBody435_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody435_20 sourceBody435_0

def sourceBody435_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_21 sourceBody435_5

def sourceBody435_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_22 sourceBody435_0

def sourceBody435_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_16 sourceBody435_23

def sourceBody435_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_15 sourceBody435_24

def sourceBody435_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_11 sourceBody435_25

def sourceBody435_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_10 sourceBody435_26

def sourceBody435_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody435_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody435_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody435_0, 435, 4)) (some 68) ([16]) (some (16, sourceBody435_29, 435, 5))

def sourceBody435_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_30 sourceBody435_5

def sourceBody435_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_31 sourceBody435_0

def sourceBody435_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_28 sourceBody435_32

def sourceBody435_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody435_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody435_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody435_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody435_0, 435, 6)) (some 182) ([12, 20]) (some (12, sourceBody435_36, 435, 7))

def sourceBody435_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_37 sourceBody435_5

def sourceBody435_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_38 sourceBody435_0

def sourceBody435_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_35 sourceBody435_39

def sourceBody435_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_34 sourceBody435_40

def sourceBody435_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody435_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 20)

def sourceBody435_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 4

def sourceBody435_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_44 sourceBody435_0

def sourceBody435_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_43 sourceBody435_45

def sourceBody435_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_46 sourceBody435_0

def sourceBody435_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_16 sourceBody435_47

def sourceBody435_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_48

def sourceBody435_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_42 sourceBody435_49

def sourceBody435_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_50

def sourceBody435_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody435_0, 435, 8)) (some 182) ([12, 20]) (some (12, sourceBody435_36, 435, 9))

def sourceBody435_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_52 sourceBody435_5

def sourceBody435_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_53 sourceBody435_0

def sourceBody435_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_35 sourceBody435_54

def sourceBody435_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_34 sourceBody435_55

def sourceBody435_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_51 sourceBody435_56

def sourceBody435_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody435_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_58 sourceBody435_49

def sourceBody435_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_59

def sourceBody435_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_57 sourceBody435_60

def sourceBody435_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody435_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody435_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody435_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody435_0, 435, 10)) (some 431) ([20, 4]) (some (20, sourceBody435_64, 435, 11))

def sourceBody435_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_65 sourceBody435_5

def sourceBody435_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_66 sourceBody435_0

def sourceBody435_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_63 sourceBody435_67

def sourceBody435_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_62 sourceBody435_68

def sourceBody435_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody435_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody435_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody435_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 14

def sourceBody435_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_73 sourceBody435_0

def sourceBody435_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_72 sourceBody435_74

def sourceBody435_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_75 sourceBody435_0

def sourceBody435_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_71 sourceBody435_76

def sourceBody435_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_77

def sourceBody435_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_70 sourceBody435_78

def sourceBody435_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_79

def sourceBody435_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody435_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody435_0, 435, 12)) (some 431) ([20, 4]) (some (20, sourceBody435_64, 435, 13))

def sourceBody435_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_82 sourceBody435_5

def sourceBody435_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_83 sourceBody435_0

def sourceBody435_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_63 sourceBody435_84

def sourceBody435_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_81 sourceBody435_85

def sourceBody435_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_80 sourceBody435_86

def sourceBody435_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody435_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_88 sourceBody435_78

def sourceBody435_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_89

def sourceBody435_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_87 sourceBody435_90

def sourceBody435_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody435_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody435_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody435_0, 435, 14)) (some 431) ([20, 4]) (some (20, sourceBody435_64, 435, 15))

def sourceBody435_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_94 sourceBody435_5

def sourceBody435_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_95 sourceBody435_0

def sourceBody435_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_93 sourceBody435_96

def sourceBody435_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_92 sourceBody435_97

def sourceBody435_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_91 sourceBody435_98

def sourceBody435_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody435_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_100 sourceBody435_78

def sourceBody435_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_101

def sourceBody435_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_99 sourceBody435_102

def sourceBody435_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody435_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody435_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody435_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody435_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody435_0, 435, 16)) (some 192) ([4, 14, 10]) (some (4, sourceBody435_107, 435, 17))

def sourceBody435_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_108 sourceBody435_5

def sourceBody435_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_109 sourceBody435_0

def sourceBody435_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_106 sourceBody435_110

def sourceBody435_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_105 sourceBody435_111

def sourceBody435_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_104 sourceBody435_112

def sourceBody435_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_113

def sourceBody435_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_114

def sourceBody435_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_103 sourceBody435_115

def sourceBody435_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody435_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody435_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_118 sourceBody435_0

def sourceBody435_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_117 sourceBody435_119

def sourceBody435_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_116 sourceBody435_120

def sourceBody435_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_69 sourceBody435_121

def sourceBody435_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_122

def sourceBody435_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_123

def sourceBody435_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_61 sourceBody435_124

def sourceBody435_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_41 sourceBody435_125

def sourceBody435_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_126

def sourceBody435_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_127

def sourceBody435_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_33 sourceBody435_128

def sourceBody435_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_129

def sourceBody435_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_130

def sourceBody435_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_27 sourceBody435_131

def sourceBody435_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_9 sourceBody435_132

def sourceBody435_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_133

def sourceBody435_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_134

def sourceBody435_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_135

def sourceBody435_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody435_0 sourceBody435_136

def source435 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (435, 2, sourceBody435_137)
end InitECandidate.Proofs.WordStages
