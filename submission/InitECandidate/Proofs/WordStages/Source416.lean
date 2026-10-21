import InitECandidate.Proofs.WordStages.Source400
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody416_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody416_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody416_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody416_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody416_0, 416, 2)) (some 402) ([16]) (some (16, sourceBody416_2, 416, 3))

def sourceBody416_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody416_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_3 sourceBody416_4

def sourceBody416_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_5 sourceBody416_0

def sourceBody416_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_1 sourceBody416_6

def sourceBody416_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody416_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody416_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody416_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody416_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 22) sourceBody416_10 sourceBody416_11

def sourceBody416_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_12 sourceBody416_4

def sourceBody416_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 28)

def sourceBody416_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody416_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def sourceBody416_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_16 sourceBody416_0

def sourceBody416_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_17 sourceBody416_0

def sourceBody416_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_15 sourceBody416_18

def sourceBody416_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_19

def sourceBody416_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody416_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_21 sourceBody416_2

def sourceBody416_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_20 sourceBody416_22

def sourceBody416_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody416_23 sourceBody416_0

def sourceBody416_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_24 sourceBody416_4

def sourceBody416_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_25 sourceBody416_0

def sourceBody416_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_14 sourceBody416_26

def sourceBody416_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_13 sourceBody416_27

def sourceBody416_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_9 sourceBody416_28

def sourceBody416_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_8 sourceBody416_29

def sourceBody416_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody416_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 16)

def sourceBody416_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody416_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody416_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody416_0, 416, 4)) (some 186) ([32, 18]) (some (32, sourceBody416_34, 416, 5))

def sourceBody416_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_35 sourceBody416_4

def sourceBody416_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_36 sourceBody416_0

def sourceBody416_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_33 sourceBody416_37

def sourceBody416_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_32 sourceBody416_38

def sourceBody416_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody416_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody416_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody416_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody416_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 30 (Flapjack.WordRegImm.reg 24) sourceBody416_42 sourceBody416_43

def sourceBody416_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_44 sourceBody416_4

def sourceBody416_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 30)

def sourceBody416_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody416_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody416_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody416_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody416_0, 416, 6)) (some 182) ([18, 30]) (some (18, sourceBody416_49, 416, 7))

def sourceBody416_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_50 sourceBody416_4

def sourceBody416_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_51 sourceBody416_0

def sourceBody416_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_48 sourceBody416_52

def sourceBody416_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_47 sourceBody416_53

def sourceBody416_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody416_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody416_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 32)

def sourceBody416_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody416_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody416_0, 416, 8)) (some 384) ([30, 24, 36]) (some (30, sourceBody416_58, 416, 9))

def sourceBody416_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_59 sourceBody416_4

def sourceBody416_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_60 sourceBody416_0

def sourceBody416_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_57 sourceBody416_61

def sourceBody416_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_56 sourceBody416_62

def sourceBody416_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_55 sourceBody416_63

def sourceBody416_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_64

def sourceBody416_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_65

def sourceBody416_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_54 sourceBody416_66

def sourceBody416_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody416_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_68 sourceBody416_0

def sourceBody416_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_69 sourceBody416_0

def sourceBody416_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody416_67 sourceBody416_70

def sourceBody416_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_71 sourceBody416_4

def sourceBody416_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_72 sourceBody416_0

def sourceBody416_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_46 sourceBody416_73

def sourceBody416_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_45 sourceBody416_74

def sourceBody416_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_41 sourceBody416_75

def sourceBody416_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_40 sourceBody416_76

def sourceBody416_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody416_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody416_0, 416, 10)) (some 68) ([30]) (some (30, sourceBody416_58, 416, 11))

def sourceBody416_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_79 sourceBody416_4

def sourceBody416_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_80 sourceBody416_0

def sourceBody416_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_78 sourceBody416_81

def sourceBody416_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody416_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody416_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 8)

def sourceBody416_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody416_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 12)

def sourceBody416_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody416_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 30) 20

def sourceBody416_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_89 sourceBody416_0

def sourceBody416_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_88 sourceBody416_90

def sourceBody416_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 36)

def sourceBody416_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 8#64])
  20

def sourceBody416_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_93 sourceBody416_0

def sourceBody416_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_92 sourceBody416_94

def sourceBody416_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody416_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 16#64])
  20

def sourceBody416_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_97 sourceBody416_0

def sourceBody416_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_96 sourceBody416_98

def sourceBody416_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody416_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 24#64])
  20

def sourceBody416_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_101 sourceBody416_0

def sourceBody416_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_100 sourceBody416_102

def sourceBody416_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_103 sourceBody416_0

def sourceBody416_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_99 sourceBody416_104

def sourceBody416_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_95 sourceBody416_105

def sourceBody416_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_91 sourceBody416_106

def sourceBody416_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_87 sourceBody416_107

def sourceBody416_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_108

def sourceBody416_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_86 sourceBody416_109

def sourceBody416_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_110

def sourceBody416_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_85 sourceBody416_111

def sourceBody416_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_112

def sourceBody416_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_84 sourceBody416_113

def sourceBody416_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_114

def sourceBody416_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_83 sourceBody416_115

def sourceBody416_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_116

def sourceBody416_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 32)

def sourceBody416_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 4)

def sourceBody416_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody416_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody416_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody416_0, 416, 12)) (some 384) ([24, 36, 14]) (some (24, sourceBody416_121, 416, 13))

def sourceBody416_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_122 sourceBody416_4

def sourceBody416_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_123 sourceBody416_0

def sourceBody416_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_120 sourceBody416_124

def sourceBody416_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_119 sourceBody416_125

def sourceBody416_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_118 sourceBody416_126

def sourceBody416_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_127

def sourceBody416_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_128

def sourceBody416_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_117 sourceBody416_129

def sourceBody416_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody416_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_131 sourceBody416_0

def sourceBody416_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_43 sourceBody416_132

def sourceBody416_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_130 sourceBody416_133

def sourceBody416_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_82 sourceBody416_134

def sourceBody416_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_135

def sourceBody416_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_136

def sourceBody416_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_77 sourceBody416_137

def sourceBody416_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_138

def sourceBody416_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_139

def sourceBody416_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_39 sourceBody416_140

def sourceBody416_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_141

def sourceBody416_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_142

def sourceBody416_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_143

def sourceBody416_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_144

def sourceBody416_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_31 sourceBody416_145

def sourceBody416_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_146

def sourceBody416_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_30 sourceBody416_147

def sourceBody416_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_7 sourceBody416_148

def sourceBody416_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_149

def sourceBody416_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody416_0 sourceBody416_150

def source416 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (416, 7, sourceBody416_151)
end InitECandidate.Proofs.WordStages
