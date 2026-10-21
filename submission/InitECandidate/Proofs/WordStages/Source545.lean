import InitECandidate.Proofs.WordStages.Source529
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody545_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody545_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody545_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 26, 6, 22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody545_0, 545, 2)) (some 471) ([]) (some (14, sourceBody545_1, 545, 3))

def sourceBody545_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody545_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_2 sourceBody545_3

def sourceBody545_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_4 sourceBody545_0

def sourceBody545_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 280#64]))

def sourceBody545_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody545_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody545_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody545_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody545_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody545_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody545_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody545_0, 545, 4)) (some 147) ([4, 20, 12, 28, 8]) (some (4, sourceBody545_12, 545, 5))

def sourceBody545_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_13 sourceBody545_3

def sourceBody545_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_14 sourceBody545_0

def sourceBody545_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_11 sourceBody545_15

def sourceBody545_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_10 sourceBody545_16

def sourceBody545_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_9 sourceBody545_17

def sourceBody545_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_8 sourceBody545_18

def sourceBody545_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_7 sourceBody545_19

def sourceBody545_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_20

def sourceBody545_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_21

def sourceBody545_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.load
                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                  [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                      [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                          (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                          (Flapjack.WordLangExpHOL.const 1#64)],
                    Flapjack.WordLangExpHOL.const 256#64]),
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody545_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody545_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody545_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody545_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody545_0, 545, 6)) (some 543) ([20, 12]) (some (20, sourceBody545_26, 545, 7))

def sourceBody545_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_27 sourceBody545_3

def sourceBody545_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_28 sourceBody545_0

def sourceBody545_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_25 sourceBody545_29

def sourceBody545_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_24 sourceBody545_30

def sourceBody545_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody545_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody545_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody545_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody545_36 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 28) sourceBody545_34 sourceBody545_35

def sourceBody545_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_36 sourceBody545_3

def sourceBody545_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody545_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 100#64)

def sourceBody545_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody545_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody545_0, 545, 8)) (some 466) ([12]) (some (12, sourceBody545_40, 545, 9))

def sourceBody545_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_41 sourceBody545_3

def sourceBody545_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_42 sourceBody545_0

def sourceBody545_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_39 sourceBody545_43

def sourceBody545_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_44

def sourceBody545_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_45

def sourceBody545_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 2100#64)

def sourceBody545_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody545_0, 545, 10)) (some 466) ([12]) (some (12, sourceBody545_40, 545, 11))

def sourceBody545_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_48 sourceBody545_3

def sourceBody545_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_49 sourceBody545_0

def sourceBody545_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_47 sourceBody545_50

def sourceBody545_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_51

def sourceBody545_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_52

def sourceBody545_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody545_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody545_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody545_0, 545, 12)) (some 544) ([12, 28]) (some (12, sourceBody545_40, 545, 13))

def sourceBody545_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_56 sourceBody545_3

def sourceBody545_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_57 sourceBody545_0

def sourceBody545_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_55 sourceBody545_58

def sourceBody545_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_54 sourceBody545_59

def sourceBody545_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_60

def sourceBody545_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_61

def sourceBody545_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_53 sourceBody545_62

def sourceBody545_64 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody545_46 sourceBody545_63

def sourceBody545_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_64 sourceBody545_3

def sourceBody545_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_65 sourceBody545_0

def sourceBody545_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_38 sourceBody545_66

def sourceBody545_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_37 sourceBody545_67

def sourceBody545_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_33 sourceBody545_68

def sourceBody545_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_32 sourceBody545_69

def sourceBody545_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody545_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody545_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody545_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 12, 28, 8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody545_0, 545, 14)) (some 406) ([24, 16]) (some (24, sourceBody545_73, 545, 15))

def sourceBody545_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_74 sourceBody545_3

def sourceBody545_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_75 sourceBody545_0

def sourceBody545_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_72 sourceBody545_76

def sourceBody545_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_71 sourceBody545_77

def sourceBody545_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody545_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody545_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 28)

def sourceBody545_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody545_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody545_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody545_0, 545, 16)) (some 472) ([16, 32, 2, 18]) (some (16, sourceBody545_83, 545, 17))

def sourceBody545_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_84 sourceBody545_3

def sourceBody545_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_85 sourceBody545_0

def sourceBody545_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_82 sourceBody545_86

def sourceBody545_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_81 sourceBody545_87

def sourceBody545_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_80 sourceBody545_88

def sourceBody545_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_79 sourceBody545_89

def sourceBody545_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_90

def sourceBody545_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_91

def sourceBody545_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody545_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody545_0, 545, 18)) (some 486) ([16]) (some (16, sourceBody545_83, 545, 19))

def sourceBody545_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_94 sourceBody545_3

def sourceBody545_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_95 sourceBody545_0

def sourceBody545_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_93 sourceBody545_96

def sourceBody545_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_97

def sourceBody545_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_98

def sourceBody545_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_92 sourceBody545_99

def sourceBody545_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody545_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody545_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_102 sourceBody545_0

def sourceBody545_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_101 sourceBody545_103

def sourceBody545_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_100 sourceBody545_104

def sourceBody545_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_78 sourceBody545_105

def sourceBody545_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_106

def sourceBody545_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_107

def sourceBody545_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_108

def sourceBody545_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_109

def sourceBody545_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_110

def sourceBody545_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_111

def sourceBody545_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_112

def sourceBody545_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_113

def sourceBody545_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_70 sourceBody545_114

def sourceBody545_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_31 sourceBody545_115

def sourceBody545_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_116

def sourceBody545_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_117

def sourceBody545_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_23 sourceBody545_118

def sourceBody545_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_119

def sourceBody545_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_22 sourceBody545_120

def sourceBody545_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_6 sourceBody545_121

def sourceBody545_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_122

def sourceBody545_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_5 sourceBody545_123

def sourceBody545_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_124

def sourceBody545_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_125

def sourceBody545_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_126

def sourceBody545_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_127

def sourceBody545_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_128

def sourceBody545_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_129

def sourceBody545_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_130

def sourceBody545_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody545_0 sourceBody545_131

def source545 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (545, 1, sourceBody545_132)
end InitECandidate.Proofs.WordStages
