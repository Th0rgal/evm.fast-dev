import InitECandidate.Proofs.WordStages.Source681
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody697_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody697_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody697_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 150#64)

def sourceBody697_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody697_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody697_0, 697, 2)) (some 466) ([4]) (some (4, sourceBody697_3, 697, 3))

def sourceBody697_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody697_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_4 sourceBody697_5

def sourceBody697_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_6 sourceBody697_0

def sourceBody697_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_2 sourceBody697_7

def sourceBody697_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_8

def sourceBody697_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_9

def sourceBody697_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody697_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody697_0, 697, 4)) (some 68) ([4]) (some (4, sourceBody697_3, 697, 5))

def sourceBody697_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_12 sourceBody697_5

def sourceBody697_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_13 sourceBody697_0

def sourceBody697_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_11 sourceBody697_14

def sourceBody697_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody697_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody697_0, 697, 6)) (some 69) ([]) (some (14, sourceBody697_16, 697, 7))

def sourceBody697_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_17 sourceBody697_5

def sourceBody697_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_18 sourceBody697_0

def sourceBody697_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody697_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody697_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody697_0, 697, 8)) (some 68) ([10]) (some (10, sourceBody697_21, 697, 9))

def sourceBody697_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_22 sourceBody697_5

def sourceBody697_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_23 sourceBody697_0

def sourceBody697_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_20 sourceBody697_24

def sourceBody697_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody697_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody697_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody697_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody697_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody697_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody697_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody697_0, 697, 10)) (some 480) ([20, 2, 12, 8, 18]) (some (20, sourceBody697_31, 697, 11))

def sourceBody697_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_32 sourceBody697_5

def sourceBody697_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_33 sourceBody697_0

def sourceBody697_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_30 sourceBody697_34

def sourceBody697_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_29 sourceBody697_35

def sourceBody697_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_28 sourceBody697_36

def sourceBody697_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_27 sourceBody697_37

def sourceBody697_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_26 sourceBody697_38

def sourceBody697_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_39

def sourceBody697_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_40

def sourceBody697_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody697_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody697_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody697_0, 697, 12)) (some 694) ([20, 2]) (some (20, sourceBody697_31, 697, 13))

def sourceBody697_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_44 sourceBody697_5

def sourceBody697_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_45 sourceBody697_0

def sourceBody697_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_43 sourceBody697_46

def sourceBody697_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_42 sourceBody697_47

def sourceBody697_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody697_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody697_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody697_0, 697, 14)) (some 70) ([2]) (some (2, sourceBody697_50, 697, 15))

def sourceBody697_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_51 sourceBody697_5

def sourceBody697_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_52 sourceBody697_0

def sourceBody697_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_49 sourceBody697_53

def sourceBody697_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_54

def sourceBody697_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_55

def sourceBody697_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody697_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody697_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody697_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.reg 12) sourceBody697_58 sourceBody697_59

def sourceBody697_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_60 sourceBody697_5

def sourceBody697_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody697_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody697_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody697_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_64 sourceBody697_0

def sourceBody697_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_65 sourceBody697_0

def sourceBody697_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_63 sourceBody697_66

def sourceBody697_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_67

def sourceBody697_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody697_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_69 sourceBody697_31

def sourceBody697_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_68 sourceBody697_70

def sourceBody697_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody697_71 sourceBody697_0

def sourceBody697_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_72 sourceBody697_5

def sourceBody697_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_73 sourceBody697_0

def sourceBody697_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_62 sourceBody697_74

def sourceBody697_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_61 sourceBody697_75

def sourceBody697_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_28 sourceBody697_76

def sourceBody697_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_57 sourceBody697_77

def sourceBody697_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_56 sourceBody697_78

def sourceBody697_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody697_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody697_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 12

def sourceBody697_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_82 sourceBody697_0

def sourceBody697_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_81 sourceBody697_83

def sourceBody697_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_84 sourceBody697_0

def sourceBody697_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_43 sourceBody697_85

def sourceBody697_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_86

def sourceBody697_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_80 sourceBody697_87

def sourceBody697_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_88

def sourceBody697_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_79 sourceBody697_89

def sourceBody697_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody697_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody697_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_92 sourceBody697_85

def sourceBody697_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_93

def sourceBody697_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_91 sourceBody697_94

def sourceBody697_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_95

def sourceBody697_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_90 sourceBody697_96

def sourceBody697_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody697_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody697_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_99 sourceBody697_0

def sourceBody697_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_98 sourceBody697_100

def sourceBody697_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_97 sourceBody697_101

def sourceBody697_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_48 sourceBody697_102

def sourceBody697_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_103

def sourceBody697_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_104

def sourceBody697_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_41 sourceBody697_105

def sourceBody697_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_25 sourceBody697_106

def sourceBody697_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_107

def sourceBody697_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_108

def sourceBody697_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_19 sourceBody697_109

def sourceBody697_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_110

def sourceBody697_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_111

def sourceBody697_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_15 sourceBody697_112

def sourceBody697_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_113

def sourceBody697_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_114

def sourceBody697_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_10 sourceBody697_115

def sourceBody697_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_1 sourceBody697_116

def sourceBody697_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody697_0 sourceBody697_117

def source697 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (697, 1, sourceBody697_118)
end InitECandidate.Proofs.WordStages
