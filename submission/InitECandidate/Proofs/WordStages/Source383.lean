import InitECandidate.Proofs.WordStages.Source367
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody383_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody383_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 72#64)

def sourceBody383_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody383_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 2)) (some 68) ([8]) (some (8, sourceBody383_2, 383, 3))

def sourceBody383_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody383_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_3 sourceBody383_4

def sourceBody383_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_5 sourceBody383_0

def sourceBody383_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_1 sourceBody383_6

def sourceBody383_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 184#64])

def sourceBody383_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody383_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody383_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody383_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_11 sourceBody383_0

def sourceBody383_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_10 sourceBody383_12

def sourceBody383_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_13 sourceBody383_0

def sourceBody383_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_9 sourceBody383_14

def sourceBody383_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_15

def sourceBody383_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_8 sourceBody383_16

def sourceBody383_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_17

def sourceBody383_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_7 sourceBody383_18

def sourceBody383_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_19

def sourceBody383_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_20

def sourceBody383_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody383_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 176#64]))

def sourceBody383_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody383_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 2

def sourceBody383_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_25 sourceBody383_0

def sourceBody383_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_24 sourceBody383_26

def sourceBody383_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_27 sourceBody383_0

def sourceBody383_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_23 sourceBody383_28

def sourceBody383_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_29

def sourceBody383_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_22 sourceBody383_30

def sourceBody383_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_31

def sourceBody383_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_21 sourceBody383_32

def sourceBody383_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody383_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody383_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 4)) (some 182) ([8, 2]) (some (8, sourceBody383_2, 383, 5))

def sourceBody383_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_36 sourceBody383_4

def sourceBody383_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_37 sourceBody383_0

def sourceBody383_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_35 sourceBody383_38

def sourceBody383_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_34 sourceBody383_39

def sourceBody383_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody383_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_41 sourceBody383_16

def sourceBody383_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_42

def sourceBody383_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 6)) (some 182) ([8, 2]) (some (8, sourceBody383_2, 383, 7))

def sourceBody383_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_44 sourceBody383_4

def sourceBody383_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_45 sourceBody383_0

def sourceBody383_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_35 sourceBody383_46

def sourceBody383_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_34 sourceBody383_47

def sourceBody383_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_43 sourceBody383_48

def sourceBody383_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody383_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_50 sourceBody383_16

def sourceBody383_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_51

def sourceBody383_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_49 sourceBody383_52

def sourceBody383_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 52#64)

def sourceBody383_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 8)) (some 182) ([8, 2]) (some (8, sourceBody383_2, 383, 9))

def sourceBody383_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_55 sourceBody383_4

def sourceBody383_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_56 sourceBody383_0

def sourceBody383_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_35 sourceBody383_57

def sourceBody383_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_54 sourceBody383_58

def sourceBody383_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_53 sourceBody383_59

def sourceBody383_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody383_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_61 sourceBody383_16

def sourceBody383_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_62

def sourceBody383_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_60 sourceBody383_63

def sourceBody383_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody383_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 10)) (some 182) ([8, 2]) (some (8, sourceBody383_2, 383, 11))

def sourceBody383_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_66 sourceBody383_4

def sourceBody383_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_67 sourceBody383_0

def sourceBody383_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_65 sourceBody383_68

def sourceBody383_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_34 sourceBody383_69

def sourceBody383_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_64 sourceBody383_70

def sourceBody383_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody383_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_72 sourceBody383_16

def sourceBody383_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_73

def sourceBody383_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_71 sourceBody383_74

def sourceBody383_76 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 12)) (some 182) ([8, 2]) (some (8, sourceBody383_2, 383, 13))

def sourceBody383_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_76 sourceBody383_4

def sourceBody383_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_77 sourceBody383_0

def sourceBody383_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_65 sourceBody383_78

def sourceBody383_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_54 sourceBody383_79

def sourceBody383_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_75 sourceBody383_80

def sourceBody383_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody383_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_82 sourceBody383_16

def sourceBody383_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_83

def sourceBody383_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_81 sourceBody383_84

def sourceBody383_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody383_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 14)) (some 182) ([8, 2]) (some (8, sourceBody383_2, 383, 15))

def sourceBody383_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_87 sourceBody383_4

def sourceBody383_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_88 sourceBody383_0

def sourceBody383_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_65 sourceBody383_89

def sourceBody383_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_86 sourceBody383_90

def sourceBody383_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_85 sourceBody383_91

def sourceBody383_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody383_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_93 sourceBody383_16

def sourceBody383_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_94

def sourceBody383_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_92 sourceBody383_95

def sourceBody383_97 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 16)) (some 182) ([8, 2]) (some (8, sourceBody383_2, 383, 17))

def sourceBody383_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_97 sourceBody383_4

def sourceBody383_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_98 sourceBody383_0

def sourceBody383_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_65 sourceBody383_99

def sourceBody383_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_34 sourceBody383_100

def sourceBody383_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_96 sourceBody383_101

def sourceBody383_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody383_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_103 sourceBody383_16

def sourceBody383_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_104

def sourceBody383_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_102 sourceBody383_105

def sourceBody383_107 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody383_0, 383, 18)) (some 182) ([8, 2]) (some (8, sourceBody383_2, 383, 19))

def sourceBody383_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_107 sourceBody383_4

def sourceBody383_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_108 sourceBody383_0

def sourceBody383_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_65 sourceBody383_109

def sourceBody383_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_54 sourceBody383_110

def sourceBody383_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_106 sourceBody383_111

def sourceBody383_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 184#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody383_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_113 sourceBody383_16

def sourceBody383_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_114

def sourceBody383_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_112 sourceBody383_115

def sourceBody383_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody383_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody383_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_118 sourceBody383_14

def sourceBody383_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_119

def sourceBody383_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_117 sourceBody383_120

def sourceBody383_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_121

def sourceBody383_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_116 sourceBody383_122

def sourceBody383_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody383_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody383_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_125 sourceBody383_0

def sourceBody383_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_124 sourceBody383_126

def sourceBody383_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_123 sourceBody383_127

def sourceBody383_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_40 sourceBody383_128

def sourceBody383_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_129

def sourceBody383_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_0 sourceBody383_130

def sourceBody383_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody383_33 sourceBody383_131

def source383 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (383, 1, sourceBody383_132)
end InitECandidate.Proofs.WordStages
