import InitECandidate.Proofs.WordStages.Source366
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody382_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody382_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody382_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody382_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody382_0, 382, 2)) (some 68) ([16]) (some (16, sourceBody382_2, 382, 3))

def sourceBody382_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody382_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_3 sourceBody382_4

def sourceBody382_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_5 sourceBody382_0

def sourceBody382_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_1 sourceBody382_6

def sourceBody382_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 168#64])

def sourceBody382_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody382_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody382_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 18

def sourceBody382_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_11 sourceBody382_0

def sourceBody382_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_10 sourceBody382_12

def sourceBody382_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_13 sourceBody382_0

def sourceBody382_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_9 sourceBody382_14

def sourceBody382_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_15

def sourceBody382_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_8 sourceBody382_16

def sourceBody382_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_17

def sourceBody382_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_7 sourceBody382_18

def sourceBody382_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_19

def sourceBody382_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_20

def sourceBody382_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 168#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody382_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody382_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody382_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 12

def sourceBody382_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_25 sourceBody382_0

def sourceBody382_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_24 sourceBody382_26

def sourceBody382_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_27 sourceBody382_0

def sourceBody382_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_23 sourceBody382_28

def sourceBody382_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_29

def sourceBody382_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_22 sourceBody382_30

def sourceBody382_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_31

def sourceBody382_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_21 sourceBody382_32

def sourceBody382_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 168#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody382_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody382_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_35 sourceBody382_28

def sourceBody382_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_36

def sourceBody382_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_34 sourceBody382_37

def sourceBody382_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_38

def sourceBody382_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_33 sourceBody382_39

def sourceBody382_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 168#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody382_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody382_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_42 sourceBody382_28

def sourceBody382_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_43

def sourceBody382_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_41 sourceBody382_44

def sourceBody382_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_45

def sourceBody382_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_40 sourceBody382_46

def sourceBody382_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody382_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 4)) (some 301) ([16, 12]) (some (16, sourceBody382_2, 382, 5))

def sourceBody382_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_49 sourceBody382_4

def sourceBody382_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_50 sourceBody382_0

def sourceBody382_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_48 sourceBody382_51

def sourceBody382_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_23 sourceBody382_52

def sourceBody382_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 168#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody382_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_54 sourceBody382_16

def sourceBody382_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_55

def sourceBody382_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody382_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody382_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody382_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 6)) (some 182) ([12, 18]) (some (12, sourceBody382_59, 382, 7))

def sourceBody382_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_60 sourceBody382_4

def sourceBody382_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_61 sourceBody382_0

def sourceBody382_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_58 sourceBody382_62

def sourceBody382_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_57 sourceBody382_63

def sourceBody382_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 168#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody382_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody382_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody382_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 8

def sourceBody382_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_68 sourceBody382_0

def sourceBody382_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_67 sourceBody382_69

def sourceBody382_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_70 sourceBody382_0

def sourceBody382_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_66 sourceBody382_71

def sourceBody382_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_72

def sourceBody382_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_65 sourceBody382_73

def sourceBody382_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_74

def sourceBody382_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 80#64)

def sourceBody382_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody382_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 8)) (some 68) ([18]) (some (18, sourceBody382_77, 382, 9))

def sourceBody382_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_78 sourceBody382_4

def sourceBody382_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_79 sourceBody382_0

def sourceBody382_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_76 sourceBody382_80

def sourceBody382_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 176#64])

def sourceBody382_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody382_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody382_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 14

def sourceBody382_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_85 sourceBody382_0

def sourceBody382_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_84 sourceBody382_86

def sourceBody382_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_87 sourceBody382_0

def sourceBody382_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_83 sourceBody382_88

def sourceBody382_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_89

def sourceBody382_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_82 sourceBody382_90

def sourceBody382_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_91

def sourceBody382_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_81 sourceBody382_92

def sourceBody382_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_93

def sourceBody382_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_94

def sourceBody382_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_75 sourceBody382_95

def sourceBody382_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody382_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody382_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_98 sourceBody382_71

def sourceBody382_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_99

def sourceBody382_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_97 sourceBody382_100

def sourceBody382_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_101

def sourceBody382_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_96 sourceBody382_102

def sourceBody382_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody382_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody382_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 10)) (some 182) ([12, 18]) (some (12, sourceBody382_59, 382, 11))

def sourceBody382_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_106 sourceBody382_4

def sourceBody382_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_107 sourceBody382_0

def sourceBody382_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_105 sourceBody382_108

def sourceBody382_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_104 sourceBody382_109

def sourceBody382_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_103 sourceBody382_110

def sourceBody382_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody382_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_112 sourceBody382_73

def sourceBody382_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_113

def sourceBody382_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_111 sourceBody382_114

def sourceBody382_116 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 12)) (some 182) ([12, 18]) (some (12, sourceBody382_59, 382, 13))

def sourceBody382_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_116 sourceBody382_4

def sourceBody382_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_117 sourceBody382_0

def sourceBody382_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_105 sourceBody382_118

def sourceBody382_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_104 sourceBody382_119

def sourceBody382_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_115 sourceBody382_120

def sourceBody382_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody382_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_122 sourceBody382_73

def sourceBody382_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_123

def sourceBody382_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_121 sourceBody382_124

def sourceBody382_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 52#64)

def sourceBody382_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 14)) (some 182) ([12, 18]) (some (12, sourceBody382_59, 382, 15))

def sourceBody382_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_127 sourceBody382_4

def sourceBody382_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_128 sourceBody382_0

def sourceBody382_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_105 sourceBody382_129

def sourceBody382_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_126 sourceBody382_130

def sourceBody382_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_125 sourceBody382_131

def sourceBody382_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody382_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_133 sourceBody382_73

def sourceBody382_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_134

def sourceBody382_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_132 sourceBody382_135

def sourceBody382_137 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 16)) (some 182) ([12, 18]) (some (12, sourceBody382_59, 382, 17))

def sourceBody382_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_137 sourceBody382_4

def sourceBody382_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_138 sourceBody382_0

def sourceBody382_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_58 sourceBody382_139

def sourceBody382_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_104 sourceBody382_140

def sourceBody382_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_136 sourceBody382_141

def sourceBody382_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody382_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_143 sourceBody382_73

def sourceBody382_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_144

def sourceBody382_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_142 sourceBody382_145

def sourceBody382_147 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 18)) (some 182) ([12, 18]) (some (12, sourceBody382_59, 382, 19))

def sourceBody382_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_147 sourceBody382_4

def sourceBody382_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_148 sourceBody382_0

def sourceBody382_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_58 sourceBody382_149

def sourceBody382_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_126 sourceBody382_150

def sourceBody382_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_146 sourceBody382_151

def sourceBody382_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody382_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_153 sourceBody382_73

def sourceBody382_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_154

def sourceBody382_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_152 sourceBody382_155

def sourceBody382_157 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 20)) (some 182) ([12, 18]) (some (12, sourceBody382_59, 382, 21))

def sourceBody382_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_157 sourceBody382_4

def sourceBody382_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_158 sourceBody382_0

def sourceBody382_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_58 sourceBody382_159

def sourceBody382_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_57 sourceBody382_160

def sourceBody382_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_156 sourceBody382_161

def sourceBody382_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody382_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_163 sourceBody382_73

def sourceBody382_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_164

def sourceBody382_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_162 sourceBody382_165

def sourceBody382_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody382_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody382_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_168 sourceBody382_71

def sourceBody382_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_169

def sourceBody382_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_167 sourceBody382_170

def sourceBody382_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_171

def sourceBody382_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_166 sourceBody382_172

def sourceBody382_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody382_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_174 sourceBody382_170

def sourceBody382_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_175

def sourceBody382_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_173 sourceBody382_176

def sourceBody382_178 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 22)) (some 182) ([12, 18]) (some (12, sourceBody382_59, 382, 23))

def sourceBody382_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_178 sourceBody382_4

def sourceBody382_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_179 sourceBody382_0

def sourceBody382_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_105 sourceBody382_180

def sourceBody382_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_104 sourceBody382_181

def sourceBody382_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_177 sourceBody382_182

def sourceBody382_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 176#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody382_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_184 sourceBody382_73

def sourceBody382_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_185

def sourceBody382_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_183 sourceBody382_186

def sourceBody382_188 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 24)) (some 68) ([18]) (some (18, sourceBody382_77, 382, 25))

def sourceBody382_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_188 sourceBody382_4

def sourceBody382_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_189 sourceBody382_0

def sourceBody382_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_58 sourceBody382_190

def sourceBody382_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 192#64])

def sourceBody382_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_192 sourceBody382_90

def sourceBody382_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_193

def sourceBody382_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_191 sourceBody382_194

def sourceBody382_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_195

def sourceBody382_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_196

def sourceBody382_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_187 sourceBody382_197

def sourceBody382_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 208#64])

def sourceBody382_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 524288#64)

def sourceBody382_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_200 sourceBody382_71

def sourceBody382_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_201

def sourceBody382_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_199 sourceBody382_202

def sourceBody382_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_203

def sourceBody382_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_198 sourceBody382_204

def sourceBody382_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
    (Flapjack.WordLangExpHOL.load
      (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
          Flapjack.WordLangExpHOL.const 208#64]))
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody382_207 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody382_0, 382, 26)) (some 68) ([18]) (some (18, sourceBody382_77, 382, 27))

def sourceBody382_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_207 sourceBody382_4

def sourceBody382_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_208 sourceBody382_0

def sourceBody382_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_206 sourceBody382_209

def sourceBody382_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 200#64])

def sourceBody382_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_211 sourceBody382_90

def sourceBody382_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_212

def sourceBody382_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_210 sourceBody382_213

def sourceBody382_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_214

def sourceBody382_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_215

def sourceBody382_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_205 sourceBody382_216

def sourceBody382_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody382_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_218 sourceBody382_170

def sourceBody382_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_219

def sourceBody382_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_217 sourceBody382_220

def sourceBody382_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 184#64])

def sourceBody382_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_222 sourceBody382_170

def sourceBody382_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_223

def sourceBody382_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_221 sourceBody382_224

def sourceBody382_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody382_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody382_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_227 sourceBody382_0

def sourceBody382_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_226 sourceBody382_228

def sourceBody382_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_225 sourceBody382_229

def sourceBody382_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_64 sourceBody382_230

def sourceBody382_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_231

def sourceBody382_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_232

def sourceBody382_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_56 sourceBody382_233

def sourceBody382_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_53 sourceBody382_234

def sourceBody382_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_235

def sourceBody382_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_0 sourceBody382_236

def sourceBody382_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody382_47 sourceBody382_237

def source382 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (382, 4, sourceBody382_238)
end InitECandidate.Proofs.WordStages
