import InitECandidate.Proofs.WordStages.Source840
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody856_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody856_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody856_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 2)) (some 383) ([]) (some (26, sourceBody856_1, 856, 3))

def sourceBody856_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody856_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_2 sourceBody856_3

def sourceBody856_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_4 sourceBody856_0

def sourceBody856_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_5

def sourceBody856_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_6

def sourceBody856_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody856_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody856_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 4)) (some 561) ([18]) (some (18, sourceBody856_9, 856, 5))

def sourceBody856_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_10 sourceBody856_3

def sourceBody856_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_11 sourceBody856_0

def sourceBody856_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_8 sourceBody856_12

def sourceBody856_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody856_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 6)) (some 855) ([]) (some (32, sourceBody856_14, 856, 7))

def sourceBody856_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_15 sourceBody856_3

def sourceBody856_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_16 sourceBody856_0

def sourceBody856_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody856_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 304#64]))

def sourceBody856_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody856_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 24

def sourceBody856_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_21 sourceBody856_0

def sourceBody856_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_20 sourceBody856_22

def sourceBody856_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_23 sourceBody856_0

def sourceBody856_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_19 sourceBody856_24

def sourceBody856_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_25

def sourceBody856_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_18 sourceBody856_26

def sourceBody856_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_27

def sourceBody856_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody856_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody856_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_30 sourceBody856_24

def sourceBody856_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_31

def sourceBody856_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_29 sourceBody856_32

def sourceBody856_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_33

def sourceBody856_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_28 sourceBody856_34

def sourceBody856_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody856_37 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 408#64]),
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody856_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 408#64]),
            Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody856_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 408#64]),
            Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody856_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 408#64]),
            Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody856_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody856_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 14

def sourceBody856_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_42 sourceBody856_0

def sourceBody856_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_41 sourceBody856_43

def sourceBody856_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody856_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 8#64])
  14

def sourceBody856_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_46 sourceBody856_0

def sourceBody856_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_45 sourceBody856_47

def sourceBody856_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody856_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 16#64])
  14

def sourceBody856_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_50 sourceBody856_0

def sourceBody856_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_49 sourceBody856_51

def sourceBody856_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody856_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 24#64])
  14

def sourceBody856_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_54 sourceBody856_0

def sourceBody856_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_53 sourceBody856_55

def sourceBody856_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_56 sourceBody856_0

def sourceBody856_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_52 sourceBody856_57

def sourceBody856_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_48 sourceBody856_58

def sourceBody856_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_44 sourceBody856_59

def sourceBody856_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_40 sourceBody856_60

def sourceBody856_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_61

def sourceBody856_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_39 sourceBody856_62

def sourceBody856_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_63

def sourceBody856_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_38 sourceBody856_64

def sourceBody856_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_65

def sourceBody856_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_37 sourceBody856_66

def sourceBody856_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_67

def sourceBody856_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_36 sourceBody856_68

def sourceBody856_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_69

def sourceBody856_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_35 sourceBody856_70

def sourceBody856_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody856_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 30000000#64)

def sourceBody856_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_73 sourceBody856_24

def sourceBody856_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_74

def sourceBody856_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_72 sourceBody856_75

def sourceBody856_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_76

def sourceBody856_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_71 sourceBody856_77

def sourceBody856_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody856_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1566720#64)

def sourceBody856_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_80 sourceBody856_24

def sourceBody856_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_81

def sourceBody856_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_79 sourceBody856_82

def sourceBody856_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_83

def sourceBody856_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_78 sourceBody856_84

def sourceBody856_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody856_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 8)) (some 483) ([]) (some (10, sourceBody856_86, 856, 9))

def sourceBody856_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_87 sourceBody856_3

def sourceBody856_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_88 sourceBody856_0

def sourceBody856_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody856_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 408#64]))

def sourceBody856_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody856_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 16

def sourceBody856_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_93 sourceBody856_0

def sourceBody856_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_92 sourceBody856_94

def sourceBody856_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_95 sourceBody856_0

def sourceBody856_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_91 sourceBody856_96

def sourceBody856_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_97

def sourceBody856_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_90 sourceBody856_98

def sourceBody856_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_99

def sourceBody856_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody856_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody856_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_102 sourceBody856_96

def sourceBody856_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_103

def sourceBody856_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_101 sourceBody856_104

def sourceBody856_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_105

def sourceBody856_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_100 sourceBody856_106

def sourceBody856_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody856_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 304#64]))

def sourceBody856_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_109 sourceBody856_96

def sourceBody856_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_110

def sourceBody856_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_108 sourceBody856_111

def sourceBody856_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_112

def sourceBody856_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_107 sourceBody856_113

def sourceBody856_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody856_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody856_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_116 sourceBody856_96

def sourceBody856_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_117

def sourceBody856_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_115 sourceBody856_118

def sourceBody856_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_119

def sourceBody856_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_114 sourceBody856_120

def sourceBody856_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody856_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_122 sourceBody856_118

def sourceBody856_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_123

def sourceBody856_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_121 sourceBody856_124

def sourceBody856_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody856_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 30000000#64)

def sourceBody856_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_127 sourceBody856_96

def sourceBody856_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_128

def sourceBody856_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_126 sourceBody856_129

def sourceBody856_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_130

def sourceBody856_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_125 sourceBody856_131

def sourceBody856_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody856_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1566720#64)

def sourceBody856_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_134 sourceBody856_96

def sourceBody856_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_135

def sourceBody856_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_133 sourceBody856_136

def sourceBody856_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_137

def sourceBody856_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_132 sourceBody856_138

def sourceBody856_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody856_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody856_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_141 sourceBody856_96

def sourceBody856_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_142

def sourceBody856_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_140 sourceBody856_143

def sourceBody856_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_144

def sourceBody856_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_139 sourceBody856_145

def sourceBody856_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody856_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody856_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_148 sourceBody856_96

def sourceBody856_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_149

def sourceBody856_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_147 sourceBody856_150

def sourceBody856_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_151

def sourceBody856_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_146 sourceBody856_152

def sourceBody856_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 104#64])

def sourceBody856_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_154 sourceBody856_118

def sourceBody856_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_155

def sourceBody856_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_153 sourceBody856_156

def sourceBody856_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 112#64])

def sourceBody856_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody856_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_159 sourceBody856_96

def sourceBody856_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_160

def sourceBody856_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_158 sourceBody856_161

def sourceBody856_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_162

def sourceBody856_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_157 sourceBody856_163

def sourceBody856_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 120#64])

def sourceBody856_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody856_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_166 sourceBody856_96

def sourceBody856_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_167

def sourceBody856_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_165 sourceBody856_168

def sourceBody856_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_169

def sourceBody856_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_164 sourceBody856_170

def sourceBody856_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody856_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody856_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody856_175 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 10)) (some 182) ([24, 16]) (some (24, sourceBody856_174, 856, 11))

def sourceBody856_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_175 sourceBody856_3

def sourceBody856_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_176 sourceBody856_0

def sourceBody856_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_173 sourceBody856_177

def sourceBody856_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_172 sourceBody856_178

def sourceBody856_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 152#64])

def sourceBody856_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody856_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody856_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 30

def sourceBody856_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_183 sourceBody856_0

def sourceBody856_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_182 sourceBody856_184

def sourceBody856_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_185 sourceBody856_0

def sourceBody856_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_181 sourceBody856_186

def sourceBody856_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_187

def sourceBody856_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_180 sourceBody856_188

def sourceBody856_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_189

def sourceBody856_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 52#64)

def sourceBody856_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody856_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody856_194 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 12)) (some 182) ([16, 30]) (some (16, sourceBody856_193, 856, 13))

def sourceBody856_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_194 sourceBody856_3

def sourceBody856_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_195 sourceBody856_0

def sourceBody856_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_192 sourceBody856_196

def sourceBody856_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_191 sourceBody856_197

def sourceBody856_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody856_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody856_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 14

def sourceBody856_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_201 sourceBody856_0

def sourceBody856_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_53 sourceBody856_202

def sourceBody856_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_203 sourceBody856_0

def sourceBody856_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_200 sourceBody856_204

def sourceBody856_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_205

def sourceBody856_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_199 sourceBody856_206

def sourceBody856_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_207

def sourceBody856_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 32)

def sourceBody856_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody856_211 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody856_0, 856, 14)) (some 621) ([30]) (some (30, sourceBody856_210, 856, 15))

def sourceBody856_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_211 sourceBody856_3

def sourceBody856_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_212 sourceBody856_0

def sourceBody856_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_209 sourceBody856_213

def sourceBody856_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody856_216 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 16)) (some 451) ([]) (some (14, sourceBody856_215, 856, 17))

def sourceBody856_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_216 sourceBody856_3

def sourceBody856_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_217 sourceBody856_0

def sourceBody856_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_218

def sourceBody856_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_219

def sourceBody856_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 80#64]))

def sourceBody856_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody856_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody856_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody856_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody856_226 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 20) sourceBody856_224 sourceBody856_225

def sourceBody856_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_226 sourceBody856_3

def sourceBody856_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody856_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody856_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 14)

def sourceBody856_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody856_232 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 34) sourceBody856_231 sourceBody856_223

def sourceBody856_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_232 sourceBody856_3

def sourceBody856_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody856_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody856_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody856_237 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 18)) (some 68) ([20]) (some (20, sourceBody856_236, 856, 19))

def sourceBody856_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_237 sourceBody856_3

def sourceBody856_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_238 sourceBody856_0

def sourceBody856_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_235 sourceBody856_239

def sourceBody856_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody856_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody856_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody856_244 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 20)) (some 77) ([34, 8, 22]) (some (34, sourceBody856_243, 856, 21))

def sourceBody856_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_244 sourceBody856_3

def sourceBody856_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_245 sourceBody856_0

def sourceBody856_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_242 sourceBody856_246

def sourceBody856_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_241 sourceBody856_247

def sourceBody856_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_228 sourceBody856_248

def sourceBody856_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_249

def sourceBody856_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_250

def sourceBody856_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody856_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 34)

def sourceBody856_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 8

def sourceBody856_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_254 sourceBody856_0

def sourceBody856_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_253 sourceBody856_255

def sourceBody856_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_256 sourceBody856_0

def sourceBody856_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_228 sourceBody856_257

def sourceBody856_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_258

def sourceBody856_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_252 sourceBody856_259

def sourceBody856_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_260

def sourceBody856_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_251 sourceBody856_261

def sourceBody856_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_240 sourceBody856_262

def sourceBody856_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_263

def sourceBody856_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_264

def sourceBody856_266 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody856_265 sourceBody856_0

def sourceBody856_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_266 sourceBody856_3

def sourceBody856_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_267 sourceBody856_0

def sourceBody856_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_234 sourceBody856_268

def sourceBody856_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_233 sourceBody856_269

def sourceBody856_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_230 sourceBody856_270

def sourceBody856_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_223 sourceBody856_271

def sourceBody856_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody856_274 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 22)) (some 76) ([20]) (some (20, sourceBody856_236, 856, 23))

def sourceBody856_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_274 sourceBody856_3

def sourceBody856_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_275 sourceBody856_0

def sourceBody856_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_273 sourceBody856_276

def sourceBody856_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_277

def sourceBody856_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_278

def sourceBody856_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_272 sourceBody856_279

def sourceBody856_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody856_282 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody856_0, 856, 24)) (some 73) ([20]) (some (20, sourceBody856_236, 856, 25))

def sourceBody856_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_282 sourceBody856_3

def sourceBody856_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_283 sourceBody856_0

def sourceBody856_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_281 sourceBody856_284

def sourceBody856_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_285

def sourceBody856_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_286

def sourceBody856_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_280 sourceBody856_287

def sourceBody856_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_229 sourceBody856_288

def sourceBody856_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_289

def sourceBody856_291 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.imm 0#64) sourceBody856_290 sourceBody856_0

def sourceBody856_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_291 sourceBody856_3

def sourceBody856_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_292 sourceBody856_0

def sourceBody856_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_228 sourceBody856_293

def sourceBody856_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_227 sourceBody856_294

def sourceBody856_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_223 sourceBody856_295

def sourceBody856_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_222 sourceBody856_296

def sourceBody856_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody856_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_298 sourceBody856_0

def sourceBody856_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_49 sourceBody856_299

def sourceBody856_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_297 sourceBody856_300

def sourceBody856_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_221 sourceBody856_301

def sourceBody856_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_302

def sourceBody856_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_220 sourceBody856_303

def sourceBody856_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_214 sourceBody856_304

def sourceBody856_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_305

def sourceBody856_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_306

def sourceBody856_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_208 sourceBody856_307

def sourceBody856_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_198 sourceBody856_308

def sourceBody856_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_309

def sourceBody856_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_310

def sourceBody856_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_190 sourceBody856_311

def sourceBody856_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_179 sourceBody856_312

def sourceBody856_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_313

def sourceBody856_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_314

def sourceBody856_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_171 sourceBody856_315

def sourceBody856_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_89 sourceBody856_316

def sourceBody856_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_317

def sourceBody856_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_318

def sourceBody856_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_85 sourceBody856_319

def sourceBody856_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_17 sourceBody856_320

def sourceBody856_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_321

def sourceBody856_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_322

def sourceBody856_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_13 sourceBody856_323

def sourceBody856_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_324

def sourceBody856_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_325

def sourceBody856_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_326

def sourceBody856_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_0 sourceBody856_327

def sourceBody856_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody856_7 sourceBody856_328

def source856 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (856, 4, sourceBody856_329)
end InitECandidate.Proofs.WordStages
