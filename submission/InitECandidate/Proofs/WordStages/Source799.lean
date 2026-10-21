import InitECandidate.Proofs.WordStages.Source783
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody799_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody799_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody799_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 2)) (some 69) ([]) (some (8, sourceBody799_1, 799, 3))

def sourceBody799_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody799_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_2 sourceBody799_3

def sourceBody799_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_4 sourceBody799_0

def sourceBody799_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody799_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody799_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 4)) (some 68) ([20]) (some (20, sourceBody799_7, 799, 5))

def sourceBody799_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_8 sourceBody799_3

def sourceBody799_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_9 sourceBody799_0

def sourceBody799_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_6 sourceBody799_10

def sourceBody799_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody799_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody799_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 6)) (some 68) ([14]) (some (14, sourceBody799_13, 799, 7))

def sourceBody799_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_14 sourceBody799_3

def sourceBody799_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_15 sourceBody799_0

def sourceBody799_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_12 sourceBody799_16

def sourceBody799_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody799_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody799_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody799_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody799_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody799_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody799_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 8)) (some 725) ([12, 26]) (some (12, sourceBody799_23, 799, 9))

def sourceBody799_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_24 sourceBody799_3

def sourceBody799_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_25 sourceBody799_0

def sourceBody799_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_22 sourceBody799_26

def sourceBody799_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_21 sourceBody799_27

def sourceBody799_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_28

def sourceBody799_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_29

def sourceBody799_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody799_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 10)) (some 736) ([12, 26]) (some (12, sourceBody799_23, 799, 11))

def sourceBody799_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_32 sourceBody799_3

def sourceBody799_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_33 sourceBody799_0

def sourceBody799_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_22 sourceBody799_34

def sourceBody799_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_31 sourceBody799_35

def sourceBody799_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_36

def sourceBody799_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_37

def sourceBody799_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_30 sourceBody799_38

def sourceBody799_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody799_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody799_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody799_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 12)) (some 735) ([12, 26, 10]) (some (12, sourceBody799_23, 799, 13))

def sourceBody799_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_43 sourceBody799_3

def sourceBody799_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_44 sourceBody799_0

def sourceBody799_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_42 sourceBody799_45

def sourceBody799_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_41 sourceBody799_46

def sourceBody799_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_40 sourceBody799_47

def sourceBody799_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_48

def sourceBody799_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_49

def sourceBody799_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_39 sourceBody799_50

def sourceBody799_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody799_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 5600#64])

def sourceBody799_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody799_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody799_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody799_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 14)) (some 798) ([12, 26, 10, 22, 16]) (some (12, sourceBody799_23, 799, 15))

def sourceBody799_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_57 sourceBody799_3

def sourceBody799_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_58 sourceBody799_0

def sourceBody799_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_56 sourceBody799_59

def sourceBody799_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_55 sourceBody799_60

def sourceBody799_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_54 sourceBody799_61

def sourceBody799_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_53 sourceBody799_62

def sourceBody799_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_52 sourceBody799_63

def sourceBody799_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_64

def sourceBody799_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_65

def sourceBody799_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_51 sourceBody799_66

def sourceBody799_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody799_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 5984#64])

def sourceBody799_70 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 16)) (some 798) ([12, 26, 10, 22, 16]) (some (12, sourceBody799_23, 799, 17))

def sourceBody799_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_70 sourceBody799_3

def sourceBody799_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_71 sourceBody799_0

def sourceBody799_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_56 sourceBody799_72

def sourceBody799_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_55 sourceBody799_73

def sourceBody799_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_54 sourceBody799_74

def sourceBody799_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_69 sourceBody799_75

def sourceBody799_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_68 sourceBody799_76

def sourceBody799_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_77

def sourceBody799_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_78

def sourceBody799_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_67 sourceBody799_79

def sourceBody799_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody799_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 6368#64])

def sourceBody799_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 18)) (some 798) ([12, 26, 10, 22, 16]) (some (12, sourceBody799_23, 799, 19))

def sourceBody799_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_83 sourceBody799_3

def sourceBody799_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_84 sourceBody799_0

def sourceBody799_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_56 sourceBody799_85

def sourceBody799_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_55 sourceBody799_86

def sourceBody799_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_54 sourceBody799_87

def sourceBody799_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_82 sourceBody799_88

def sourceBody799_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_81 sourceBody799_89

def sourceBody799_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_90

def sourceBody799_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_91

def sourceBody799_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_80 sourceBody799_92

def sourceBody799_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody799_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 6752#64])

def sourceBody799_96 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 20)) (some 798) ([12, 26, 10, 22, 16]) (some (12, sourceBody799_23, 799, 21))

def sourceBody799_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_96 sourceBody799_3

def sourceBody799_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_97 sourceBody799_0

def sourceBody799_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_56 sourceBody799_98

def sourceBody799_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_55 sourceBody799_99

def sourceBody799_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_54 sourceBody799_100

def sourceBody799_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_95 sourceBody799_101

def sourceBody799_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_94 sourceBody799_102

def sourceBody799_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_103

def sourceBody799_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_104

def sourceBody799_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_93 sourceBody799_105

def sourceBody799_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody799_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody799_109 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 22)) (some 735) ([12, 26, 10]) (some (12, sourceBody799_23, 799, 23))

def sourceBody799_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_109 sourceBody799_3

def sourceBody799_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_110 sourceBody799_0

def sourceBody799_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_108 sourceBody799_111

def sourceBody799_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_107 sourceBody799_112

def sourceBody799_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_81 sourceBody799_113

def sourceBody799_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_114

def sourceBody799_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_115

def sourceBody799_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_106 sourceBody799_116

def sourceBody799_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody799_119 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 24)) (some 735) ([12, 26, 10]) (some (12, sourceBody799_23, 799, 25))

def sourceBody799_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_119 sourceBody799_3

def sourceBody799_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_120 sourceBody799_0

def sourceBody799_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_42 sourceBody799_121

def sourceBody799_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_118 sourceBody799_122

def sourceBody799_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_94 sourceBody799_123

def sourceBody799_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_124

def sourceBody799_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_125

def sourceBody799_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_117 sourceBody799_126

def sourceBody799_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody799_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody799_130 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 26)) (some 735) ([12, 26, 10]) (some (12, sourceBody799_23, 799, 27))

def sourceBody799_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_130 sourceBody799_3

def sourceBody799_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_131 sourceBody799_0

def sourceBody799_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_129 sourceBody799_132

def sourceBody799_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_128 sourceBody799_133

def sourceBody799_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_21 sourceBody799_134

def sourceBody799_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_135

def sourceBody799_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_136

def sourceBody799_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_127 sourceBody799_137

def sourceBody799_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody799_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody799_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 28)) (some 735) ([12, 26, 10]) (some (12, sourceBody799_23, 799, 29))

def sourceBody799_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_141 sourceBody799_3

def sourceBody799_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_142 sourceBody799_0

def sourceBody799_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_140 sourceBody799_143

def sourceBody799_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_139 sourceBody799_144

def sourceBody799_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_31 sourceBody799_145

def sourceBody799_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_146

def sourceBody799_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_147

def sourceBody799_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_138 sourceBody799_148

def sourceBody799_150 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 30)) (some 735) ([12, 26, 10]) (some (12, sourceBody799_23, 799, 31))

def sourceBody799_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_150 sourceBody799_3

def sourceBody799_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_151 sourceBody799_0

def sourceBody799_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_129 sourceBody799_152

def sourceBody799_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_139 sourceBody799_153

def sourceBody799_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_40 sourceBody799_154

def sourceBody799_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_155

def sourceBody799_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_156

def sourceBody799_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_149 sourceBody799_157

def sourceBody799_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody799_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody799_161 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody799_0, 799, 32)) (some 776) ([12, 26]) (some (12, sourceBody799_23, 799, 33))

def sourceBody799_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_161 sourceBody799_3

def sourceBody799_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_162 sourceBody799_0

def sourceBody799_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_160 sourceBody799_163

def sourceBody799_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_159 sourceBody799_164

def sourceBody799_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_165

def sourceBody799_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_166

def sourceBody799_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_158 sourceBody799_167

def sourceBody799_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody799_170 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody799_0, 799, 34)) (some 70) ([12]) (some (12, sourceBody799_23, 799, 35))

def sourceBody799_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_170 sourceBody799_3

def sourceBody799_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_171 sourceBody799_0

def sourceBody799_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_169 sourceBody799_172

def sourceBody799_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_173

def sourceBody799_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_174

def sourceBody799_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_168 sourceBody799_175

def sourceBody799_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody799_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody799_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_178 sourceBody799_0

def sourceBody799_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_177 sourceBody799_179

def sourceBody799_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_176 sourceBody799_180

def sourceBody799_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_20 sourceBody799_181

def sourceBody799_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_182

def sourceBody799_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_19 sourceBody799_183

def sourceBody799_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_184

def sourceBody799_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_18 sourceBody799_185

def sourceBody799_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_186

def sourceBody799_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_17 sourceBody799_187

def sourceBody799_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_188

def sourceBody799_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_189

def sourceBody799_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_11 sourceBody799_190

def sourceBody799_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_191

def sourceBody799_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_192

def sourceBody799_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_5 sourceBody799_193

def sourceBody799_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_194

def sourceBody799_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody799_0 sourceBody799_195

def source799 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (799, 3, sourceBody799_196)
end InitECandidate.Proofs.WordStages
