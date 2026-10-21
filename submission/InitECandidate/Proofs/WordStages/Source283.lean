import InitECandidate.Proofs.WordStages.Source267
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody283_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody283_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody283_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody283_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody283_0, 283, 2)) (some 68) ([8]) (some (8, sourceBody283_2, 283, 3))

def sourceBody283_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody283_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_3 sourceBody283_4

def sourceBody283_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_5 sourceBody283_0

def sourceBody283_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_1 sourceBody283_6

def sourceBody283_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody283_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody283_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody283_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody283_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_11 sourceBody283_0

def sourceBody283_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_10 sourceBody283_12

def sourceBody283_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_13 sourceBody283_0

def sourceBody283_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_9 sourceBody283_14

def sourceBody283_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_15

def sourceBody283_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_8 sourceBody283_16

def sourceBody283_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_17

def sourceBody283_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_7 sourceBody283_18

def sourceBody283_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_19

def sourceBody283_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_20

def sourceBody283_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody283_0, 283, 4)) (some 68) ([8]) (some (8, sourceBody283_2, 283, 5))

def sourceBody283_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_22 sourceBody283_4

def sourceBody283_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_23 sourceBody283_0

def sourceBody283_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_1 sourceBody283_24

def sourceBody283_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 136#64])

def sourceBody283_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_26 sourceBody283_16

def sourceBody283_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_27

def sourceBody283_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_25 sourceBody283_28

def sourceBody283_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_29

def sourceBody283_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_30

def sourceBody283_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_21 sourceBody283_31

def sourceBody283_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody283_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody283_0, 283, 6)) (some 68) ([8]) (some (8, sourceBody283_2, 283, 7))

def sourceBody283_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_34 sourceBody283_4

def sourceBody283_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_35 sourceBody283_0

def sourceBody283_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_33 sourceBody283_36

def sourceBody283_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 144#64])

def sourceBody283_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_38 sourceBody283_16

def sourceBody283_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_39

def sourceBody283_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_37 sourceBody283_40

def sourceBody283_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_41

def sourceBody283_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_42

def sourceBody283_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_32 sourceBody283_43

def sourceBody283_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody283_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody283_0, 283, 8)) (some 68) ([8]) (some (8, sourceBody283_2, 283, 9))

def sourceBody283_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_46 sourceBody283_4

def sourceBody283_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_47 sourceBody283_0

def sourceBody283_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_45 sourceBody283_48

def sourceBody283_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 152#64])

def sourceBody283_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_50 sourceBody283_16

def sourceBody283_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_51

def sourceBody283_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_49 sourceBody283_52

def sourceBody283_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_53

def sourceBody283_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_54

def sourceBody283_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_44 sourceBody283_55

def sourceBody283_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody283_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody283_0, 283, 10)) (some 68) ([8]) (some (8, sourceBody283_2, 283, 11))

def sourceBody283_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_58 sourceBody283_4

def sourceBody283_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_59 sourceBody283_0

def sourceBody283_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_57 sourceBody283_60

def sourceBody283_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 160#64])

def sourceBody283_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_62 sourceBody283_16

def sourceBody283_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_63

def sourceBody283_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_61 sourceBody283_64

def sourceBody283_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_65

def sourceBody283_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_66

def sourceBody283_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_56 sourceBody283_67

def sourceBody283_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody283_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody283_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 8 (Flapjack.WordLangAddr.addr 4 0#64))

def sourceBody283_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_71 sourceBody283_0

def sourceBody283_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_70 sourceBody283_72

def sourceBody283_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_69 sourceBody283_73

def sourceBody283_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_68 sourceBody283_74

def sourceBody283_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody283_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody283_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody283_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody283_0, 283, 12)) (some 158) ([8, 2, 6]) (some (8, sourceBody283_2, 283, 13))

def sourceBody283_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_79 sourceBody283_4

def sourceBody283_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_80 sourceBody283_0

def sourceBody283_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_78 sourceBody283_81

def sourceBody283_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_77 sourceBody283_82

def sourceBody283_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_76 sourceBody283_83

def sourceBody283_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_84

def sourceBody283_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_85

def sourceBody283_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_75 sourceBody283_86

def sourceBody283_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody283_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody283_90 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody283_0, 283, 14)) (some 158) ([8, 2, 6]) (some (8, sourceBody283_2, 283, 15))

def sourceBody283_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_90 sourceBody283_4

def sourceBody283_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_91 sourceBody283_0

def sourceBody283_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_89 sourceBody283_92

def sourceBody283_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_88 sourceBody283_93

def sourceBody283_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_76 sourceBody283_94

def sourceBody283_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_95

def sourceBody283_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_0 sourceBody283_96

def sourceBody283_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_87 sourceBody283_97

def sourceBody283_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody283_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody283_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_100 sourceBody283_0

def sourceBody283_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_99 sourceBody283_101

def sourceBody283_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody283_98 sourceBody283_102

def source283 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (283, 1, sourceBody283_103)
end InitECandidate.Proofs.WordStages
