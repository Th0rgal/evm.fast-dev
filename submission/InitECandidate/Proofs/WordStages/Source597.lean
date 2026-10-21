import InitECandidate.Proofs.WordStages.Source581
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody597_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody597_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 288#64]))

def sourceBody597_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody597_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody597_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody597_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody597_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody597_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody597_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody597_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody597_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 80#64]))

def sourceBody597_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody597_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody597_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody597_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody597_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody597_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 42) sourceBody597_14 sourceBody597_15

def sourceBody597_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody597_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_16 sourceBody597_17

def sourceBody597_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 22)

def sourceBody597_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody597_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody597_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody597_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody597_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody597_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 42 (Flapjack.WordRegImm.reg 2) sourceBody597_23 sourceBody597_24

def sourceBody597_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_25 sourceBody597_17

def sourceBody597_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody597_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 18)

def sourceBody597_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 34)

def sourceBody597_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody597_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody597_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_31 sourceBody597_0

def sourceBody597_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_32 sourceBody597_0

def sourceBody597_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 32)

def sourceBody597_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody597_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 3)) (some 387) ([24]) (some (24, sourceBody597_35, 597, 4))

def sourceBody597_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_36 sourceBody597_17

def sourceBody597_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_37 sourceBody597_0

def sourceBody597_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_34 sourceBody597_38

def sourceBody597_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_39

def sourceBody597_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_40

def sourceBody597_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 5)) (some 470) ([]) (some (24, sourceBody597_35, 597, 6))

def sourceBody597_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_42 sourceBody597_17

def sourceBody597_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_43 sourceBody597_0

def sourceBody597_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_44

def sourceBody597_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_45

def sourceBody597_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_41 sourceBody597_46

def sourceBody597_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody597_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 7)) (some 600) ([24]) (some (24, sourceBody597_35, 597, 8))

def sourceBody597_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_49 sourceBody597_17

def sourceBody597_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_50 sourceBody597_0

def sourceBody597_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_48 sourceBody597_51

def sourceBody597_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_52

def sourceBody597_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_53

def sourceBody597_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_47 sourceBody597_54

def sourceBody597_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody597_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody597_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody597_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 2) 14

def sourceBody597_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_59 sourceBody597_0

def sourceBody597_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_58 sourceBody597_60

def sourceBody597_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_61 sourceBody597_0

def sourceBody597_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_57 sourceBody597_62

def sourceBody597_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_63

def sourceBody597_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_56 sourceBody597_64

def sourceBody597_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_65

def sourceBody597_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_55 sourceBody597_66

def sourceBody597_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody597_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody597_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_69 sourceBody597_62

def sourceBody597_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_70

def sourceBody597_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_68 sourceBody597_71

def sourceBody597_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_72

def sourceBody597_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_67 sourceBody597_73

def sourceBody597_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_33 sourceBody597_74

def sourceBody597_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_17 sourceBody597_75

def sourceBody597_77 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 8#64) sourceBody597_30 sourceBody597_76

def sourceBody597_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_77 sourceBody597_17

def sourceBody597_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 2)) (some 603) ([2, 24]) (some (2, sourceBody597_78, 597, 9))

def sourceBody597_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_79 sourceBody597_17

def sourceBody597_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_80 sourceBody597_0

def sourceBody597_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_29 sourceBody597_81

def sourceBody597_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_28 sourceBody597_82

def sourceBody597_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_83

def sourceBody597_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_84

def sourceBody597_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_85

def sourceBody597_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_86

def sourceBody597_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 32)

def sourceBody597_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody597_90 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 10)) (some 387) ([42]) (some (42, sourceBody597_89, 597, 11))

def sourceBody597_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_90 sourceBody597_17

def sourceBody597_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_91 sourceBody597_0

def sourceBody597_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_88 sourceBody597_92

def sourceBody597_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_93

def sourceBody597_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_94

def sourceBody597_96 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody597_87 sourceBody597_95

def sourceBody597_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_96 sourceBody597_17

def sourceBody597_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_97 sourceBody597_0

def sourceBody597_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_27 sourceBody597_98

def sourceBody597_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_26 sourceBody597_99

def sourceBody597_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_22 sourceBody597_100

def sourceBody597_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_21 sourceBody597_101

def sourceBody597_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_20 sourceBody597_102

def sourceBody597_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_103

def sourceBody597_105 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody597_104 sourceBody597_0

def sourceBody597_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_105 sourceBody597_17

def sourceBody597_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_106 sourceBody597_0

def sourceBody597_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_19 sourceBody597_107

def sourceBody597_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_18 sourceBody597_108

def sourceBody597_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_13 sourceBody597_109

def sourceBody597_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_12 sourceBody597_110

def sourceBody597_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 256#64])

def sourceBody597_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody597_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 22)

def sourceBody597_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 42

def sourceBody597_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_115 sourceBody597_0

def sourceBody597_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_114 sourceBody597_116

def sourceBody597_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_117 sourceBody597_0

def sourceBody597_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_113 sourceBody597_118

def sourceBody597_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_119

def sourceBody597_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_112 sourceBody597_120

def sourceBody597_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_121

def sourceBody597_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_111 sourceBody597_122

def sourceBody597_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 288#64])

def sourceBody597_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody597_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_125 sourceBody597_118

def sourceBody597_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_126

def sourceBody597_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_124 sourceBody597_127

def sourceBody597_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_128

def sourceBody597_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_123 sourceBody597_129

def sourceBody597_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody597_132 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.reg 2) sourceBody597_23 sourceBody597_24

def sourceBody597_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_132 sourceBody597_17

def sourceBody597_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 34)

def sourceBody597_135 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 12)) (some 607) ([42]) (some (42, sourceBody597_89, 597, 13))

def sourceBody597_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_135 sourceBody597_17

def sourceBody597_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_136 sourceBody597_0

def sourceBody597_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_134 sourceBody597_137

def sourceBody597_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_138

def sourceBody597_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_139

def sourceBody597_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 14)) (some 605) ([42]) (some (42, sourceBody597_89, 597, 15))

def sourceBody597_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_141 sourceBody597_17

def sourceBody597_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_142 sourceBody597_0

def sourceBody597_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_134 sourceBody597_143

def sourceBody597_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_144

def sourceBody597_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_145

def sourceBody597_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_140 sourceBody597_146

def sourceBody597_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody597_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 183600#64)

def sourceBody597_150 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 16)) (some 468) ([42]) (some (42, sourceBody597_89, 597, 17))

def sourceBody597_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_150 sourceBody597_17

def sourceBody597_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_151 sourceBody597_0

def sourceBody597_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_149 sourceBody597_152

def sourceBody597_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_153

def sourceBody597_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_154

def sourceBody597_156 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody597_155 sourceBody597_0

def sourceBody597_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_156 sourceBody597_17

def sourceBody597_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_157 sourceBody597_0

def sourceBody597_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_27 sourceBody597_158

def sourceBody597_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_133 sourceBody597_159

def sourceBody597_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_22 sourceBody597_160

def sourceBody597_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_148 sourceBody597_161

def sourceBody597_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_147 sourceBody597_162

def sourceBody597_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody597_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody597_166 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 18)) (some 609) ([42, 2]) (some (42, sourceBody597_89, 597, 19))

def sourceBody597_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_166 sourceBody597_17

def sourceBody597_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_167 sourceBody597_0

def sourceBody597_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_165 sourceBody597_168

def sourceBody597_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_164 sourceBody597_169

def sourceBody597_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_170

def sourceBody597_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_171

def sourceBody597_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_163 sourceBody597_172

def sourceBody597_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody597_175 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 20)) (some 472) ([42, 2, 24, 14]) (some (42, sourceBody597_89, 597, 21))

def sourceBody597_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_175 sourceBody597_17

def sourceBody597_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_176 sourceBody597_0

def sourceBody597_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_174 sourceBody597_177

def sourceBody597_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_69 sourceBody597_178

def sourceBody597_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_22 sourceBody597_179

def sourceBody597_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_24 sourceBody597_180

def sourceBody597_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_181

def sourceBody597_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_182

def sourceBody597_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_173 sourceBody597_183

def sourceBody597_185 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 22)) (some 606) ([42]) (some (42, sourceBody597_89, 597, 23))

def sourceBody597_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_185 sourceBody597_17

def sourceBody597_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_186 sourceBody597_0

def sourceBody597_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_134 sourceBody597_187

def sourceBody597_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_188

def sourceBody597_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_189

def sourceBody597_191 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 24)) (some 609) ([42, 2]) (some (42, sourceBody597_89, 597, 25))

def sourceBody597_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_191 sourceBody597_17

def sourceBody597_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_192 sourceBody597_0

def sourceBody597_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_22 sourceBody597_193

def sourceBody597_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_88 sourceBody597_194

def sourceBody597_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_195

def sourceBody597_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_196

def sourceBody597_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_190 sourceBody597_197

def sourceBody597_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody597_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody597_201 : WordLangProgHOL (BitVec 64) :=
.call (some (([22, 42, 2, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 26)) (some 463) ([14]) (some (14, sourceBody597_200, 597, 27))

def sourceBody597_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_201 sourceBody597_17

def sourceBody597_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_202 sourceBody597_0

def sourceBody597_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_199 sourceBody597_203

def sourceBody597_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody597_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 42)

def sourceBody597_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 2)

def sourceBody597_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody597_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody597_210 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 28)) (some 472) ([36, 8, 30, 20]) (some (36, sourceBody597_209, 597, 29))

def sourceBody597_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_210 sourceBody597_17

def sourceBody597_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_211 sourceBody597_0

def sourceBody597_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_208 sourceBody597_212

def sourceBody597_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_207 sourceBody597_213

def sourceBody597_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_206 sourceBody597_214

def sourceBody597_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_205 sourceBody597_215

def sourceBody597_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_216

def sourceBody597_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_217

def sourceBody597_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_204 sourceBody597_218

def sourceBody597_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_219

def sourceBody597_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_220

def sourceBody597_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_221

def sourceBody597_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_222

def sourceBody597_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_223

def sourceBody597_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_224

def sourceBody597_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_225

def sourceBody597_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_226

def sourceBody597_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_198 sourceBody597_227

def sourceBody597_229 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody597_184 sourceBody597_228

def sourceBody597_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_229 sourceBody597_17

def sourceBody597_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_230 sourceBody597_0

def sourceBody597_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_27 sourceBody597_231

def sourceBody597_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_133 sourceBody597_232

def sourceBody597_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_22 sourceBody597_233

def sourceBody597_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_21 sourceBody597_234

def sourceBody597_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_131 sourceBody597_235

def sourceBody597_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_236

def sourceBody597_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody597_239 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 42) sourceBody597_14 sourceBody597_15

def sourceBody597_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_239 sourceBody597_17

def sourceBody597_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 34)

def sourceBody597_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody597_243 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 30)) (some 607) ([22]) (some (22, sourceBody597_242, 597, 31))

def sourceBody597_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_243 sourceBody597_17

def sourceBody597_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_244 sourceBody597_0

def sourceBody597_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_241 sourceBody597_245

def sourceBody597_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_246

def sourceBody597_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_247

def sourceBody597_249 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 32)) (some 605) ([22]) (some (22, sourceBody597_242, 597, 33))

def sourceBody597_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_249 sourceBody597_17

def sourceBody597_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_250 sourceBody597_0

def sourceBody597_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_241 sourceBody597_251

def sourceBody597_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_252

def sourceBody597_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_253

def sourceBody597_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_248 sourceBody597_254

def sourceBody597_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 40)

def sourceBody597_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 183600#64)

def sourceBody597_258 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 34)) (some 468) ([22]) (some (22, sourceBody597_242, 597, 35))

def sourceBody597_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_258 sourceBody597_17

def sourceBody597_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_259 sourceBody597_0

def sourceBody597_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_257 sourceBody597_260

def sourceBody597_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_261

def sourceBody597_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_262

def sourceBody597_264 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody597_263 sourceBody597_0

def sourceBody597_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_264 sourceBody597_17

def sourceBody597_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_265 sourceBody597_0

def sourceBody597_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_19 sourceBody597_266

def sourceBody597_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_240 sourceBody597_267

def sourceBody597_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_24 sourceBody597_268

def sourceBody597_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_256 sourceBody597_269

def sourceBody597_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_255 sourceBody597_270

def sourceBody597_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody597_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody597_274 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 36)) (some 609) ([22, 42]) (some (22, sourceBody597_242, 597, 37))

def sourceBody597_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_274 sourceBody597_17

def sourceBody597_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_275 sourceBody597_0

def sourceBody597_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_273 sourceBody597_276

def sourceBody597_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_272 sourceBody597_277

def sourceBody597_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_278

def sourceBody597_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_279

def sourceBody597_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_271 sourceBody597_280

def sourceBody597_282 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 38)) (some 472) ([22, 42, 2, 24]) (some (22, sourceBody597_242, 597, 39))

def sourceBody597_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_282 sourceBody597_17

def sourceBody597_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_283 sourceBody597_0

def sourceBody597_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_69 sourceBody597_284

def sourceBody597_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_22 sourceBody597_285

def sourceBody597_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_24 sourceBody597_286

def sourceBody597_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_15 sourceBody597_287

def sourceBody597_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_288

def sourceBody597_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_289

def sourceBody597_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_281 sourceBody597_290

def sourceBody597_292 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 40)) (some 606) ([22]) (some (22, sourceBody597_242, 597, 41))

def sourceBody597_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_292 sourceBody597_17

def sourceBody597_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_293 sourceBody597_0

def sourceBody597_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_241 sourceBody597_294

def sourceBody597_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_295

def sourceBody597_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_296

def sourceBody597_298 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 42)) (some 609) ([22, 42]) (some (22, sourceBody597_242, 597, 43))

def sourceBody597_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_298 sourceBody597_17

def sourceBody597_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_299 sourceBody597_0

def sourceBody597_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_273 sourceBody597_300

def sourceBody597_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_272 sourceBody597_301

def sourceBody597_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_302

def sourceBody597_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_303

def sourceBody597_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_297 sourceBody597_304

def sourceBody597_306 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 44)) (some 472) ([22, 42, 2, 24]) (some (22, sourceBody597_242, 597, 45))

def sourceBody597_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_306 sourceBody597_17

def sourceBody597_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_307 sourceBody597_0

def sourceBody597_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_69 sourceBody597_308

def sourceBody597_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_22 sourceBody597_309

def sourceBody597_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_24 sourceBody597_310

def sourceBody597_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_14 sourceBody597_311

def sourceBody597_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_312

def sourceBody597_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_313

def sourceBody597_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_305 sourceBody597_314

def sourceBody597_316 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody597_291 sourceBody597_315

def sourceBody597_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_316 sourceBody597_17

def sourceBody597_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_317 sourceBody597_0

def sourceBody597_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_19 sourceBody597_318

def sourceBody597_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_240 sourceBody597_319

def sourceBody597_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_24 sourceBody597_320

def sourceBody597_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_238 sourceBody597_321

def sourceBody597_323 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 38)

def sourceBody597_324 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 46)) (some 92) ([22, 42]) (some (22, sourceBody597_242, 597, 47))

def sourceBody597_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_324 sourceBody597_17

def sourceBody597_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_325 sourceBody597_0

def sourceBody597_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_273 sourceBody597_326

def sourceBody597_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_323 sourceBody597_327

def sourceBody597_329 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
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
            Flapjack.WordLangExpHOL.const 24#64]),
      Flapjack.WordLangExpHOL.var 16])

def sourceBody597_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
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
        Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody597_331 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 48)) (some 77) ([42, 2, 24]) (some (42, sourceBody597_89, 597, 49))

def sourceBody597_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_331 sourceBody597_17

def sourceBody597_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_332 sourceBody597_0

def sourceBody597_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_34 sourceBody597_333

def sourceBody597_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_330 sourceBody597_334

def sourceBody597_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_329 sourceBody597_335

def sourceBody597_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_336

def sourceBody597_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_337

def sourceBody597_339 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody597_338 sourceBody597_0

def sourceBody597_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_339 sourceBody597_17

def sourceBody597_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_340 sourceBody597_0

def sourceBody597_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_27 sourceBody597_341

def sourceBody597_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_133 sourceBody597_342

def sourceBody597_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_22 sourceBody597_343

def sourceBody597_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_88 sourceBody597_344

def sourceBody597_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_328 sourceBody597_345

def sourceBody597_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_346

def sourceBody597_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_347

def sourceBody597_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_322 sourceBody597_348

def sourceBody597_350 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody597_237 sourceBody597_349

def sourceBody597_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_350 sourceBody597_17

def sourceBody597_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_351 sourceBody597_0

def sourceBody597_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_19 sourceBody597_352

def sourceBody597_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_18 sourceBody597_353

def sourceBody597_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_13 sourceBody597_354

def sourceBody597_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_12 sourceBody597_355

def sourceBody597_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_130 sourceBody597_356

def sourceBody597_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody597_359 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody597_0, 597, 50)) (some 76) ([22]) (some (22, sourceBody597_242, 597, 51))

def sourceBody597_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_359 sourceBody597_17

def sourceBody597_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_360 sourceBody597_0

def sourceBody597_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_358 sourceBody597_361

def sourceBody597_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_362

def sourceBody597_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_363

def sourceBody597_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_357 sourceBody597_364

def sourceBody597_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody597_367 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody597_0, 597, 52)) (some 73) ([22]) (some (22, sourceBody597_242, 597, 53))

def sourceBody597_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_367 sourceBody597_17

def sourceBody597_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_368 sourceBody597_0

def sourceBody597_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_366 sourceBody597_369

def sourceBody597_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_370

def sourceBody597_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_371

def sourceBody597_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_365 sourceBody597_372

def sourceBody597_374 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody597_0, 597, 54)) (some 486) ([22]) (some (22, sourceBody597_242, 597, 55))

def sourceBody597_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_374 sourceBody597_17

def sourceBody597_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_375 sourceBody597_0

def sourceBody597_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_14 sourceBody597_376

def sourceBody597_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_377

def sourceBody597_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_378

def sourceBody597_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_373 sourceBody597_379

def sourceBody597_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody597_382 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody597_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_382 sourceBody597_0

def sourceBody597_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_381 sourceBody597_383

def sourceBody597_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_380 sourceBody597_384

def sourceBody597_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_11 sourceBody597_385

def sourceBody597_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_386

def sourceBody597_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_10 sourceBody597_387

def sourceBody597_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_388

def sourceBody597_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_9 sourceBody597_389

def sourceBody597_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_390

def sourceBody597_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_8 sourceBody597_391

def sourceBody597_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_392

def sourceBody597_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_7 sourceBody597_393

def sourceBody597_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_394

def sourceBody597_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_6 sourceBody597_395

def sourceBody597_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_396

def sourceBody597_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_5 sourceBody597_397

def sourceBody597_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_398

def sourceBody597_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_4 sourceBody597_399

def sourceBody597_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_400

def sourceBody597_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_3 sourceBody597_401

def sourceBody597_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_402

def sourceBody597_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_2 sourceBody597_403

def sourceBody597_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_404

def sourceBody597_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_1 sourceBody597_405

def sourceBody597_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody597_0 sourceBody597_406

def source597 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (597, 1, sourceBody597_407)
end InitECandidate.Proofs.WordStages
