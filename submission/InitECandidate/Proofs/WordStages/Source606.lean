import InitECandidate.Proofs.WordStages.Source590
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody606_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody606_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody606_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody606_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody606_0, 606, 2)) (some 605) ([18]) (some (18, sourceBody606_2, 606, 3))

def sourceBody606_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody606_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_3 sourceBody606_4

def sourceBody606_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_5 sourceBody606_0

def sourceBody606_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_1 sourceBody606_6

def sourceBody606_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_7

def sourceBody606_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_8

def sourceBody606_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 192#64])

def sourceBody606_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
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
            Flapjack.WordLangExpHOL.const 192#64]),
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])])

def sourceBody606_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody606_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody606_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_13 sourceBody606_0

def sourceBody606_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_12 sourceBody606_14

def sourceBody606_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_15 sourceBody606_0

def sourceBody606_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_11 sourceBody606_16

def sourceBody606_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_17

def sourceBody606_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_10 sourceBody606_18

def sourceBody606_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_19

def sourceBody606_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_9 sourceBody606_20

def sourceBody606_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
        Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody606_23 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 192#64]))

def sourceBody606_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody606_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody606_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody606_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.WordRegImm.reg 16) sourceBody606_25 sourceBody606_26

def sourceBody606_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_27 sourceBody606_4

def sourceBody606_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody606_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
        Flapjack.WordLangExpHOL.const 192#64]))

def sourceBody606_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_30 sourceBody606_0

def sourceBody606_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_31 sourceBody606_0

def sourceBody606_33 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody606_32 sourceBody606_0

def sourceBody606_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_33 sourceBody606_4

def sourceBody606_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_34 sourceBody606_0

def sourceBody606_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_29 sourceBody606_35

def sourceBody606_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_28 sourceBody606_36

def sourceBody606_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_24 sourceBody606_37

def sourceBody606_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_23 sourceBody606_38

def sourceBody606_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody606_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
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
            Flapjack.WordLangExpHOL.const 64#64]),
      Flapjack.WordLangExpHOL.var 8])

def sourceBody606_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody606_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 16

def sourceBody606_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_43 sourceBody606_0

def sourceBody606_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_42 sourceBody606_44

def sourceBody606_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_45 sourceBody606_0

def sourceBody606_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_41 sourceBody606_46

def sourceBody606_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_47

def sourceBody606_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_40 sourceBody606_48

def sourceBody606_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_49

def sourceBody606_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_39 sourceBody606_50

def sourceBody606_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody606_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
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
            Flapjack.WordLangExpHOL.const 72#64]),
      Flapjack.WordLangExpHOL.var 8])

def sourceBody606_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_53 sourceBody606_46

def sourceBody606_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_54

def sourceBody606_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_52 sourceBody606_55

def sourceBody606_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_56

def sourceBody606_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_51 sourceBody606_57

def sourceBody606_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 192#64])

def sourceBody606_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
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
            Flapjack.WordLangExpHOL.const 192#64]),
      Flapjack.WordLangExpHOL.var 8])

def sourceBody606_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_60 sourceBody606_46

def sourceBody606_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_61

def sourceBody606_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_59 sourceBody606_62

def sourceBody606_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_63

def sourceBody606_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_58 sourceBody606_64

def sourceBody606_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody606_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody606_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody606_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody606_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody606_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody606_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody606_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody606_74 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 4 (Flapjack.WordRegImm.reg 14) sourceBody606_72 sourceBody606_73

def sourceBody606_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_74 sourceBody606_4

def sourceBody606_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody606_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody606_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 16,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody606_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody606_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody606_0, 606, 4)) (some 541) ([4, 14]) (some (4, sourceBody606_79, 606, 5))

def sourceBody606_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_80 sourceBody606_4

def sourceBody606_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_81 sourceBody606_0

def sourceBody606_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_78 sourceBody606_82

def sourceBody606_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_77 sourceBody606_83

def sourceBody606_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_84

def sourceBody606_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_85

def sourceBody606_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody606_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody606_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_88 sourceBody606_0

def sourceBody606_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_89 sourceBody606_0

def sourceBody606_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_87 sourceBody606_90

def sourceBody606_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_91

def sourceBody606_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_86 sourceBody606_92

def sourceBody606_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody606_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_93 sourceBody606_94

def sourceBody606_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody606_97 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody606_95 sourceBody606_96

def sourceBody606_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_97 sourceBody606_4

def sourceBody606_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_98 sourceBody606_0

def sourceBody606_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_76 sourceBody606_99

def sourceBody606_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_75 sourceBody606_100

def sourceBody606_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_71 sourceBody606_101

def sourceBody606_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_70 sourceBody606_102

def sourceBody606_104 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody606_103 (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)

def sourceBody606_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_104 sourceBody606_4

def sourceBody606_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_4 sourceBody606_105

def sourceBody606_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 96#64])

def sourceBody606_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
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
            Flapjack.WordLangExpHOL.const 96#64]),
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])])

def sourceBody606_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody606_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 14

def sourceBody606_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_110 sourceBody606_0

def sourceBody606_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_109 sourceBody606_111

def sourceBody606_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_112 sourceBody606_0

def sourceBody606_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_108 sourceBody606_113

def sourceBody606_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_114

def sourceBody606_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_107 sourceBody606_115

def sourceBody606_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_116

def sourceBody606_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_106 sourceBody606_117

def sourceBody606_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
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
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody606_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody606_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody606_0, 606, 6)) (some 428) ([4, 14]) (some (4, sourceBody606_79, 606, 7))

def sourceBody606_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_121 sourceBody606_4

def sourceBody606_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_122 sourceBody606_0

def sourceBody606_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_120 sourceBody606_123

def sourceBody606_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_119 sourceBody606_124

def sourceBody606_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_125

def sourceBody606_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_126

def sourceBody606_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_118 sourceBody606_127

def sourceBody606_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody606_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody606_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_130 sourceBody606_0

def sourceBody606_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_129 sourceBody606_131

def sourceBody606_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_128 sourceBody606_132

def sourceBody606_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_69 sourceBody606_133

def sourceBody606_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_134

def sourceBody606_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_68 sourceBody606_135

def sourceBody606_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_136

def sourceBody606_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_67 sourceBody606_137

def sourceBody606_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_138

def sourceBody606_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_66 sourceBody606_139

def sourceBody606_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_140

def sourceBody606_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_65 sourceBody606_141

def sourceBody606_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_22 sourceBody606_142

def sourceBody606_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_0 sourceBody606_143

def sourceBody606_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody606_21 sourceBody606_144

def source606 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (606, 2, sourceBody606_145)
end InitECandidate.Proofs.WordStages
