import InitECandidate.Proofs.WordStages.Source585
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody601_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody601_1 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody601_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody601_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody601_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody601_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody601_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody601_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 6) sourceBody601_5 sourceBody601_6

def sourceBody601_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody601_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_7 sourceBody601_8

def sourceBody601_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody601_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody601_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody601_0, 601, 2)) (some 589) ([]) (some (8, sourceBody601_11, 601, 3))

def sourceBody601_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_12 sourceBody601_8

def sourceBody601_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_13 sourceBody601_0

def sourceBody601_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_14

def sourceBody601_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_15

def sourceBody601_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody601_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody601_0, 601, 4)) (some 469) ([8]) (some (8, sourceBody601_11, 601, 5))

def sourceBody601_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_18 sourceBody601_8

def sourceBody601_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_19 sourceBody601_0

def sourceBody601_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_17 sourceBody601_20

def sourceBody601_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 200#64])

def sourceBody601_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody601_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody601_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 12

def sourceBody601_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_25 sourceBody601_0

def sourceBody601_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_24 sourceBody601_26

def sourceBody601_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_27 sourceBody601_0

def sourceBody601_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_23 sourceBody601_28

def sourceBody601_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_29

def sourceBody601_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_22 sourceBody601_30

def sourceBody601_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_31

def sourceBody601_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody601_34 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody601_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_34 sourceBody601_28

def sourceBody601_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_35

def sourceBody601_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_33 sourceBody601_36

def sourceBody601_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_37

def sourceBody601_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_32 sourceBody601_38

def sourceBody601_40 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody601_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_4 sourceBody601_28

def sourceBody601_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_41

def sourceBody601_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_40 sourceBody601_42

def sourceBody601_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_43

def sourceBody601_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_39 sourceBody601_44

def sourceBody601_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_21 sourceBody601_45

def sourceBody601_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_46

def sourceBody601_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_47

def sourceBody601_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_16 sourceBody601_48

def sourceBody601_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody601_49 sourceBody601_0

def sourceBody601_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_50 sourceBody601_8

def sourceBody601_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_51 sourceBody601_0

def sourceBody601_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_10 sourceBody601_52

def sourceBody601_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_9 sourceBody601_53

def sourceBody601_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_4 sourceBody601_54

def sourceBody601_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_3 sourceBody601_55

def sourceBody601_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody601_0, 601, 6)) (some 590) ([]) (some (8, sourceBody601_11, 601, 7))

def sourceBody601_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_57 sourceBody601_8

def sourceBody601_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_58 sourceBody601_0

def sourceBody601_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_59

def sourceBody601_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_60

def sourceBody601_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_56 sourceBody601_61

def sourceBody601_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody601_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody601_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_64 sourceBody601_0

def sourceBody601_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_63 sourceBody601_65

def sourceBody601_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_62 sourceBody601_66

def sourceBody601_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_2 sourceBody601_67

def sourceBody601_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_68

def sourceBody601_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_1 sourceBody601_69

def sourceBody601_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody601_0 sourceBody601_70

def source601 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (601, 1, sourceBody601_71)
end InitECandidate.Proofs.WordStages
