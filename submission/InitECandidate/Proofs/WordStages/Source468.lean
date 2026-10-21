import InitECandidate.Proofs.WordStages.Source452
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody468_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody468_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody468_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody468_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody468_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody468_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody468_0, 468, 2)) (some 92) ([4, 10]) (some (4, sourceBody468_4, 468, 3))

def sourceBody468_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody468_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_5 sourceBody468_6

def sourceBody468_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_7 sourceBody468_0

def sourceBody468_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_3 sourceBody468_8

def sourceBody468_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_2 sourceBody468_9

def sourceBody468_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody468_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
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
      Flapjack.WordLangExpHOL.var 12])

def sourceBody468_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody468_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 8

def sourceBody468_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_14 sourceBody468_0

def sourceBody468_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_13 sourceBody468_15

def sourceBody468_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_16 sourceBody468_0

def sourceBody468_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_12 sourceBody468_17

def sourceBody468_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_18

def sourceBody468_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_11 sourceBody468_19

def sourceBody468_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_20

def sourceBody468_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 192#64])

def sourceBody468_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 12])

def sourceBody468_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_23 sourceBody468_17

def sourceBody468_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_24

def sourceBody468_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_22 sourceBody468_25

def sourceBody468_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_26

def sourceBody468_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_21 sourceBody468_27

def sourceBody468_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody468_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
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
            Flapjack.WordLangExpHOL.const 72#64]),
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 12]])

def sourceBody468_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_30 sourceBody468_17

def sourceBody468_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_31

def sourceBody468_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_29 sourceBody468_32

def sourceBody468_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_33

def sourceBody468_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_28 sourceBody468_34

def sourceBody468_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody468_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody468_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_37 sourceBody468_0

def sourceBody468_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_36 sourceBody468_38

def sourceBody468_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_35 sourceBody468_39

def sourceBody468_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_10 sourceBody468_40

def sourceBody468_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_41

def sourceBody468_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_42

def sourceBody468_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_1 sourceBody468_43

def sourceBody468_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody468_0 sourceBody468_44

def source468 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (468, 2, sourceBody468_45)
end InitECandidate.Proofs.WordStages
