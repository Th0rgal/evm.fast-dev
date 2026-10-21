import InitECandidate.Proofs.WordStages.Source454
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody470_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody470_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody470_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody470_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
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
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 192#64])])

def sourceBody470_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody470_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody470_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_5 sourceBody470_0

def sourceBody470_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_4 sourceBody470_6

def sourceBody470_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_7 sourceBody470_0

def sourceBody470_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_3 sourceBody470_8

def sourceBody470_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_0 sourceBody470_9

def sourceBody470_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_2 sourceBody470_10

def sourceBody470_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_0 sourceBody470_11

def sourceBody470_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody470_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody470_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_14 sourceBody470_8

def sourceBody470_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_0 sourceBody470_15

def sourceBody470_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_13 sourceBody470_16

def sourceBody470_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_0 sourceBody470_17

def sourceBody470_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_12 sourceBody470_18

def sourceBody470_20 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody470_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody470_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_21 sourceBody470_8

def sourceBody470_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_0 sourceBody470_22

def sourceBody470_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_20 sourceBody470_23

def sourceBody470_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_0 sourceBody470_24

def sourceBody470_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_19 sourceBody470_25

def sourceBody470_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody470_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody470_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_28 sourceBody470_0

def sourceBody470_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_27 sourceBody470_29

def sourceBody470_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_26 sourceBody470_30

def sourceBody470_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_1 sourceBody470_31

def sourceBody470_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody470_0 sourceBody470_32

def source470 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (470, 1, sourceBody470_33)
end InitECandidate.Proofs.WordStages
