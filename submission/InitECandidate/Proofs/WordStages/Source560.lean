import InitECandidate.Proofs.WordStages.Source544
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody560_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody560_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody560_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody560_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody560_0, 560, 2)) (some 466) ([10]) (some (10, sourceBody560_2, 560, 3))

def sourceBody560_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody560_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_3 sourceBody560_4

def sourceBody560_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_5 sourceBody560_0

def sourceBody560_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_1 sourceBody560_6

def sourceBody560_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_0 sourceBody560_7

def sourceBody560_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_0 sourceBody560_8

def sourceBody560_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
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
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody560_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody560_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody560_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody560_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody560_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody560_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody560_0, 560, 4)) (some 472) ([2, 8, 6, 12]) (some (2, sourceBody560_15, 560, 5))

def sourceBody560_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_16 sourceBody560_4

def sourceBody560_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_17 sourceBody560_0

def sourceBody560_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_14 sourceBody560_18

def sourceBody560_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_13 sourceBody560_19

def sourceBody560_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_12 sourceBody560_20

def sourceBody560_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_11 sourceBody560_21

def sourceBody560_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_0 sourceBody560_22

def sourceBody560_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_0 sourceBody560_23

def sourceBody560_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody560_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody560_0, 560, 6)) (some 486) ([2]) (some (2, sourceBody560_15, 560, 7))

def sourceBody560_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_26 sourceBody560_4

def sourceBody560_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_27 sourceBody560_0

def sourceBody560_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_25 sourceBody560_28

def sourceBody560_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_0 sourceBody560_29

def sourceBody560_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_0 sourceBody560_30

def sourceBody560_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_24 sourceBody560_31

def sourceBody560_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody560_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody560_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_34 sourceBody560_0

def sourceBody560_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_33 sourceBody560_35

def sourceBody560_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_32 sourceBody560_36

def sourceBody560_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_10 sourceBody560_37

def sourceBody560_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_0 sourceBody560_38

def sourceBody560_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody560_9 sourceBody560_39

def source560 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (560, 1, sourceBody560_40)
end InitECandidate.Proofs.WordStages
