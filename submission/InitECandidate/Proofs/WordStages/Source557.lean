import InitECandidate.Proofs.WordStages.Source541
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody557_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody557_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody557_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody557_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody557_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody557_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody557_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody557_0, 557, 2)) (some 556) ([2, 8, 6]) (some (2, sourceBody557_5, 557, 3))

def sourceBody557_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody557_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_6 sourceBody557_7

def sourceBody557_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_8 sourceBody557_0

def sourceBody557_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_4 sourceBody557_9

def sourceBody557_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_3 sourceBody557_10

def sourceBody557_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_2 sourceBody557_11

def sourceBody557_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_0 sourceBody557_12

def sourceBody557_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_0 sourceBody557_13

def sourceBody557_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody557_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody557_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_16 sourceBody557_0

def sourceBody557_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_15 sourceBody557_17

def sourceBody557_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_14 sourceBody557_18

def sourceBody557_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_1 sourceBody557_19

def sourceBody557_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody557_0 sourceBody557_20

def source557 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (557, 1, sourceBody557_21)
end InitECandidate.Proofs.WordStages
