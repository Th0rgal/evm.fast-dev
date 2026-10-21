import InitECandidate.Proofs.WordStages.Source543
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody559_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody559_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody559_2 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody559_3 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody559_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody559_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody559_0, 559, 2)) (some 556) ([8, 2, 6]) (some (8, sourceBody559_4, 559, 3))

def sourceBody559_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody559_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_5 sourceBody559_6

def sourceBody559_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_7 sourceBody559_0

def sourceBody559_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_3 sourceBody559_8

def sourceBody559_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_2 sourceBody559_9

def sourceBody559_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_1 sourceBody559_10

def sourceBody559_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_0 sourceBody559_11

def sourceBody559_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_0 sourceBody559_12

def sourceBody559_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody559_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody559_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_15 sourceBody559_0

def sourceBody559_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_14 sourceBody559_16

def sourceBody559_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody559_13 sourceBody559_17

def source559 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (559, 1, sourceBody559_18)
end InitECandidate.Proofs.WordStages
