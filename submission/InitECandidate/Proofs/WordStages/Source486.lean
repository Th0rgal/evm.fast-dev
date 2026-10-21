import InitECandidate.Proofs.WordStages.Source470
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody486_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody486_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody486_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
            Flapjack.WordLangExpHOL.const 0#64]),
      Flapjack.WordLangExpHOL.var 2])

def sourceBody486_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 8)

def sourceBody486_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 4

def sourceBody486_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_4 sourceBody486_0

def sourceBody486_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_3 sourceBody486_5

def sourceBody486_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_6 sourceBody486_0

def sourceBody486_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_2 sourceBody486_7

def sourceBody486_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_0 sourceBody486_8

def sourceBody486_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_1 sourceBody486_9

def sourceBody486_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_0 sourceBody486_10

def sourceBody486_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody486_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody486_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_13 sourceBody486_0

def sourceBody486_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_12 sourceBody486_14

def sourceBody486_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody486_11 sourceBody486_15

def source486 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (486, 2, sourceBody486_16)
end InitECandidate.Proofs.WordStages
