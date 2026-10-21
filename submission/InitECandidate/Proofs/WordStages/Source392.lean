import InitECandidate.Proofs.WordStages.Source376
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody392_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody392_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 176#64]),
        Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody392_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody392_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody392_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody392_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody392_0, 392, 2)) (some 192) ([10, 4, 8]) (some (10, sourceBody392_4, 392, 3))

def sourceBody392_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody392_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_5 sourceBody392_6

def sourceBody392_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_7 sourceBody392_0

def sourceBody392_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_3 sourceBody392_8

def sourceBody392_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_2 sourceBody392_9

def sourceBody392_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_1 sourceBody392_10

def sourceBody392_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_0 sourceBody392_11

def sourceBody392_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_0 sourceBody392_12

def sourceBody392_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody392_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody392_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_15 sourceBody392_0

def sourceBody392_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_14 sourceBody392_16

def sourceBody392_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody392_13 sourceBody392_17

def source392 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (392, 2, sourceBody392_18)
end InitECandidate.Proofs.WordStages
