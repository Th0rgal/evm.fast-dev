import InitECandidate.Proofs.WordStages.Source405
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody421_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody421_1 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody421_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody421_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody421_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody421_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody421_0, 421, 2)) (some 192) ([10, 4, 8]) (some (10, sourceBody421_4, 421, 3))

def sourceBody421_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody421_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_5 sourceBody421_6

def sourceBody421_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_7 sourceBody421_0

def sourceBody421_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_3 sourceBody421_8

def sourceBody421_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_2 sourceBody421_9

def sourceBody421_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_1 sourceBody421_10

def sourceBody421_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_0 sourceBody421_11

def sourceBody421_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_0 sourceBody421_12

def sourceBody421_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody421_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody421_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_15 sourceBody421_0

def sourceBody421_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_14 sourceBody421_16

def sourceBody421_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody421_13 sourceBody421_17

def source421 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (421, 2, sourceBody421_18)
end InitECandidate.Proofs.WordStages
