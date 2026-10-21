import InitECandidate.Proofs.WordStages.Source474
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody490_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody490_1 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody490_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody490_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody490_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody490_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody490_0, 490, 2)) (some 192) ([10, 4, 8]) (some (10, sourceBody490_4, 490, 3))

def sourceBody490_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody490_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_5 sourceBody490_6

def sourceBody490_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_7 sourceBody490_0

def sourceBody490_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_3 sourceBody490_8

def sourceBody490_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_2 sourceBody490_9

def sourceBody490_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_1 sourceBody490_10

def sourceBody490_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_0 sourceBody490_11

def sourceBody490_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_0 sourceBody490_12

def sourceBody490_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody490_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody490_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_15 sourceBody490_0

def sourceBody490_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_14 sourceBody490_16

def sourceBody490_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody490_13 sourceBody490_17

def source490 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (490, 2, sourceBody490_18)
end InitECandidate.Proofs.WordStages
