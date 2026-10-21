import InitECandidate.Proofs.WordStages.Source473
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody489_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody489_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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

def sourceBody489_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody489_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody489_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody489_0, 489, 2)) (some 187) ([8, 4]) (some (8, sourceBody489_3, 489, 3))

def sourceBody489_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody489_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_4 sourceBody489_5

def sourceBody489_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_6 sourceBody489_0

def sourceBody489_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_2 sourceBody489_7

def sourceBody489_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_1 sourceBody489_8

def sourceBody489_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody489_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody489_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_11 sourceBody489_0

def sourceBody489_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_10 sourceBody489_12

def sourceBody489_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_9 sourceBody489_13

def sourceBody489_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_0 sourceBody489_14

def sourceBody489_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody489_0 sourceBody489_15

def source489 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (489, 2, sourceBody489_16)
end InitECandidate.Proofs.WordStages
