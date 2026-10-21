import InitECandidate.Proofs.WordStages.Source527
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody543_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody543_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody543_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody543_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody543_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody543_0, 543, 2)) (some 388) ([6, 10]) (some (6, sourceBody543_3, 543, 3))

def sourceBody543_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody543_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_4 sourceBody543_5

def sourceBody543_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_6 sourceBody543_0

def sourceBody543_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_2 sourceBody543_7

def sourceBody543_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_1 sourceBody543_8

def sourceBody543_10 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 176#64]))

def sourceBody543_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody543_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody543_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody543_0, 543, 4)) (some 187) ([10, 8]) (some (10, sourceBody543_12, 543, 5))

def sourceBody543_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_13 sourceBody543_5

def sourceBody543_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_14 sourceBody543_0

def sourceBody543_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_11 sourceBody543_15

def sourceBody543_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_10 sourceBody543_16

def sourceBody543_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody543_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody543_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_19 sourceBody543_0

def sourceBody543_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_18 sourceBody543_20

def sourceBody543_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_17 sourceBody543_21

def sourceBody543_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_0 sourceBody543_22

def sourceBody543_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_0 sourceBody543_23

def sourceBody543_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_9 sourceBody543_24

def sourceBody543_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_0 sourceBody543_25

def sourceBody543_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody543_0 sourceBody543_26

def source543 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (543, 3, sourceBody543_27)
end InitECandidate.Proofs.WordStages
