import InitECandidate.Proofs.WordStages.Source287
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody303_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody303_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody303_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody303_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody303_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody303_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody303_0, 303, 2)) (some 284) ([6, 10, 8]) (some (6, sourceBody303_4, 303, 3))

def sourceBody303_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody303_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_5 sourceBody303_6

def sourceBody303_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_7 sourceBody303_0

def sourceBody303_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_3 sourceBody303_8

def sourceBody303_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_2 sourceBody303_9

def sourceBody303_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_1 sourceBody303_10

def sourceBody303_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_0 sourceBody303_11

def sourceBody303_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_0 sourceBody303_12

def sourceBody303_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody303_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody303_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody303_17 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 302) ([0, 12, 6, 10]) (none)

def sourceBody303_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_17 sourceBody303_0

def sourceBody303_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_16 sourceBody303_18

def sourceBody303_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_15 sourceBody303_19

def sourceBody303_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_14 sourceBody303_20

def sourceBody303_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody303_13 sourceBody303_21

def source303 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (303, 3, sourceBody303_22)
end InitECandidate.Proofs.WordStages
