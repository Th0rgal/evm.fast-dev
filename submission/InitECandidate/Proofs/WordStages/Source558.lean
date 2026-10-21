import InitECandidate.Proofs.WordStages.Source542
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody558_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody558_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody558_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody558_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody558_0, 558, 2)) (some 466) ([4]) (some (4, sourceBody558_2, 558, 3))

def sourceBody558_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody558_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_3 sourceBody558_4

def sourceBody558_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_5 sourceBody558_0

def sourceBody558_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_1 sourceBody558_6

def sourceBody558_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_0 sourceBody558_7

def sourceBody558_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_0 sourceBody558_8

def sourceBody558_10 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody558_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody558_0, 558, 4)) (some 473) ([4]) (some (4, sourceBody558_2, 558, 5))

def sourceBody558_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_11 sourceBody558_4

def sourceBody558_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_12 sourceBody558_0

def sourceBody558_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_10 sourceBody558_13

def sourceBody558_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_0 sourceBody558_14

def sourceBody558_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_0 sourceBody558_15

def sourceBody558_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_9 sourceBody558_16

def sourceBody558_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody558_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody558_0, 558, 6)) (some 486) ([4]) (some (4, sourceBody558_2, 558, 7))

def sourceBody558_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_19 sourceBody558_4

def sourceBody558_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_20 sourceBody558_0

def sourceBody558_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_18 sourceBody558_21

def sourceBody558_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_0 sourceBody558_22

def sourceBody558_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_0 sourceBody558_23

def sourceBody558_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_17 sourceBody558_24

def sourceBody558_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody558_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody558_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_27 sourceBody558_0

def sourceBody558_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_26 sourceBody558_28

def sourceBody558_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody558_25 sourceBody558_29

def source558 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (558, 1, sourceBody558_30)
end InitECandidate.Proofs.WordStages
