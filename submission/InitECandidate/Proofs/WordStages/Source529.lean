import InitECandidate.Proofs.WordStages.Source513
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody529_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody529_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody529_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody529_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody529_0, 529, 2)) (some 466) ([4]) (some (4, sourceBody529_2, 529, 3))

def sourceBody529_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody529_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_3 sourceBody529_4

def sourceBody529_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_5 sourceBody529_0

def sourceBody529_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_1 sourceBody529_6

def sourceBody529_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_0 sourceBody529_7

def sourceBody529_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_0 sourceBody529_8

def sourceBody529_10 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody529_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody529_0, 529, 4)) (some 473) ([4]) (some (4, sourceBody529_2, 529, 5))

def sourceBody529_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_11 sourceBody529_4

def sourceBody529_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_12 sourceBody529_0

def sourceBody529_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_10 sourceBody529_13

def sourceBody529_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_0 sourceBody529_14

def sourceBody529_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_0 sourceBody529_15

def sourceBody529_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_9 sourceBody529_16

def sourceBody529_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody529_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody529_0, 529, 6)) (some 486) ([4]) (some (4, sourceBody529_2, 529, 7))

def sourceBody529_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_19 sourceBody529_4

def sourceBody529_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_20 sourceBody529_0

def sourceBody529_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_18 sourceBody529_21

def sourceBody529_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_0 sourceBody529_22

def sourceBody529_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_0 sourceBody529_23

def sourceBody529_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_17 sourceBody529_24

def sourceBody529_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody529_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody529_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_27 sourceBody529_0

def sourceBody529_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_26 sourceBody529_28

def sourceBody529_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody529_25 sourceBody529_29

def source529 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (529, 1, sourceBody529_30)
end InitECandidate.Proofs.WordStages
