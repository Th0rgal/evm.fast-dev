import InitECandidate.Proofs.WordStages.Source507
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody523_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody523_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody523_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody523_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody523_0, 523, 2)) (some 466) ([4]) (some (4, sourceBody523_2, 523, 3))

def sourceBody523_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody523_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_3 sourceBody523_4

def sourceBody523_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_5 sourceBody523_0

def sourceBody523_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_1 sourceBody523_6

def sourceBody523_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_0 sourceBody523_7

def sourceBody523_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_0 sourceBody523_8

def sourceBody523_10 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody523_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody523_0, 523, 4)) (some 473) ([4]) (some (4, sourceBody523_2, 523, 5))

def sourceBody523_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_11 sourceBody523_4

def sourceBody523_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_12 sourceBody523_0

def sourceBody523_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_10 sourceBody523_13

def sourceBody523_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_0 sourceBody523_14

def sourceBody523_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_0 sourceBody523_15

def sourceBody523_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_9 sourceBody523_16

def sourceBody523_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody523_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody523_0, 523, 6)) (some 486) ([4]) (some (4, sourceBody523_2, 523, 7))

def sourceBody523_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_19 sourceBody523_4

def sourceBody523_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_20 sourceBody523_0

def sourceBody523_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_18 sourceBody523_21

def sourceBody523_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_0 sourceBody523_22

def sourceBody523_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_0 sourceBody523_23

def sourceBody523_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_17 sourceBody523_24

def sourceBody523_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody523_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody523_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_27 sourceBody523_0

def sourceBody523_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_26 sourceBody523_28

def sourceBody523_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody523_25 sourceBody523_29

def source523 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (523, 1, sourceBody523_30)
end InitECandidate.Proofs.WordStages
