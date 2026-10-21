import InitECandidate.Proofs.WordStages.Source548
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody564_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody564_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody564_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody564_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody564_0, 564, 2)) (some 466) ([4]) (some (4, sourceBody564_2, 564, 3))

def sourceBody564_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody564_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_3 sourceBody564_4

def sourceBody564_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_5 sourceBody564_0

def sourceBody564_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_1 sourceBody564_6

def sourceBody564_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_0 sourceBody564_7

def sourceBody564_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_0 sourceBody564_8

def sourceBody564_10 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody564_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody564_0, 564, 4)) (some 473) ([4]) (some (4, sourceBody564_2, 564, 5))

def sourceBody564_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_11 sourceBody564_4

def sourceBody564_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_12 sourceBody564_0

def sourceBody564_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_10 sourceBody564_13

def sourceBody564_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_0 sourceBody564_14

def sourceBody564_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_0 sourceBody564_15

def sourceBody564_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_9 sourceBody564_16

def sourceBody564_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody564_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody564_0, 564, 6)) (some 486) ([4]) (some (4, sourceBody564_2, 564, 7))

def sourceBody564_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_19 sourceBody564_4

def sourceBody564_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_20 sourceBody564_0

def sourceBody564_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_18 sourceBody564_21

def sourceBody564_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_0 sourceBody564_22

def sourceBody564_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_0 sourceBody564_23

def sourceBody564_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_17 sourceBody564_24

def sourceBody564_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody564_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody564_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_27 sourceBody564_0

def sourceBody564_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_26 sourceBody564_28

def sourceBody564_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody564_25 sourceBody564_29

def source564 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (564, 1, sourceBody564_30)
end InitECandidate.Proofs.WordStages
