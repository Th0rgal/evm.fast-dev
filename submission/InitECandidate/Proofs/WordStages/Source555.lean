import InitECandidate.Proofs.WordStages.Source539
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody555_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody555_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody555_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody555_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody555_0, 555, 2)) (some 466) ([4]) (some (4, sourceBody555_2, 555, 3))

def sourceBody555_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody555_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_3 sourceBody555_4

def sourceBody555_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_5 sourceBody555_0

def sourceBody555_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_1 sourceBody555_6

def sourceBody555_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_0 sourceBody555_7

def sourceBody555_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_0 sourceBody555_8

def sourceBody555_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.load
                (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                  [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                      [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                          (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                          (Flapjack.WordLangExpHOL.const 1#64)],
                    Flapjack.WordLangExpHOL.const 256#64]),
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody555_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody555_0, 555, 4)) (some 473) ([4]) (some (4, sourceBody555_2, 555, 5))

def sourceBody555_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_11 sourceBody555_4

def sourceBody555_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_12 sourceBody555_0

def sourceBody555_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_10 sourceBody555_13

def sourceBody555_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_0 sourceBody555_14

def sourceBody555_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_0 sourceBody555_15

def sourceBody555_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_9 sourceBody555_16

def sourceBody555_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody555_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody555_0, 555, 6)) (some 486) ([4]) (some (4, sourceBody555_2, 555, 7))

def sourceBody555_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_19 sourceBody555_4

def sourceBody555_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_20 sourceBody555_0

def sourceBody555_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_18 sourceBody555_21

def sourceBody555_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_0 sourceBody555_22

def sourceBody555_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_0 sourceBody555_23

def sourceBody555_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_17 sourceBody555_24

def sourceBody555_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody555_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody555_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_27 sourceBody555_0

def sourceBody555_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_26 sourceBody555_28

def sourceBody555_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody555_25 sourceBody555_29

def source555 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (555, 1, sourceBody555_30)
end InitECandidate.Proofs.WordStages
