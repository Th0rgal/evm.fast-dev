import InitECandidate.Proofs.WordStages.Source508
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody524_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody524_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody524_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody524_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody524_0, 524, 2)) (some 466) ([4]) (some (4, sourceBody524_2, 524, 3))

def sourceBody524_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody524_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_3 sourceBody524_4

def sourceBody524_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_5 sourceBody524_0

def sourceBody524_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_1 sourceBody524_6

def sourceBody524_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_0 sourceBody524_7

def sourceBody524_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_0 sourceBody524_8

def sourceBody524_10 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody524_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody524_0, 524, 4)) (some 473) ([4]) (some (4, sourceBody524_2, 524, 5))

def sourceBody524_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_11 sourceBody524_4

def sourceBody524_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_12 sourceBody524_0

def sourceBody524_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_10 sourceBody524_13

def sourceBody524_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_0 sourceBody524_14

def sourceBody524_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_0 sourceBody524_15

def sourceBody524_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_9 sourceBody524_16

def sourceBody524_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody524_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody524_0, 524, 6)) (some 486) ([4]) (some (4, sourceBody524_2, 524, 7))

def sourceBody524_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_19 sourceBody524_4

def sourceBody524_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_20 sourceBody524_0

def sourceBody524_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_18 sourceBody524_21

def sourceBody524_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_0 sourceBody524_22

def sourceBody524_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_0 sourceBody524_23

def sourceBody524_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_17 sourceBody524_24

def sourceBody524_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody524_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def sourceBody524_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_27 sourceBody524_0

def sourceBody524_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_26 sourceBody524_28

def sourceBody524_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody524_25 sourceBody524_29

def source524 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (524, 1, sourceBody524_30)
end InitECandidate.Proofs.WordStages
