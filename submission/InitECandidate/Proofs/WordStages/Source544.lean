import InitECandidate.Proofs.WordStages.Source528
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody544_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody544_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody544_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody544_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody544_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody544_0, 544, 2)) (some 388) ([6, 10]) (some (6, sourceBody544_3, 544, 3))

def sourceBody544_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody544_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_4 sourceBody544_5

def sourceBody544_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_6 sourceBody544_0

def sourceBody544_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_2 sourceBody544_7

def sourceBody544_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_1 sourceBody544_8

def sourceBody544_10 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody544_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody544_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody544_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody544_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody544_0, 544, 4)) (some 192) ([10, 8, 14]) (some (10, sourceBody544_13, 544, 5))

def sourceBody544_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_14 sourceBody544_5

def sourceBody544_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_15 sourceBody544_0

def sourceBody544_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_12 sourceBody544_16

def sourceBody544_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_11 sourceBody544_17

def sourceBody544_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_10 sourceBody544_18

def sourceBody544_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_0 sourceBody544_19

def sourceBody544_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_0 sourceBody544_20

def sourceBody544_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody544_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody544_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_23 sourceBody544_0

def sourceBody544_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_22 sourceBody544_24

def sourceBody544_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_21 sourceBody544_25

def sourceBody544_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_9 sourceBody544_26

def sourceBody544_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_0 sourceBody544_27

def sourceBody544_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody544_0 sourceBody544_28

def source544 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (544, 3, sourceBody544_29)
end InitECandidate.Proofs.WordStages
