import InitECandidate.Proofs.WordStages.Source504
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody520_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody520_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 104#64])

def sourceBody520_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody520_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 6)

def sourceBody520_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 2

def sourceBody520_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_4 sourceBody520_0

def sourceBody520_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_3 sourceBody520_5

def sourceBody520_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_6 sourceBody520_0

def sourceBody520_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_2 sourceBody520_7

def sourceBody520_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_0 sourceBody520_8

def sourceBody520_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_1 sourceBody520_9

def sourceBody520_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_0 sourceBody520_10

def sourceBody520_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody520_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody520_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody520_0, 520, 2)) (some 486) ([6]) (some (6, sourceBody520_13, 520, 3))

def sourceBody520_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody520_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_14 sourceBody520_15

def sourceBody520_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_16 sourceBody520_0

def sourceBody520_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_12 sourceBody520_17

def sourceBody520_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_0 sourceBody520_18

def sourceBody520_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_0 sourceBody520_19

def sourceBody520_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_11 sourceBody520_20

def sourceBody520_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody520_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody520_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_23 sourceBody520_0

def sourceBody520_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_22 sourceBody520_24

def sourceBody520_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody520_21 sourceBody520_25

def source520 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (520, 1, sourceBody520_26)
end InitECandidate.Proofs.WordStages
