import InitECandidate.Proofs.WordStages.Source399
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody415_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody415_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 184#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody415_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody415_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody415_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody415_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody415_0, 415, 2)) (some 384) ([6, 10, 8]) (some (6, sourceBody415_4, 415, 3))

def sourceBody415_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody415_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_5 sourceBody415_6

def sourceBody415_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_7 sourceBody415_0

def sourceBody415_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_3 sourceBody415_8

def sourceBody415_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_2 sourceBody415_9

def sourceBody415_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_1 sourceBody415_10

def sourceBody415_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_0 sourceBody415_11

def sourceBody415_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_0 sourceBody415_12

def sourceBody415_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody415_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody415_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_15 sourceBody415_0

def sourceBody415_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_14 sourceBody415_16

def sourceBody415_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody415_13 sourceBody415_17

def source415 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (415, 3, sourceBody415_18)
end InitECandidate.Proofs.WordStages
