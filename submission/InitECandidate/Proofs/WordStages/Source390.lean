import InitECandidate.Proofs.WordStages.Source374
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody390_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody390_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody390_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody390_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody390_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody390_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody390_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody390_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody390_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody390_0, 390, 2)) (some 389) ([12, 4, 10, 8, 14, 2]) (some (12, sourceBody390_7, 390, 3))

def sourceBody390_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody390_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_8 sourceBody390_9

def sourceBody390_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_10 sourceBody390_0

def sourceBody390_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_6 sourceBody390_11

def sourceBody390_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_5 sourceBody390_12

def sourceBody390_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_4 sourceBody390_13

def sourceBody390_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_3 sourceBody390_14

def sourceBody390_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_2 sourceBody390_15

def sourceBody390_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_1 sourceBody390_16

def sourceBody390_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody390_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody390_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_19 sourceBody390_0

def sourceBody390_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_18 sourceBody390_20

def sourceBody390_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_17 sourceBody390_21

def sourceBody390_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_0 sourceBody390_22

def sourceBody390_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody390_0 sourceBody390_23

def source390 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (390, 1, sourceBody390_24)
end InitECandidate.Proofs.WordStages
