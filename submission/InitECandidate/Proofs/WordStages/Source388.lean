import InitECandidate.Proofs.WordStages.Source372
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody388_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody388_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 192#64]))

def sourceBody388_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody388_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody388_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody388_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody388_0, 388, 2)) (some 77) ([6, 10, 8]) (some (6, sourceBody388_4, 388, 3))

def sourceBody388_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody388_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_5 sourceBody388_6

def sourceBody388_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_7 sourceBody388_0

def sourceBody388_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_3 sourceBody388_8

def sourceBody388_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_2 sourceBody388_9

def sourceBody388_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_1 sourceBody388_10

def sourceBody388_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_0 sourceBody388_11

def sourceBody388_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_0 sourceBody388_12

def sourceBody388_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 192#64]),
      Flapjack.WordLangExpHOL.const 20#64])

def sourceBody388_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody388_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody388_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody388_0, 388, 4)) (some 77) ([6, 10, 8]) (some (6, sourceBody388_4, 388, 5))

def sourceBody388_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_17 sourceBody388_6

def sourceBody388_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_18 sourceBody388_0

def sourceBody388_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_16 sourceBody388_19

def sourceBody388_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_15 sourceBody388_20

def sourceBody388_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_14 sourceBody388_21

def sourceBody388_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_0 sourceBody388_22

def sourceBody388_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_0 sourceBody388_23

def sourceBody388_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_13 sourceBody388_24

def sourceBody388_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 192#64]))

def sourceBody388_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody388_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_27 sourceBody388_0

def sourceBody388_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_26 sourceBody388_28

def sourceBody388_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody388_25 sourceBody388_29

def source388 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (388, 3, sourceBody388_30)
end InitECandidate.Proofs.WordStages
