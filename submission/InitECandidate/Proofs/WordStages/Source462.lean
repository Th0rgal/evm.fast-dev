import InitECandidate.Proofs.WordStages.Source446
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody462_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody462_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 240#64])

def sourceBody462_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody462_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody462_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody462_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody462_0, 462, 2)) (some 88) ([16, 10]) (some (16, sourceBody462_4, 462, 3))

def sourceBody462_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody462_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_5 sourceBody462_6

def sourceBody462_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_7 sourceBody462_0

def sourceBody462_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_3 sourceBody462_8

def sourceBody462_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_2 sourceBody462_9

def sourceBody462_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_0 sourceBody462_10

def sourceBody462_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_0 sourceBody462_11

def sourceBody462_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody462_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody462_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody462_0, 462, 4)) (some 89) ([16, 10]) (some (16, sourceBody462_4, 462, 5))

def sourceBody462_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_15 sourceBody462_6

def sourceBody462_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_16 sourceBody462_0

def sourceBody462_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_14 sourceBody462_17

def sourceBody462_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_13 sourceBody462_18

def sourceBody462_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_0 sourceBody462_19

def sourceBody462_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_0 sourceBody462_20

def sourceBody462_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_12 sourceBody462_21

def sourceBody462_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 12#64])

def sourceBody462_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody462_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody462_0, 462, 6)) (some 89) ([16, 10]) (some (16, sourceBody462_4, 462, 7))

def sourceBody462_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_25 sourceBody462_6

def sourceBody462_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_26 sourceBody462_0

def sourceBody462_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_24 sourceBody462_27

def sourceBody462_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_23 sourceBody462_28

def sourceBody462_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_0 sourceBody462_29

def sourceBody462_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_0 sourceBody462_30

def sourceBody462_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_22 sourceBody462_31

def sourceBody462_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody462_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody462_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_34 sourceBody462_0

def sourceBody462_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_33 sourceBody462_35

def sourceBody462_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_32 sourceBody462_36

def sourceBody462_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_1 sourceBody462_37

def sourceBody462_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody462_0 sourceBody462_38

def source462 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (462, 5, sourceBody462_39)
end InitECandidate.Proofs.WordStages
