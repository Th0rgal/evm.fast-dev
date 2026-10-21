import InitECandidate.Proofs.WordStages.Source757
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody773_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody773_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody773_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody773_0, 773, 2)) (some 69) ([]) (some (14, sourceBody773_1, 773, 3))

def sourceBody773_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody773_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_2 sourceBody773_3

def sourceBody773_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_4 sourceBody773_0

def sourceBody773_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody773_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody773_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody773_0, 773, 4)) (some 68) ([6]) (some (6, sourceBody773_7, 773, 5))

def sourceBody773_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_8 sourceBody773_3

def sourceBody773_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_9 sourceBody773_0

def sourceBody773_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_6 sourceBody773_10

def sourceBody773_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody773_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody773_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 1344#64])

def sourceBody773_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody773_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody773_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody773_0, 773, 6)) (some 768) ([12, 10, 16, 4]) (some (12, sourceBody773_16, 773, 7))

def sourceBody773_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_17 sourceBody773_3

def sourceBody773_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_18 sourceBody773_0

def sourceBody773_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_15 sourceBody773_19

def sourceBody773_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_14 sourceBody773_20

def sourceBody773_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_13 sourceBody773_21

def sourceBody773_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_12 sourceBody773_22

def sourceBody773_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_23

def sourceBody773_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_24

def sourceBody773_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody773_0, 773, 8)) (some 763) ([12]) (some (12, sourceBody773_16, 773, 9))

def sourceBody773_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_26 sourceBody773_3

def sourceBody773_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_27 sourceBody773_0

def sourceBody773_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_12 sourceBody773_28

def sourceBody773_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody773_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody773_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody773_0, 773, 10)) (some 70) ([10]) (some (10, sourceBody773_31, 773, 11))

def sourceBody773_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_32 sourceBody773_3

def sourceBody773_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_33 sourceBody773_0

def sourceBody773_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_30 sourceBody773_34

def sourceBody773_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_35

def sourceBody773_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_36

def sourceBody773_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody773_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody773_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_39 sourceBody773_0

def sourceBody773_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_38 sourceBody773_40

def sourceBody773_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_37 sourceBody773_41

def sourceBody773_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_29 sourceBody773_42

def sourceBody773_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_43

def sourceBody773_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_44

def sourceBody773_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_25 sourceBody773_45

def sourceBody773_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_11 sourceBody773_46

def sourceBody773_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_47

def sourceBody773_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_48

def sourceBody773_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_5 sourceBody773_49

def sourceBody773_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_50

def sourceBody773_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody773_0 sourceBody773_51

def source773 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (773, 2, sourceBody773_52)
end InitECandidate.Proofs.WordStages
