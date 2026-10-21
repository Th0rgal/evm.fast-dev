import InitECandidate.Proofs.WordStages.Source769
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody785_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody785_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody785_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody785_0, 785, 2)) (some 69) ([]) (some (14, sourceBody785_1, 785, 3))

def sourceBody785_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody785_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_2 sourceBody785_3

def sourceBody785_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_4 sourceBody785_0

def sourceBody785_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody785_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody785_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody785_0, 785, 4)) (some 68) ([6]) (some (6, sourceBody785_7, 785, 5))

def sourceBody785_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_8 sourceBody785_3

def sourceBody785_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_9 sourceBody785_0

def sourceBody785_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_6 sourceBody785_10

def sourceBody785_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody785_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody785_14 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody785_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody785_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody785_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody785_0, 785, 6)) (some 780) ([12, 10, 16, 4]) (some (12, sourceBody785_16, 785, 7))

def sourceBody785_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_17 sourceBody785_3

def sourceBody785_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_18 sourceBody785_0

def sourceBody785_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_15 sourceBody785_19

def sourceBody785_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_14 sourceBody785_20

def sourceBody785_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_13 sourceBody785_21

def sourceBody785_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_12 sourceBody785_22

def sourceBody785_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_23

def sourceBody785_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_24

def sourceBody785_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody785_0, 785, 8)) (some 775) ([12]) (some (12, sourceBody785_16, 785, 9))

def sourceBody785_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_26 sourceBody785_3

def sourceBody785_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_27 sourceBody785_0

def sourceBody785_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_12 sourceBody785_28

def sourceBody785_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody785_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody785_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody785_0, 785, 10)) (some 70) ([10]) (some (10, sourceBody785_31, 785, 11))

def sourceBody785_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_32 sourceBody785_3

def sourceBody785_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_33 sourceBody785_0

def sourceBody785_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_30 sourceBody785_34

def sourceBody785_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_35

def sourceBody785_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_36

def sourceBody785_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody785_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody785_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_39 sourceBody785_0

def sourceBody785_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_38 sourceBody785_40

def sourceBody785_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_37 sourceBody785_41

def sourceBody785_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_29 sourceBody785_42

def sourceBody785_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_43

def sourceBody785_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_44

def sourceBody785_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_25 sourceBody785_45

def sourceBody785_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_11 sourceBody785_46

def sourceBody785_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_47

def sourceBody785_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_48

def sourceBody785_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_5 sourceBody785_49

def sourceBody785_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_50

def sourceBody785_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody785_0 sourceBody785_51

def source785 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (785, 2, sourceBody785_52)
end InitECandidate.Proofs.WordStages
