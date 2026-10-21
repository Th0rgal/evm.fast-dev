import InitECandidate.Proofs.WordStages.Source350
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody366_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody366_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody366_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody366_0, 366, 2)) (some 69) ([]) (some (14, sourceBody366_1, 366, 3))

def sourceBody366_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody366_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_2 sourceBody366_3

def sourceBody366_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_4 sourceBody366_0

def sourceBody366_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody366_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody366_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody366_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody366_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody366_0, 366, 4)) (some 363) ([10, 16, 12]) (some (10, sourceBody366_9, 366, 5))

def sourceBody366_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_10 sourceBody366_3

def sourceBody366_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_11 sourceBody366_0

def sourceBody366_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_8 sourceBody366_12

def sourceBody366_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_7 sourceBody366_13

def sourceBody366_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_6 sourceBody366_14

def sourceBody366_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody366_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody366_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody366_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody366_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody366_0, 366, 6)) (some 158) ([16, 12, 20]) (some (16, sourceBody366_19, 366, 7))

def sourceBody366_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_20 sourceBody366_3

def sourceBody366_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_21 sourceBody366_0

def sourceBody366_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_18 sourceBody366_22

def sourceBody366_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_17 sourceBody366_23

def sourceBody366_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_16 sourceBody366_24

def sourceBody366_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_25

def sourceBody366_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_26

def sourceBody366_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody366_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody366_0, 366, 8)) (some 70) ([16]) (some (16, sourceBody366_19, 366, 9))

def sourceBody366_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_29 sourceBody366_3

def sourceBody366_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_30 sourceBody366_0

def sourceBody366_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_28 sourceBody366_31

def sourceBody366_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_32

def sourceBody366_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_33

def sourceBody366_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_27 sourceBody366_34

def sourceBody366_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody366_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody366_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_37 sourceBody366_0

def sourceBody366_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_36 sourceBody366_38

def sourceBody366_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_35 sourceBody366_39

def sourceBody366_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_15 sourceBody366_40

def sourceBody366_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_41

def sourceBody366_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_42

def sourceBody366_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_43

def sourceBody366_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_44

def sourceBody366_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_5 sourceBody366_45

def sourceBody366_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_46

def sourceBody366_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody366_0 sourceBody366_47

def source366 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (366, 5, sourceBody366_48)
end InitECandidate.Proofs.WordStages
