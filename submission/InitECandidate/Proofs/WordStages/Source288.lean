import InitECandidate.Proofs.WordStages.Source272
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody288_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody288_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody288_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody288_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody288_0, 288, 2)) (some 68) ([12]) (some (12, sourceBody288_2, 288, 3))

def sourceBody288_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody288_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_3 sourceBody288_4

def sourceBody288_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_5 sourceBody288_0

def sourceBody288_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_1 sourceBody288_6

def sourceBody288_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody288_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody288_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody288_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody288_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody288_0, 288, 4)) (some 77) ([18, 10, 14]) (some (18, sourceBody288_11, 288, 5))

def sourceBody288_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_12 sourceBody288_4

def sourceBody288_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_13 sourceBody288_0

def sourceBody288_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_10 sourceBody288_14

def sourceBody288_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_9 sourceBody288_15

def sourceBody288_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_8 sourceBody288_16

def sourceBody288_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_0 sourceBody288_17

def sourceBody288_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_0 sourceBody288_18

def sourceBody288_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 4])

def sourceBody288_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody288_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody288_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody288_0, 288, 6)) (some 77) ([18, 10, 14]) (some (18, sourceBody288_11, 288, 7))

def sourceBody288_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_23 sourceBody288_4

def sourceBody288_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_24 sourceBody288_0

def sourceBody288_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_22 sourceBody288_25

def sourceBody288_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_21 sourceBody288_26

def sourceBody288_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_20 sourceBody288_27

def sourceBody288_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_0 sourceBody288_28

def sourceBody288_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_0 sourceBody288_29

def sourceBody288_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_19 sourceBody288_30

def sourceBody288_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody288_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody288_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_33 sourceBody288_0

def sourceBody288_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_32 sourceBody288_34

def sourceBody288_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_31 sourceBody288_35

def sourceBody288_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_7 sourceBody288_36

def sourceBody288_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_0 sourceBody288_37

def sourceBody288_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody288_0 sourceBody288_38

def source288 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (288, 5, sourceBody288_39)
end InitECandidate.Proofs.WordStages
