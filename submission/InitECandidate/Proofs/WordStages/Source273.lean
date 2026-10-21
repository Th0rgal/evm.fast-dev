import InitECandidate.Proofs.WordStages.Source257
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody273_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody273_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody273_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody273_0, 273, 2)) (some 69) ([]) (some (8, sourceBody273_1, 273, 3))

def sourceBody273_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody273_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_2 sourceBody273_3

def sourceBody273_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_4 sourceBody273_0

def sourceBody273_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody273_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody273_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody273_0, 273, 4)) (some 272) ([10]) (some (10, sourceBody273_7, 273, 5))

def sourceBody273_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_8 sourceBody273_3

def sourceBody273_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_9 sourceBody273_0

def sourceBody273_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_6 sourceBody273_10

def sourceBody273_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody273_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody273_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody273_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody273_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody273_0, 273, 6)) (some 158) ([18, 6, 12]) (some (18, sourceBody273_15, 273, 7))

def sourceBody273_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_16 sourceBody273_3

def sourceBody273_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_17 sourceBody273_0

def sourceBody273_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_14 sourceBody273_18

def sourceBody273_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_13 sourceBody273_19

def sourceBody273_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_12 sourceBody273_20

def sourceBody273_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_21

def sourceBody273_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_22

def sourceBody273_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody273_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody273_0, 273, 8)) (some 70) ([18]) (some (18, sourceBody273_15, 273, 9))

def sourceBody273_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_25 sourceBody273_3

def sourceBody273_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_26 sourceBody273_0

def sourceBody273_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_24 sourceBody273_27

def sourceBody273_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_28

def sourceBody273_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_29

def sourceBody273_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_23 sourceBody273_30

def sourceBody273_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody273_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody273_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_33 sourceBody273_0

def sourceBody273_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_32 sourceBody273_34

def sourceBody273_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_31 sourceBody273_35

def sourceBody273_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_11 sourceBody273_36

def sourceBody273_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_37

def sourceBody273_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_38

def sourceBody273_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_39

def sourceBody273_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_40

def sourceBody273_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_5 sourceBody273_41

def sourceBody273_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_42

def sourceBody273_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody273_0 sourceBody273_43

def source273 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (273, 3, sourceBody273_44)
end InitECandidate.Proofs.WordStages
