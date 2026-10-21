import InitECandidate.Proofs.WordStages.Source493
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody509_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody509_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody509_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 16, 4, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody509_0, 509, 2)) (some 471) ([]) (some (10, sourceBody509_1, 509, 3))

def sourceBody509_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody509_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_2 sourceBody509_3

def sourceBody509_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_4 sourceBody509_0

def sourceBody509_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody509_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody509_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody509_0, 509, 4)) (some 466) ([18]) (some (18, sourceBody509_7, 509, 5))

def sourceBody509_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_8 sourceBody509_3

def sourceBody509_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_9 sourceBody509_0

def sourceBody509_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_6 sourceBody509_10

def sourceBody509_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_11

def sourceBody509_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_12

def sourceBody509_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody509_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody509_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody509_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody509_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody509_0, 509, 6)) (some 102) ([18, 2, 12, 8]) (some (18, sourceBody509_7, 509, 7))

def sourceBody509_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_18 sourceBody509_3

def sourceBody509_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_19 sourceBody509_0

def sourceBody509_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_17 sourceBody509_20

def sourceBody509_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_16 sourceBody509_21

def sourceBody509_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_15 sourceBody509_22

def sourceBody509_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_14 sourceBody509_23

def sourceBody509_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody509_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody509_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody509_0, 509, 8)) (some 474) ([2]) (some (2, sourceBody509_26, 509, 9))

def sourceBody509_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_27 sourceBody509_3

def sourceBody509_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_28 sourceBody509_0

def sourceBody509_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_25 sourceBody509_29

def sourceBody509_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_30

def sourceBody509_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_31

def sourceBody509_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody509_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody509_0, 509, 10)) (some 486) ([2]) (some (2, sourceBody509_26, 509, 11))

def sourceBody509_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_34 sourceBody509_3

def sourceBody509_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_35 sourceBody509_0

def sourceBody509_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_33 sourceBody509_36

def sourceBody509_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_37

def sourceBody509_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_38

def sourceBody509_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_32 sourceBody509_39

def sourceBody509_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody509_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody509_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_42 sourceBody509_0

def sourceBody509_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_41 sourceBody509_43

def sourceBody509_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_40 sourceBody509_44

def sourceBody509_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_24 sourceBody509_45

def sourceBody509_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_46

def sourceBody509_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_47

def sourceBody509_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_13 sourceBody509_48

def sourceBody509_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_5 sourceBody509_49

def sourceBody509_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_50

def sourceBody509_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_51

def sourceBody509_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_52

def sourceBody509_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_53

def sourceBody509_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_54

def sourceBody509_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_55

def sourceBody509_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_56

def sourceBody509_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody509_0 sourceBody509_57

def source509 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (509, 1, sourceBody509_58)
end InitECandidate.Proofs.WordStages
