import InitECandidate.Proofs.WordStages.Source337
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody353_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody353_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody353_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody353_0, 353, 2)) (some 69) ([]) (some (26, sourceBody353_1, 353, 3))

def sourceBody353_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody353_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_2 sourceBody353_3

def sourceBody353_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_4 sourceBody353_0

def sourceBody353_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody353_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody353_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody353_0, 353, 4)) (some 68) ([12]) (some (12, sourceBody353_7, 353, 5))

def sourceBody353_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_8 sourceBody353_3

def sourceBody353_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_9 sourceBody353_0

def sourceBody353_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_6 sourceBody353_10

def sourceBody353_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody353_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody353_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody353_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody353_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody353_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody353_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody353_0, 353, 6)) (some 148) ([20, 16, 24, 14, 22]) (some (20, sourceBody353_17, 353, 7))

def sourceBody353_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_18 sourceBody353_3

def sourceBody353_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_19 sourceBody353_0

def sourceBody353_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_16 sourceBody353_20

def sourceBody353_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_15 sourceBody353_21

def sourceBody353_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_14 sourceBody353_22

def sourceBody353_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_13 sourceBody353_23

def sourceBody353_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_12 sourceBody353_24

def sourceBody353_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody353_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody353_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody353_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody353_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody353_0, 353, 8)) (some 176) ([16, 24, 14]) (some (16, sourceBody353_29, 353, 9))

def sourceBody353_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_30 sourceBody353_3

def sourceBody353_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_31 sourceBody353_0

def sourceBody353_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_28 sourceBody353_32

def sourceBody353_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_27 sourceBody353_33

def sourceBody353_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_26 sourceBody353_34

def sourceBody353_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody353_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody353_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody353_0, 353, 10)) (some 70) ([24]) (some (24, sourceBody353_37, 353, 11))

def sourceBody353_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_38 sourceBody353_3

def sourceBody353_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_39 sourceBody353_0

def sourceBody353_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_36 sourceBody353_40

def sourceBody353_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_41

def sourceBody353_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_42

def sourceBody353_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody353_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody353_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_45 sourceBody353_0

def sourceBody353_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_44 sourceBody353_46

def sourceBody353_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_43 sourceBody353_47

def sourceBody353_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_35 sourceBody353_48

def sourceBody353_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_49

def sourceBody353_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_50

def sourceBody353_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_25 sourceBody353_51

def sourceBody353_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_52

def sourceBody353_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_53

def sourceBody353_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_11 sourceBody353_54

def sourceBody353_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_55

def sourceBody353_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_56

def sourceBody353_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_5 sourceBody353_57

def sourceBody353_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_58

def sourceBody353_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody353_0 sourceBody353_59

def source353 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (353, 6, sourceBody353_60)
end InitECandidate.Proofs.WordStages
