import InitECandidate.Proofs.WordStages.Source463
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody479_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody479_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody479_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 6)

def sourceBody479_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody479_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 10)

def sourceBody479_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody479_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody479_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody479_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody479_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody479_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 36]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody479_0, 479, 2)) (some 476) ([22, 32, 28, 38, 20, 30, 24, 34]) (some (22, sourceBody479_9, 479, 3))

def sourceBody479_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody479_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_10 sourceBody479_11

def sourceBody479_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_12 sourceBody479_0

def sourceBody479_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_8 sourceBody479_13

def sourceBody479_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_7 sourceBody479_14

def sourceBody479_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_6 sourceBody479_15

def sourceBody479_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_5 sourceBody479_16

def sourceBody479_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_4 sourceBody479_17

def sourceBody479_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_3 sourceBody479_18

def sourceBody479_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_2 sourceBody479_19

def sourceBody479_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_1 sourceBody479_20

def sourceBody479_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 2)

def sourceBody479_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 26)

def sourceBody479_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody479_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody479_0, 479, 4)) (some 459) ([32, 28]) (some (32, sourceBody479_24, 479, 5))

def sourceBody479_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_25 sourceBody479_11

def sourceBody479_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_26 sourceBody479_0

def sourceBody479_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_23 sourceBody479_27

def sourceBody479_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_22 sourceBody479_28

def sourceBody479_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody479_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody479_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody479_0, 479, 6)) (some 466) ([28]) (some (28, sourceBody479_31, 479, 7))

def sourceBody479_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_32 sourceBody479_11

def sourceBody479_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_33 sourceBody479_0

def sourceBody479_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_30 sourceBody479_34

def sourceBody479_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_35

def sourceBody479_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_36

def sourceBody479_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 36)

def sourceBody479_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody479_0, 479, 8)) (some 478) ([28]) (some (28, sourceBody479_31, 479, 9))

def sourceBody479_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_39 sourceBody479_11

def sourceBody479_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_40 sourceBody479_0

def sourceBody479_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_38 sourceBody479_41

def sourceBody479_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_42

def sourceBody479_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_43

def sourceBody479_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_37 sourceBody479_44

def sourceBody479_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody479_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody479_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_47 sourceBody479_0

def sourceBody479_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_46 sourceBody479_48

def sourceBody479_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_45 sourceBody479_49

def sourceBody479_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_29 sourceBody479_50

def sourceBody479_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_51

def sourceBody479_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_52

def sourceBody479_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_21 sourceBody479_53

def sourceBody479_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_54

def sourceBody479_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_55

def sourceBody479_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_56

def sourceBody479_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody479_0 sourceBody479_57

def source479 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (479, 10, sourceBody479_58)
end InitECandidate.Proofs.WordStages
