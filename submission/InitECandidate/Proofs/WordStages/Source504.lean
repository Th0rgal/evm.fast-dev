import InitECandidate.Proofs.WordStages.Source488
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody504_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody504_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody504_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody504_0, 504, 2)) (some 471) ([]) (some (16, sourceBody504_1, 504, 3))

def sourceBody504_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody504_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_2 sourceBody504_3

def sourceBody504_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_4 sourceBody504_0

def sourceBody504_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody504_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 32, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody504_0, 504, 4)) (some 471) ([]) (some (14, sourceBody504_6, 504, 5))

def sourceBody504_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_7 sourceBody504_3

def sourceBody504_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_8 sourceBody504_0

def sourceBody504_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody504_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody504_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody504_0, 504, 6)) (some 466) ([30]) (some (30, sourceBody504_11, 504, 7))

def sourceBody504_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_12 sourceBody504_3

def sourceBody504_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_13 sourceBody504_0

def sourceBody504_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_10 sourceBody504_14

def sourceBody504_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_15

def sourceBody504_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_16

def sourceBody504_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody504_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody504_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody504_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody504_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody504_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody504_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody504_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody504_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody504_0, 504, 8)) (some 106) ([30, 8, 26, 18, 34, 2, 20, 12]) (some (30, sourceBody504_11, 504, 9))

def sourceBody504_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_26 sourceBody504_3

def sourceBody504_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_27 sourceBody504_0

def sourceBody504_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_25 sourceBody504_28

def sourceBody504_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_24 sourceBody504_29

def sourceBody504_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_23 sourceBody504_30

def sourceBody504_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_22 sourceBody504_31

def sourceBody504_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_21 sourceBody504_32

def sourceBody504_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_20 sourceBody504_33

def sourceBody504_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_19 sourceBody504_34

def sourceBody504_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_18 sourceBody504_35

def sourceBody504_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody504_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody504_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody504_0, 504, 10)) (some 474) ([8]) (some (8, sourceBody504_38, 504, 11))

def sourceBody504_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_39 sourceBody504_3

def sourceBody504_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_40 sourceBody504_0

def sourceBody504_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_37 sourceBody504_41

def sourceBody504_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_42

def sourceBody504_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_43

def sourceBody504_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody504_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody504_0, 504, 12)) (some 486) ([8]) (some (8, sourceBody504_38, 504, 13))

def sourceBody504_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_46 sourceBody504_3

def sourceBody504_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_47 sourceBody504_0

def sourceBody504_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_45 sourceBody504_48

def sourceBody504_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_49

def sourceBody504_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_50

def sourceBody504_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_44 sourceBody504_51

def sourceBody504_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody504_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody504_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_54 sourceBody504_0

def sourceBody504_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_53 sourceBody504_55

def sourceBody504_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_52 sourceBody504_56

def sourceBody504_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_36 sourceBody504_57

def sourceBody504_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_58

def sourceBody504_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_59

def sourceBody504_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_17 sourceBody504_60

def sourceBody504_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_9 sourceBody504_61

def sourceBody504_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_62

def sourceBody504_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_63

def sourceBody504_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_64

def sourceBody504_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_65

def sourceBody504_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_66

def sourceBody504_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_67

def sourceBody504_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_68

def sourceBody504_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_69

def sourceBody504_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_5 sourceBody504_70

def sourceBody504_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_71

def sourceBody504_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_72

def sourceBody504_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_73

def sourceBody504_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_74

def sourceBody504_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_75

def sourceBody504_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_76

def sourceBody504_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_77

def sourceBody504_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody504_0 sourceBody504_78

def source504 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (504, 1, sourceBody504_79)
end InitECandidate.Proofs.WordStages
