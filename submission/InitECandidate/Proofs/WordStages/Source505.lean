import InitECandidate.Proofs.WordStages.Source489
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody505_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody505_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody505_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody505_0, 505, 2)) (some 471) ([]) (some (16, sourceBody505_1, 505, 3))

def sourceBody505_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody505_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_2 sourceBody505_3

def sourceBody505_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_4 sourceBody505_0

def sourceBody505_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody505_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 32, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody505_0, 505, 4)) (some 471) ([]) (some (14, sourceBody505_6, 505, 5))

def sourceBody505_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_7 sourceBody505_3

def sourceBody505_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_8 sourceBody505_0

def sourceBody505_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody505_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody505_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody505_0, 505, 6)) (some 466) ([30]) (some (30, sourceBody505_11, 505, 7))

def sourceBody505_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_12 sourceBody505_3

def sourceBody505_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_13 sourceBody505_0

def sourceBody505_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_10 sourceBody505_14

def sourceBody505_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_15

def sourceBody505_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_16

def sourceBody505_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody505_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody505_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody505_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody505_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody505_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody505_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody505_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody505_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody505_0, 505, 8)) (some 107) ([30, 8, 26, 18, 34, 2, 20, 12]) (some (30, sourceBody505_11, 505, 9))

def sourceBody505_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_26 sourceBody505_3

def sourceBody505_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_27 sourceBody505_0

def sourceBody505_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_25 sourceBody505_28

def sourceBody505_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_24 sourceBody505_29

def sourceBody505_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_23 sourceBody505_30

def sourceBody505_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_22 sourceBody505_31

def sourceBody505_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_21 sourceBody505_32

def sourceBody505_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_20 sourceBody505_33

def sourceBody505_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_19 sourceBody505_34

def sourceBody505_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_18 sourceBody505_35

def sourceBody505_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody505_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody505_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody505_0, 505, 10)) (some 474) ([8]) (some (8, sourceBody505_38, 505, 11))

def sourceBody505_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_39 sourceBody505_3

def sourceBody505_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_40 sourceBody505_0

def sourceBody505_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_37 sourceBody505_41

def sourceBody505_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_42

def sourceBody505_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_43

def sourceBody505_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody505_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody505_0, 505, 12)) (some 486) ([8]) (some (8, sourceBody505_38, 505, 13))

def sourceBody505_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_46 sourceBody505_3

def sourceBody505_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_47 sourceBody505_0

def sourceBody505_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_45 sourceBody505_48

def sourceBody505_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_49

def sourceBody505_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_50

def sourceBody505_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_44 sourceBody505_51

def sourceBody505_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody505_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody505_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_54 sourceBody505_0

def sourceBody505_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_53 sourceBody505_55

def sourceBody505_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_52 sourceBody505_56

def sourceBody505_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_36 sourceBody505_57

def sourceBody505_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_58

def sourceBody505_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_59

def sourceBody505_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_17 sourceBody505_60

def sourceBody505_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_9 sourceBody505_61

def sourceBody505_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_62

def sourceBody505_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_63

def sourceBody505_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_64

def sourceBody505_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_65

def sourceBody505_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_66

def sourceBody505_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_67

def sourceBody505_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_68

def sourceBody505_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_69

def sourceBody505_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_5 sourceBody505_70

def sourceBody505_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_71

def sourceBody505_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_72

def sourceBody505_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_73

def sourceBody505_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_74

def sourceBody505_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_75

def sourceBody505_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_76

def sourceBody505_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_77

def sourceBody505_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody505_0 sourceBody505_78

def source505 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (505, 1, sourceBody505_79)
end InitECandidate.Proofs.WordStages
