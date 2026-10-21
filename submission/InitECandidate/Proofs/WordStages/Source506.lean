import InitECandidate.Proofs.WordStages.Source490
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody506_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody506_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody506_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody506_0, 506, 2)) (some 471) ([]) (some (16, sourceBody506_1, 506, 3))

def sourceBody506_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody506_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_2 sourceBody506_3

def sourceBody506_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_4 sourceBody506_0

def sourceBody506_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody506_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 32, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody506_0, 506, 4)) (some 471) ([]) (some (14, sourceBody506_6, 506, 5))

def sourceBody506_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_7 sourceBody506_3

def sourceBody506_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_8 sourceBody506_0

def sourceBody506_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody506_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody506_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody506_0, 506, 6)) (some 466) ([30]) (some (30, sourceBody506_11, 506, 7))

def sourceBody506_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_12 sourceBody506_3

def sourceBody506_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_13 sourceBody506_0

def sourceBody506_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_10 sourceBody506_14

def sourceBody506_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_15

def sourceBody506_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_16

def sourceBody506_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody506_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody506_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody506_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody506_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody506_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody506_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody506_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody506_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody506_0, 506, 8)) (some 108) ([30, 8, 26, 18, 34, 2, 20, 12]) (some (30, sourceBody506_11, 506, 9))

def sourceBody506_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_26 sourceBody506_3

def sourceBody506_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_27 sourceBody506_0

def sourceBody506_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_25 sourceBody506_28

def sourceBody506_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_24 sourceBody506_29

def sourceBody506_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_23 sourceBody506_30

def sourceBody506_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_22 sourceBody506_31

def sourceBody506_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_21 sourceBody506_32

def sourceBody506_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_20 sourceBody506_33

def sourceBody506_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_19 sourceBody506_34

def sourceBody506_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_18 sourceBody506_35

def sourceBody506_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody506_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody506_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody506_0, 506, 10)) (some 474) ([8]) (some (8, sourceBody506_38, 506, 11))

def sourceBody506_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_39 sourceBody506_3

def sourceBody506_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_40 sourceBody506_0

def sourceBody506_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_37 sourceBody506_41

def sourceBody506_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_42

def sourceBody506_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_43

def sourceBody506_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody506_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody506_0, 506, 12)) (some 486) ([8]) (some (8, sourceBody506_38, 506, 13))

def sourceBody506_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_46 sourceBody506_3

def sourceBody506_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_47 sourceBody506_0

def sourceBody506_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_45 sourceBody506_48

def sourceBody506_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_49

def sourceBody506_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_50

def sourceBody506_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_44 sourceBody506_51

def sourceBody506_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody506_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody506_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_54 sourceBody506_0

def sourceBody506_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_53 sourceBody506_55

def sourceBody506_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_52 sourceBody506_56

def sourceBody506_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_36 sourceBody506_57

def sourceBody506_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_58

def sourceBody506_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_59

def sourceBody506_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_17 sourceBody506_60

def sourceBody506_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_9 sourceBody506_61

def sourceBody506_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_62

def sourceBody506_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_63

def sourceBody506_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_64

def sourceBody506_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_65

def sourceBody506_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_66

def sourceBody506_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_67

def sourceBody506_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_68

def sourceBody506_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_69

def sourceBody506_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_5 sourceBody506_70

def sourceBody506_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_71

def sourceBody506_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_72

def sourceBody506_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_73

def sourceBody506_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_74

def sourceBody506_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_75

def sourceBody506_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_76

def sourceBody506_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_77

def sourceBody506_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody506_0 sourceBody506_78

def source506 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (506, 1, sourceBody506_79)
end InitECandidate.Proofs.WordStages
