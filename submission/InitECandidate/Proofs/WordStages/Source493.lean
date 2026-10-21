import InitECandidate.Proofs.WordStages.Source477
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody493_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody493_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody493_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 32, 6, 26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody493_0, 493, 2)) (some 471) ([]) (some (18, sourceBody493_1, 493, 3))

def sourceBody493_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody493_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_2 sourceBody493_3

def sourceBody493_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_4 sourceBody493_0

def sourceBody493_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody493_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 38, 4, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody493_0, 493, 4)) (some 471) ([]) (some (16, sourceBody493_6, 493, 5))

def sourceBody493_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_7 sourceBody493_3

def sourceBody493_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_8 sourceBody493_0

def sourceBody493_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody493_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody493_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody493_0, 493, 6)) (some 466) ([36]) (some (36, sourceBody493_11, 493, 7))

def sourceBody493_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_12 sourceBody493_3

def sourceBody493_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_13 sourceBody493_0

def sourceBody493_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_10 sourceBody493_14

def sourceBody493_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_15

def sourceBody493_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_16

def sourceBody493_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody493_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 32)

def sourceBody493_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 6)

def sourceBody493_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody493_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody493_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody493_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody493_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody493_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody493_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 36, 10, 30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody493_0, 493, 8)) (some 116) ([20, 40, 2, 22, 14, 34, 8, 28]) (some (20, sourceBody493_26, 493, 9))

def sourceBody493_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_27 sourceBody493_3

def sourceBody493_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_28 sourceBody493_0

def sourceBody493_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_25 sourceBody493_29

def sourceBody493_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_24 sourceBody493_30

def sourceBody493_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_23 sourceBody493_31

def sourceBody493_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_22 sourceBody493_32

def sourceBody493_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_21 sourceBody493_33

def sourceBody493_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_20 sourceBody493_34

def sourceBody493_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_19 sourceBody493_35

def sourceBody493_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_18 sourceBody493_36

def sourceBody493_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody493_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 36)

def sourceBody493_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody493_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody493_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody493_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody493_0, 493, 10)) (some 472) ([40, 2, 22, 14]) (some (40, sourceBody493_42, 493, 11))

def sourceBody493_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_43 sourceBody493_3

def sourceBody493_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_44 sourceBody493_0

def sourceBody493_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_41 sourceBody493_45

def sourceBody493_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_40 sourceBody493_46

def sourceBody493_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_39 sourceBody493_47

def sourceBody493_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_38 sourceBody493_48

def sourceBody493_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_49

def sourceBody493_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_50

def sourceBody493_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody493_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody493_0, 493, 12)) (some 486) ([40]) (some (40, sourceBody493_42, 493, 13))

def sourceBody493_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_53 sourceBody493_3

def sourceBody493_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_54 sourceBody493_0

def sourceBody493_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_52 sourceBody493_55

def sourceBody493_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_56

def sourceBody493_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_57

def sourceBody493_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_51 sourceBody493_58

def sourceBody493_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody493_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody493_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_61 sourceBody493_0

def sourceBody493_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_60 sourceBody493_62

def sourceBody493_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_59 sourceBody493_63

def sourceBody493_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_37 sourceBody493_64

def sourceBody493_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_65

def sourceBody493_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_66

def sourceBody493_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_67

def sourceBody493_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_68

def sourceBody493_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_69

def sourceBody493_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_70

def sourceBody493_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_71

def sourceBody493_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_72

def sourceBody493_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_17 sourceBody493_73

def sourceBody493_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_9 sourceBody493_74

def sourceBody493_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_75

def sourceBody493_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_76

def sourceBody493_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_77

def sourceBody493_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_78

def sourceBody493_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_79

def sourceBody493_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_80

def sourceBody493_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_81

def sourceBody493_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_82

def sourceBody493_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_5 sourceBody493_83

def sourceBody493_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_84

def sourceBody493_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_85

def sourceBody493_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_86

def sourceBody493_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_87

def sourceBody493_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_88

def sourceBody493_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_89

def sourceBody493_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_90

def sourceBody493_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody493_0 sourceBody493_91

def source493 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (493, 1, sourceBody493_92)
end InitECandidate.Proofs.WordStages
