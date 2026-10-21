import InitECandidate.Proofs.WordStages.Source479
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody495_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody495_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody495_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 32, 6, 26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody495_0, 495, 2)) (some 471) ([]) (some (18, sourceBody495_1, 495, 3))

def sourceBody495_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody495_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_2 sourceBody495_3

def sourceBody495_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_4 sourceBody495_0

def sourceBody495_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody495_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 38, 4, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody495_0, 495, 4)) (some 471) ([]) (some (16, sourceBody495_6, 495, 5))

def sourceBody495_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_7 sourceBody495_3

def sourceBody495_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_8 sourceBody495_0

def sourceBody495_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody495_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody495_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody495_0, 495, 6)) (some 466) ([36]) (some (36, sourceBody495_11, 495, 7))

def sourceBody495_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_12 sourceBody495_3

def sourceBody495_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_13 sourceBody495_0

def sourceBody495_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_10 sourceBody495_14

def sourceBody495_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_15

def sourceBody495_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_16

def sourceBody495_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody495_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 32)

def sourceBody495_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 6)

def sourceBody495_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody495_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody495_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody495_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody495_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody495_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody495_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 36, 10, 30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody495_0, 495, 8)) (some 117) ([20, 40, 2, 22, 14, 34, 8, 28]) (some (20, sourceBody495_26, 495, 9))

def sourceBody495_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_27 sourceBody495_3

def sourceBody495_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_28 sourceBody495_0

def sourceBody495_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_25 sourceBody495_29

def sourceBody495_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_24 sourceBody495_30

def sourceBody495_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_23 sourceBody495_31

def sourceBody495_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_22 sourceBody495_32

def sourceBody495_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_21 sourceBody495_33

def sourceBody495_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_20 sourceBody495_34

def sourceBody495_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_19 sourceBody495_35

def sourceBody495_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_18 sourceBody495_36

def sourceBody495_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody495_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 36)

def sourceBody495_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody495_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody495_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody495_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody495_0, 495, 10)) (some 472) ([40, 2, 22, 14]) (some (40, sourceBody495_42, 495, 11))

def sourceBody495_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_43 sourceBody495_3

def sourceBody495_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_44 sourceBody495_0

def sourceBody495_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_41 sourceBody495_45

def sourceBody495_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_40 sourceBody495_46

def sourceBody495_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_39 sourceBody495_47

def sourceBody495_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_38 sourceBody495_48

def sourceBody495_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_49

def sourceBody495_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_50

def sourceBody495_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody495_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody495_0, 495, 12)) (some 486) ([40]) (some (40, sourceBody495_42, 495, 13))

def sourceBody495_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_53 sourceBody495_3

def sourceBody495_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_54 sourceBody495_0

def sourceBody495_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_52 sourceBody495_55

def sourceBody495_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_56

def sourceBody495_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_57

def sourceBody495_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_51 sourceBody495_58

def sourceBody495_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody495_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody495_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_61 sourceBody495_0

def sourceBody495_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_60 sourceBody495_62

def sourceBody495_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_59 sourceBody495_63

def sourceBody495_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_37 sourceBody495_64

def sourceBody495_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_65

def sourceBody495_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_66

def sourceBody495_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_67

def sourceBody495_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_68

def sourceBody495_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_69

def sourceBody495_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_70

def sourceBody495_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_71

def sourceBody495_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_72

def sourceBody495_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_17 sourceBody495_73

def sourceBody495_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_9 sourceBody495_74

def sourceBody495_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_75

def sourceBody495_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_76

def sourceBody495_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_77

def sourceBody495_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_78

def sourceBody495_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_79

def sourceBody495_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_80

def sourceBody495_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_81

def sourceBody495_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_82

def sourceBody495_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_5 sourceBody495_83

def sourceBody495_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_84

def sourceBody495_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_85

def sourceBody495_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_86

def sourceBody495_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_87

def sourceBody495_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_88

def sourceBody495_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_89

def sourceBody495_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_90

def sourceBody495_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody495_0 sourceBody495_91

def source495 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (495, 1, sourceBody495_92)
end InitECandidate.Proofs.WordStages
