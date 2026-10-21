import InitECandidate.Proofs.WordStages.Source480
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody496_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody496_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody496_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 32, 6, 26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody496_0, 496, 2)) (some 471) ([]) (some (18, sourceBody496_1, 496, 3))

def sourceBody496_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody496_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_2 sourceBody496_3

def sourceBody496_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_4 sourceBody496_0

def sourceBody496_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody496_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 38, 4, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody496_0, 496, 4)) (some 471) ([]) (some (16, sourceBody496_6, 496, 5))

def sourceBody496_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_7 sourceBody496_3

def sourceBody496_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_8 sourceBody496_0

def sourceBody496_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody496_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody496_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody496_0, 496, 6)) (some 466) ([36]) (some (36, sourceBody496_11, 496, 7))

def sourceBody496_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_12 sourceBody496_3

def sourceBody496_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_13 sourceBody496_0

def sourceBody496_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_10 sourceBody496_14

def sourceBody496_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_15

def sourceBody496_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_16

def sourceBody496_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody496_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 32)

def sourceBody496_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 6)

def sourceBody496_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody496_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody496_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody496_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody496_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody496_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody496_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 36, 10, 30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody496_0, 496, 8)) (some 130) ([20, 40, 2, 22, 14, 34, 8, 28]) (some (20, sourceBody496_26, 496, 9))

def sourceBody496_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_27 sourceBody496_3

def sourceBody496_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_28 sourceBody496_0

def sourceBody496_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_25 sourceBody496_29

def sourceBody496_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_24 sourceBody496_30

def sourceBody496_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_23 sourceBody496_31

def sourceBody496_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_22 sourceBody496_32

def sourceBody496_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_21 sourceBody496_33

def sourceBody496_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_20 sourceBody496_34

def sourceBody496_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_19 sourceBody496_35

def sourceBody496_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_18 sourceBody496_36

def sourceBody496_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody496_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 36)

def sourceBody496_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody496_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody496_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody496_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody496_0, 496, 10)) (some 472) ([40, 2, 22, 14]) (some (40, sourceBody496_42, 496, 11))

def sourceBody496_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_43 sourceBody496_3

def sourceBody496_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_44 sourceBody496_0

def sourceBody496_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_41 sourceBody496_45

def sourceBody496_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_40 sourceBody496_46

def sourceBody496_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_39 sourceBody496_47

def sourceBody496_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_38 sourceBody496_48

def sourceBody496_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_49

def sourceBody496_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_50

def sourceBody496_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody496_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody496_0, 496, 12)) (some 486) ([40]) (some (40, sourceBody496_42, 496, 13))

def sourceBody496_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_53 sourceBody496_3

def sourceBody496_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_54 sourceBody496_0

def sourceBody496_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_52 sourceBody496_55

def sourceBody496_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_56

def sourceBody496_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_57

def sourceBody496_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_51 sourceBody496_58

def sourceBody496_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody496_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody496_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_61 sourceBody496_0

def sourceBody496_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_60 sourceBody496_62

def sourceBody496_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_59 sourceBody496_63

def sourceBody496_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_37 sourceBody496_64

def sourceBody496_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_65

def sourceBody496_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_66

def sourceBody496_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_67

def sourceBody496_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_68

def sourceBody496_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_69

def sourceBody496_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_70

def sourceBody496_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_71

def sourceBody496_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_72

def sourceBody496_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_17 sourceBody496_73

def sourceBody496_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_9 sourceBody496_74

def sourceBody496_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_75

def sourceBody496_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_76

def sourceBody496_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_77

def sourceBody496_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_78

def sourceBody496_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_79

def sourceBody496_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_80

def sourceBody496_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_81

def sourceBody496_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_82

def sourceBody496_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_5 sourceBody496_83

def sourceBody496_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_84

def sourceBody496_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_85

def sourceBody496_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_86

def sourceBody496_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_87

def sourceBody496_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_88

def sourceBody496_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_89

def sourceBody496_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_90

def sourceBody496_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody496_0 sourceBody496_91

def source496 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (496, 1, sourceBody496_92)
end InitECandidate.Proofs.WordStages
