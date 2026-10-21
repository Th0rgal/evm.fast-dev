import InitECandidate.Proofs.WordStages.Source478
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody494_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody494_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody494_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 32, 6, 26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody494_0, 494, 2)) (some 471) ([]) (some (18, sourceBody494_1, 494, 3))

def sourceBody494_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody494_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_2 sourceBody494_3

def sourceBody494_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_4 sourceBody494_0

def sourceBody494_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody494_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 38, 4, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody494_0, 494, 4)) (some 471) ([]) (some (16, sourceBody494_6, 494, 5))

def sourceBody494_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_7 sourceBody494_3

def sourceBody494_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_8 sourceBody494_0

def sourceBody494_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody494_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody494_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody494_0, 494, 6)) (some 466) ([36]) (some (36, sourceBody494_11, 494, 7))

def sourceBody494_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_12 sourceBody494_3

def sourceBody494_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_13 sourceBody494_0

def sourceBody494_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_10 sourceBody494_14

def sourceBody494_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_15

def sourceBody494_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_16

def sourceBody494_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody494_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 32)

def sourceBody494_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 6)

def sourceBody494_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody494_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody494_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody494_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody494_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody494_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody494_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 36, 10, 30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody494_0, 494, 8)) (some 120) ([20, 40, 2, 22, 14, 34, 8, 28]) (some (20, sourceBody494_26, 494, 9))

def sourceBody494_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_27 sourceBody494_3

def sourceBody494_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_28 sourceBody494_0

def sourceBody494_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_25 sourceBody494_29

def sourceBody494_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_24 sourceBody494_30

def sourceBody494_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_23 sourceBody494_31

def sourceBody494_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_22 sourceBody494_32

def sourceBody494_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_21 sourceBody494_33

def sourceBody494_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_20 sourceBody494_34

def sourceBody494_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_19 sourceBody494_35

def sourceBody494_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_18 sourceBody494_36

def sourceBody494_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody494_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 36)

def sourceBody494_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody494_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody494_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody494_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody494_0, 494, 10)) (some 472) ([40, 2, 22, 14]) (some (40, sourceBody494_42, 494, 11))

def sourceBody494_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_43 sourceBody494_3

def sourceBody494_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_44 sourceBody494_0

def sourceBody494_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_41 sourceBody494_45

def sourceBody494_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_40 sourceBody494_46

def sourceBody494_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_39 sourceBody494_47

def sourceBody494_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_38 sourceBody494_48

def sourceBody494_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_49

def sourceBody494_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_50

def sourceBody494_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody494_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody494_0, 494, 12)) (some 486) ([40]) (some (40, sourceBody494_42, 494, 13))

def sourceBody494_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_53 sourceBody494_3

def sourceBody494_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_54 sourceBody494_0

def sourceBody494_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_52 sourceBody494_55

def sourceBody494_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_56

def sourceBody494_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_57

def sourceBody494_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_51 sourceBody494_58

def sourceBody494_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody494_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody494_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_61 sourceBody494_0

def sourceBody494_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_60 sourceBody494_62

def sourceBody494_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_59 sourceBody494_63

def sourceBody494_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_37 sourceBody494_64

def sourceBody494_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_65

def sourceBody494_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_66

def sourceBody494_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_67

def sourceBody494_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_68

def sourceBody494_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_69

def sourceBody494_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_70

def sourceBody494_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_71

def sourceBody494_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_72

def sourceBody494_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_17 sourceBody494_73

def sourceBody494_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_9 sourceBody494_74

def sourceBody494_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_75

def sourceBody494_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_76

def sourceBody494_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_77

def sourceBody494_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_78

def sourceBody494_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_79

def sourceBody494_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_80

def sourceBody494_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_81

def sourceBody494_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_82

def sourceBody494_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_5 sourceBody494_83

def sourceBody494_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_84

def sourceBody494_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_85

def sourceBody494_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_86

def sourceBody494_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_87

def sourceBody494_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_88

def sourceBody494_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_89

def sourceBody494_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_90

def sourceBody494_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody494_0 sourceBody494_91

def source494 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (494, 1, sourceBody494_92)
end InitECandidate.Proofs.WordStages
