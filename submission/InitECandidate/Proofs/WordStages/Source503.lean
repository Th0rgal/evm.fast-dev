import InitECandidate.Proofs.WordStages.Source487
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody503_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody503_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody503_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody503_0, 503, 2)) (some 471) ([]) (some (16, sourceBody503_1, 503, 3))

def sourceBody503_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody503_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_2 sourceBody503_3

def sourceBody503_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_4 sourceBody503_0

def sourceBody503_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody503_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 34, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody503_0, 503, 4)) (some 471) ([]) (some (14, sourceBody503_6, 503, 5))

def sourceBody503_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_7 sourceBody503_3

def sourceBody503_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_8 sourceBody503_0

def sourceBody503_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody503_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody503_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody503_0, 503, 6)) (some 466) ([32]) (some (32, sourceBody503_11, 503, 7))

def sourceBody503_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_12 sourceBody503_3

def sourceBody503_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_13 sourceBody503_0

def sourceBody503_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_10 sourceBody503_14

def sourceBody503_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_15

def sourceBody503_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_16

def sourceBody503_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody503_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody503_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody503_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody503_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody503_0, 503, 8)) (some 458) ([32, 8, 26, 18]) (some (32, sourceBody503_11, 503, 9))

def sourceBody503_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_22 sourceBody503_3

def sourceBody503_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_23 sourceBody503_0

def sourceBody503_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_21 sourceBody503_24

def sourceBody503_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_20 sourceBody503_25

def sourceBody503_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_19 sourceBody503_26

def sourceBody503_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_18 sourceBody503_27

def sourceBody503_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 14)

def sourceBody503_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody503_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 34)

def sourceBody503_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody503_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody503_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody503_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 8, 26, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody503_0, 503, 10)) (some 144) ([36, 2, 20, 12, 30]) (some (36, sourceBody503_34, 503, 11))

def sourceBody503_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_35 sourceBody503_3

def sourceBody503_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_36 sourceBody503_0

def sourceBody503_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_33 sourceBody503_37

def sourceBody503_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_32 sourceBody503_38

def sourceBody503_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_31 sourceBody503_39

def sourceBody503_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_30 sourceBody503_40

def sourceBody503_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_29 sourceBody503_41

def sourceBody503_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody503_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody503_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody503_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody503_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody503_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody503_0, 503, 12)) (some 472) ([2, 20, 12, 30]) (some (2, sourceBody503_47, 503, 13))

def sourceBody503_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_48 sourceBody503_3

def sourceBody503_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_49 sourceBody503_0

def sourceBody503_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_46 sourceBody503_50

def sourceBody503_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_45 sourceBody503_51

def sourceBody503_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_44 sourceBody503_52

def sourceBody503_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_43 sourceBody503_53

def sourceBody503_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_54

def sourceBody503_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_55

def sourceBody503_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody503_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody503_0, 503, 14)) (some 486) ([2]) (some (2, sourceBody503_47, 503, 15))

def sourceBody503_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_58 sourceBody503_3

def sourceBody503_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_59 sourceBody503_0

def sourceBody503_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_57 sourceBody503_60

def sourceBody503_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_61

def sourceBody503_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_62

def sourceBody503_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_56 sourceBody503_63

def sourceBody503_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody503_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody503_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_66 sourceBody503_0

def sourceBody503_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_65 sourceBody503_67

def sourceBody503_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_64 sourceBody503_68

def sourceBody503_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_42 sourceBody503_69

def sourceBody503_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_70

def sourceBody503_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_71

def sourceBody503_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_72

def sourceBody503_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_73

def sourceBody503_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_74

def sourceBody503_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_75

def sourceBody503_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_76

def sourceBody503_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_77

def sourceBody503_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_28 sourceBody503_78

def sourceBody503_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_79

def sourceBody503_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_80

def sourceBody503_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_17 sourceBody503_81

def sourceBody503_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_9 sourceBody503_82

def sourceBody503_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_83

def sourceBody503_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_84

def sourceBody503_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_85

def sourceBody503_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_86

def sourceBody503_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_87

def sourceBody503_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_88

def sourceBody503_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_89

def sourceBody503_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_90

def sourceBody503_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_5 sourceBody503_91

def sourceBody503_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_92

def sourceBody503_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_93

def sourceBody503_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_94

def sourceBody503_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_95

def sourceBody503_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_96

def sourceBody503_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_97

def sourceBody503_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_98

def sourceBody503_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody503_0 sourceBody503_99

def source503 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (503, 1, sourceBody503_100)
end InitECandidate.Proofs.WordStages
