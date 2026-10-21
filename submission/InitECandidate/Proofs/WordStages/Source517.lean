import InitECandidate.Proofs.WordStages.Source501
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody517_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody517_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody517_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody517_0, 517, 2)) (some 471) ([]) (some (16, sourceBody517_1, 517, 3))

def sourceBody517_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody517_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_2 sourceBody517_3

def sourceBody517_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_4 sourceBody517_0

def sourceBody517_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody517_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 34, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody517_0, 517, 4)) (some 471) ([]) (some (14, sourceBody517_6, 517, 5))

def sourceBody517_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_7 sourceBody517_3

def sourceBody517_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_8 sourceBody517_0

def sourceBody517_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody517_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody517_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody517_0, 517, 6)) (some 466) ([32]) (some (32, sourceBody517_11, 517, 7))

def sourceBody517_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_12 sourceBody517_3

def sourceBody517_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_13 sourceBody517_0

def sourceBody517_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_10 sourceBody517_14

def sourceBody517_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_15

def sourceBody517_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_16

def sourceBody517_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody517_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody517_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody517_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody517_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody517_0, 517, 8)) (some 458) ([32, 8, 26, 18]) (some (32, sourceBody517_11, 517, 9))

def sourceBody517_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_22 sourceBody517_3

def sourceBody517_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_23 sourceBody517_0

def sourceBody517_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_21 sourceBody517_24

def sourceBody517_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_20 sourceBody517_25

def sourceBody517_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_19 sourceBody517_26

def sourceBody517_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_18 sourceBody517_27

def sourceBody517_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 16)

def sourceBody517_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 34)

def sourceBody517_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody517_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody517_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody517_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody517_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 8, 26, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody517_0, 517, 10)) (some 143) ([36, 2, 20, 12, 30]) (some (36, sourceBody517_34, 517, 11))

def sourceBody517_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_35 sourceBody517_3

def sourceBody517_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_36 sourceBody517_0

def sourceBody517_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_33 sourceBody517_37

def sourceBody517_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_32 sourceBody517_38

def sourceBody517_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_31 sourceBody517_39

def sourceBody517_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_30 sourceBody517_40

def sourceBody517_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_29 sourceBody517_41

def sourceBody517_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody517_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody517_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody517_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody517_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody517_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody517_0, 517, 12)) (some 472) ([2, 20, 12, 30]) (some (2, sourceBody517_47, 517, 13))

def sourceBody517_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_48 sourceBody517_3

def sourceBody517_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_49 sourceBody517_0

def sourceBody517_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_46 sourceBody517_50

def sourceBody517_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_45 sourceBody517_51

def sourceBody517_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_44 sourceBody517_52

def sourceBody517_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_43 sourceBody517_53

def sourceBody517_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_54

def sourceBody517_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_55

def sourceBody517_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody517_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody517_0, 517, 14)) (some 486) ([2]) (some (2, sourceBody517_47, 517, 15))

def sourceBody517_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_58 sourceBody517_3

def sourceBody517_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_59 sourceBody517_0

def sourceBody517_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_57 sourceBody517_60

def sourceBody517_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_61

def sourceBody517_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_62

def sourceBody517_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_56 sourceBody517_63

def sourceBody517_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody517_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody517_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_66 sourceBody517_0

def sourceBody517_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_65 sourceBody517_67

def sourceBody517_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_64 sourceBody517_68

def sourceBody517_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_42 sourceBody517_69

def sourceBody517_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_70

def sourceBody517_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_71

def sourceBody517_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_72

def sourceBody517_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_73

def sourceBody517_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_74

def sourceBody517_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_75

def sourceBody517_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_76

def sourceBody517_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_77

def sourceBody517_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_28 sourceBody517_78

def sourceBody517_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_79

def sourceBody517_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_80

def sourceBody517_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_17 sourceBody517_81

def sourceBody517_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_9 sourceBody517_82

def sourceBody517_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_83

def sourceBody517_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_84

def sourceBody517_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_85

def sourceBody517_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_86

def sourceBody517_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_87

def sourceBody517_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_88

def sourceBody517_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_89

def sourceBody517_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_90

def sourceBody517_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_5 sourceBody517_91

def sourceBody517_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_92

def sourceBody517_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_93

def sourceBody517_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_94

def sourceBody517_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_95

def sourceBody517_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_96

def sourceBody517_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_97

def sourceBody517_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_98

def sourceBody517_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody517_0 sourceBody517_99

def source517 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (517, 1, sourceBody517_100)
end InitECandidate.Proofs.WordStages
