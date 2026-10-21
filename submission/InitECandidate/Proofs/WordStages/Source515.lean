import InitECandidate.Proofs.WordStages.Source499
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody515_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody515_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody515_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody515_0, 515, 2)) (some 471) ([]) (some (16, sourceBody515_1, 515, 3))

def sourceBody515_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody515_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_2 sourceBody515_3

def sourceBody515_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_4 sourceBody515_0

def sourceBody515_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody515_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 34, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody515_0, 515, 4)) (some 471) ([]) (some (14, sourceBody515_6, 515, 5))

def sourceBody515_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_7 sourceBody515_3

def sourceBody515_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_8 sourceBody515_0

def sourceBody515_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody515_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody515_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody515_0, 515, 6)) (some 466) ([32]) (some (32, sourceBody515_11, 515, 7))

def sourceBody515_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_12 sourceBody515_3

def sourceBody515_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_13 sourceBody515_0

def sourceBody515_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_10 sourceBody515_14

def sourceBody515_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_15

def sourceBody515_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_16

def sourceBody515_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody515_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody515_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody515_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody515_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody515_0, 515, 8)) (some 458) ([32, 8, 26, 18]) (some (32, sourceBody515_11, 515, 9))

def sourceBody515_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_22 sourceBody515_3

def sourceBody515_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_23 sourceBody515_0

def sourceBody515_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_21 sourceBody515_24

def sourceBody515_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_20 sourceBody515_25

def sourceBody515_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_19 sourceBody515_26

def sourceBody515_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_18 sourceBody515_27

def sourceBody515_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 16)

def sourceBody515_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 34)

def sourceBody515_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody515_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody515_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody515_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody515_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 8, 26, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody515_0, 515, 10)) (some 141) ([36, 2, 20, 12, 30]) (some (36, sourceBody515_34, 515, 11))

def sourceBody515_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_35 sourceBody515_3

def sourceBody515_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_36 sourceBody515_0

def sourceBody515_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_33 sourceBody515_37

def sourceBody515_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_32 sourceBody515_38

def sourceBody515_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_31 sourceBody515_39

def sourceBody515_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_30 sourceBody515_40

def sourceBody515_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_29 sourceBody515_41

def sourceBody515_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody515_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody515_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody515_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody515_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody515_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody515_0, 515, 12)) (some 472) ([2, 20, 12, 30]) (some (2, sourceBody515_47, 515, 13))

def sourceBody515_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_48 sourceBody515_3

def sourceBody515_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_49 sourceBody515_0

def sourceBody515_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_46 sourceBody515_50

def sourceBody515_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_45 sourceBody515_51

def sourceBody515_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_44 sourceBody515_52

def sourceBody515_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_43 sourceBody515_53

def sourceBody515_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_54

def sourceBody515_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_55

def sourceBody515_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody515_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody515_0, 515, 14)) (some 486) ([2]) (some (2, sourceBody515_47, 515, 15))

def sourceBody515_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_58 sourceBody515_3

def sourceBody515_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_59 sourceBody515_0

def sourceBody515_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_57 sourceBody515_60

def sourceBody515_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_61

def sourceBody515_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_62

def sourceBody515_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_56 sourceBody515_63

def sourceBody515_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody515_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody515_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_66 sourceBody515_0

def sourceBody515_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_65 sourceBody515_67

def sourceBody515_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_64 sourceBody515_68

def sourceBody515_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_42 sourceBody515_69

def sourceBody515_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_70

def sourceBody515_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_71

def sourceBody515_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_72

def sourceBody515_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_73

def sourceBody515_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_74

def sourceBody515_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_75

def sourceBody515_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_76

def sourceBody515_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_77

def sourceBody515_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_28 sourceBody515_78

def sourceBody515_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_79

def sourceBody515_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_80

def sourceBody515_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_17 sourceBody515_81

def sourceBody515_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_9 sourceBody515_82

def sourceBody515_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_83

def sourceBody515_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_84

def sourceBody515_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_85

def sourceBody515_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_86

def sourceBody515_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_87

def sourceBody515_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_88

def sourceBody515_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_89

def sourceBody515_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_90

def sourceBody515_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_5 sourceBody515_91

def sourceBody515_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_92

def sourceBody515_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_93

def sourceBody515_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_94

def sourceBody515_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_95

def sourceBody515_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_96

def sourceBody515_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_97

def sourceBody515_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_98

def sourceBody515_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody515_0 sourceBody515_99

def source515 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (515, 1, sourceBody515_100)
end InitECandidate.Proofs.WordStages
