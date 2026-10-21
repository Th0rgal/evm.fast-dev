import InitECandidate.Proofs.WordStages.Source500
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody516_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody516_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody516_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody516_0, 516, 2)) (some 471) ([]) (some (16, sourceBody516_1, 516, 3))

def sourceBody516_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody516_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_2 sourceBody516_3

def sourceBody516_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_4 sourceBody516_0

def sourceBody516_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody516_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 34, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody516_0, 516, 4)) (some 471) ([]) (some (14, sourceBody516_6, 516, 5))

def sourceBody516_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_7 sourceBody516_3

def sourceBody516_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_8 sourceBody516_0

def sourceBody516_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody516_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody516_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody516_0, 516, 6)) (some 466) ([32]) (some (32, sourceBody516_11, 516, 7))

def sourceBody516_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_12 sourceBody516_3

def sourceBody516_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_13 sourceBody516_0

def sourceBody516_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_10 sourceBody516_14

def sourceBody516_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_15

def sourceBody516_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_16

def sourceBody516_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody516_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody516_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody516_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody516_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody516_0, 516, 8)) (some 458) ([32, 8, 26, 18]) (some (32, sourceBody516_11, 516, 9))

def sourceBody516_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_22 sourceBody516_3

def sourceBody516_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_23 sourceBody516_0

def sourceBody516_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_21 sourceBody516_24

def sourceBody516_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_20 sourceBody516_25

def sourceBody516_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_19 sourceBody516_26

def sourceBody516_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_18 sourceBody516_27

def sourceBody516_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 16)

def sourceBody516_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 34)

def sourceBody516_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody516_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody516_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody516_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody516_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 8, 26, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody516_0, 516, 10)) (some 142) ([36, 2, 20, 12, 30]) (some (36, sourceBody516_34, 516, 11))

def sourceBody516_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_35 sourceBody516_3

def sourceBody516_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_36 sourceBody516_0

def sourceBody516_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_33 sourceBody516_37

def sourceBody516_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_32 sourceBody516_38

def sourceBody516_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_31 sourceBody516_39

def sourceBody516_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_30 sourceBody516_40

def sourceBody516_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_29 sourceBody516_41

def sourceBody516_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody516_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody516_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody516_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody516_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody516_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody516_0, 516, 12)) (some 472) ([2, 20, 12, 30]) (some (2, sourceBody516_47, 516, 13))

def sourceBody516_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_48 sourceBody516_3

def sourceBody516_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_49 sourceBody516_0

def sourceBody516_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_46 sourceBody516_50

def sourceBody516_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_45 sourceBody516_51

def sourceBody516_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_44 sourceBody516_52

def sourceBody516_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_43 sourceBody516_53

def sourceBody516_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_54

def sourceBody516_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_55

def sourceBody516_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody516_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody516_0, 516, 14)) (some 486) ([2]) (some (2, sourceBody516_47, 516, 15))

def sourceBody516_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_58 sourceBody516_3

def sourceBody516_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_59 sourceBody516_0

def sourceBody516_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_57 sourceBody516_60

def sourceBody516_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_61

def sourceBody516_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_62

def sourceBody516_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_56 sourceBody516_63

def sourceBody516_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody516_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody516_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_66 sourceBody516_0

def sourceBody516_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_65 sourceBody516_67

def sourceBody516_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_64 sourceBody516_68

def sourceBody516_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_42 sourceBody516_69

def sourceBody516_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_70

def sourceBody516_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_71

def sourceBody516_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_72

def sourceBody516_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_73

def sourceBody516_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_74

def sourceBody516_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_75

def sourceBody516_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_76

def sourceBody516_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_77

def sourceBody516_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_28 sourceBody516_78

def sourceBody516_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_79

def sourceBody516_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_80

def sourceBody516_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_17 sourceBody516_81

def sourceBody516_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_9 sourceBody516_82

def sourceBody516_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_83

def sourceBody516_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_84

def sourceBody516_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_85

def sourceBody516_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_86

def sourceBody516_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_87

def sourceBody516_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_88

def sourceBody516_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_89

def sourceBody516_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_90

def sourceBody516_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_5 sourceBody516_91

def sourceBody516_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_92

def sourceBody516_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_93

def sourceBody516_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_94

def sourceBody516_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_95

def sourceBody516_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_96

def sourceBody516_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_97

def sourceBody516_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_98

def sourceBody516_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody516_0 sourceBody516_99

def source516 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (516, 1, sourceBody516_100)
end InitECandidate.Proofs.WordStages
