import InitECandidate.Proofs.WordStages.Source498
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody514_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody514_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody514_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 24, 6, 20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody514_0, 514, 2)) (some 471) ([]) (some (14, sourceBody514_1, 514, 3))

def sourceBody514_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody514_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_2 sourceBody514_3

def sourceBody514_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_4 sourceBody514_0

def sourceBody514_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody514_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 28, 4, 18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody514_0, 514, 4)) (some 471) ([]) (some (12, sourceBody514_6, 514, 5))

def sourceBody514_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_7 sourceBody514_3

def sourceBody514_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_8 sourceBody514_0

def sourceBody514_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody514_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody514_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody514_0, 514, 6)) (some 466) ([26]) (some (26, sourceBody514_11, 514, 7))

def sourceBody514_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_12 sourceBody514_3

def sourceBody514_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_13 sourceBody514_0

def sourceBody514_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_10 sourceBody514_14

def sourceBody514_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_15

def sourceBody514_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_16

def sourceBody514_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody514_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 24)

def sourceBody514_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody514_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody514_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody514_0, 514, 8)) (some 458) ([26, 8, 22, 16]) (some (26, sourceBody514_11, 514, 9))

def sourceBody514_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_22 sourceBody514_3

def sourceBody514_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_23 sourceBody514_0

def sourceBody514_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_21 sourceBody514_24

def sourceBody514_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_20 sourceBody514_25

def sourceBody514_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_19 sourceBody514_26

def sourceBody514_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_18 sourceBody514_27

def sourceBody514_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody514_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody514_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody514_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody514_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 18)

def sourceBody514_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody514_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody514_0, 514, 10)) (some 145) ([8, 22, 16, 30, 2]) (some (8, sourceBody514_34, 514, 11))

def sourceBody514_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_35 sourceBody514_3

def sourceBody514_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_36 sourceBody514_0

def sourceBody514_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_33 sourceBody514_37

def sourceBody514_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_32 sourceBody514_38

def sourceBody514_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_31 sourceBody514_39

def sourceBody514_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_30 sourceBody514_40

def sourceBody514_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_29 sourceBody514_41

def sourceBody514_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody514_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody514_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody514_0, 514, 12)) (some 473) ([22]) (some (22, sourceBody514_44, 514, 13))

def sourceBody514_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_45 sourceBody514_3

def sourceBody514_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_46 sourceBody514_0

def sourceBody514_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_43 sourceBody514_47

def sourceBody514_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_48

def sourceBody514_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_49

def sourceBody514_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody514_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody514_0, 514, 14)) (some 486) ([22]) (some (22, sourceBody514_44, 514, 15))

def sourceBody514_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_52 sourceBody514_3

def sourceBody514_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_53 sourceBody514_0

def sourceBody514_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_51 sourceBody514_54

def sourceBody514_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_55

def sourceBody514_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_56

def sourceBody514_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_50 sourceBody514_57

def sourceBody514_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody514_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody514_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_60 sourceBody514_0

def sourceBody514_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_59 sourceBody514_61

def sourceBody514_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_58 sourceBody514_62

def sourceBody514_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_42 sourceBody514_63

def sourceBody514_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_64

def sourceBody514_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_65

def sourceBody514_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_28 sourceBody514_66

def sourceBody514_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_67

def sourceBody514_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_68

def sourceBody514_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_17 sourceBody514_69

def sourceBody514_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_9 sourceBody514_70

def sourceBody514_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_71

def sourceBody514_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_72

def sourceBody514_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_73

def sourceBody514_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_74

def sourceBody514_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_75

def sourceBody514_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_76

def sourceBody514_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_77

def sourceBody514_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_78

def sourceBody514_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_5 sourceBody514_79

def sourceBody514_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_80

def sourceBody514_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_81

def sourceBody514_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_82

def sourceBody514_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_83

def sourceBody514_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_84

def sourceBody514_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_85

def sourceBody514_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_86

def sourceBody514_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody514_0 sourceBody514_87

def source514 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (514, 1, sourceBody514_88)
end InitECandidate.Proofs.WordStages
