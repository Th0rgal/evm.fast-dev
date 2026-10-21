import InitECandidate.Proofs.WordStages.Source484
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody500_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody500_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody500_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 44, 8, 36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody500_0, 500, 2)) (some 471) ([]) (some (24, sourceBody500_1, 500, 3))

def sourceBody500_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody500_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_2 sourceBody500_3

def sourceBody500_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_4 sourceBody500_0

def sourceBody500_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody500_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 52, 4, 32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody500_0, 500, 4)) (some 471) ([]) (some (20, sourceBody500_6, 500, 5))

def sourceBody500_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_7 sourceBody500_3

def sourceBody500_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_8 sourceBody500_0

def sourceBody500_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody500_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 48, 12, 40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody500_0, 500, 6)) (some 471) ([]) (some (28, sourceBody500_10, 500, 7))

def sourceBody500_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_11 sourceBody500_3

def sourceBody500_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_12 sourceBody500_0

def sourceBody500_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody500_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody500_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody500_0, 500, 8)) (some 466) ([56]) (some (56, sourceBody500_15, 500, 9))

def sourceBody500_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_16 sourceBody500_3

def sourceBody500_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_17 sourceBody500_0

def sourceBody500_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_14 sourceBody500_18

def sourceBody500_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_19

def sourceBody500_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_20

def sourceBody500_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody500_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 44)

def sourceBody500_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody500_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 36)

def sourceBody500_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 24)

def sourceBody500_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 52)

def sourceBody500_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody500_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody500_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody500_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 48)

def sourceBody500_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody500_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody500_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody500_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 56, 2, 30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody500_0, 500, 10)) (some 135) ([18, 46, 10, 38, 26, 54, 6, 34, 22, 50, 14, 42]) (some (18, sourceBody500_34, 500, 11))

def sourceBody500_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_35 sourceBody500_3

def sourceBody500_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_36 sourceBody500_0

def sourceBody500_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_33 sourceBody500_37

def sourceBody500_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_32 sourceBody500_38

def sourceBody500_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_31 sourceBody500_39

def sourceBody500_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_30 sourceBody500_40

def sourceBody500_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_29 sourceBody500_41

def sourceBody500_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_28 sourceBody500_42

def sourceBody500_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_27 sourceBody500_43

def sourceBody500_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_26 sourceBody500_44

def sourceBody500_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_25 sourceBody500_45

def sourceBody500_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_24 sourceBody500_46

def sourceBody500_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_23 sourceBody500_47

def sourceBody500_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_22 sourceBody500_48

def sourceBody500_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 28)

def sourceBody500_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 56)

def sourceBody500_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 2)

def sourceBody500_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody500_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody500_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody500_0, 500, 12)) (some 472) ([46, 10, 38, 26]) (some (46, sourceBody500_54, 500, 13))

def sourceBody500_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_55 sourceBody500_3

def sourceBody500_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_56 sourceBody500_0

def sourceBody500_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_53 sourceBody500_57

def sourceBody500_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_52 sourceBody500_58

def sourceBody500_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_51 sourceBody500_59

def sourceBody500_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_50 sourceBody500_60

def sourceBody500_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_61

def sourceBody500_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_62

def sourceBody500_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody500_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody500_0, 500, 14)) (some 486) ([46]) (some (46, sourceBody500_54, 500, 15))

def sourceBody500_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_65 sourceBody500_3

def sourceBody500_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_66 sourceBody500_0

def sourceBody500_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_64 sourceBody500_67

def sourceBody500_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_68

def sourceBody500_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_69

def sourceBody500_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_63 sourceBody500_70

def sourceBody500_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody500_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody500_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_73 sourceBody500_0

def sourceBody500_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_72 sourceBody500_74

def sourceBody500_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_71 sourceBody500_75

def sourceBody500_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_49 sourceBody500_76

def sourceBody500_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_77

def sourceBody500_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_78

def sourceBody500_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_79

def sourceBody500_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_80

def sourceBody500_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_81

def sourceBody500_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_82

def sourceBody500_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_83

def sourceBody500_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_84

def sourceBody500_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_21 sourceBody500_85

def sourceBody500_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_13 sourceBody500_86

def sourceBody500_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_87

def sourceBody500_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_88

def sourceBody500_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_89

def sourceBody500_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_90

def sourceBody500_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_91

def sourceBody500_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_92

def sourceBody500_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_93

def sourceBody500_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_94

def sourceBody500_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_9 sourceBody500_95

def sourceBody500_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_96

def sourceBody500_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_97

def sourceBody500_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_98

def sourceBody500_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_99

def sourceBody500_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_100

def sourceBody500_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_101

def sourceBody500_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_102

def sourceBody500_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_103

def sourceBody500_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_5 sourceBody500_104

def sourceBody500_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_105

def sourceBody500_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_106

def sourceBody500_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_107

def sourceBody500_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_108

def sourceBody500_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_109

def sourceBody500_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_110

def sourceBody500_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_111

def sourceBody500_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody500_0 sourceBody500_112

def source500 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (500, 1, sourceBody500_113)
end InitECandidate.Proofs.WordStages
