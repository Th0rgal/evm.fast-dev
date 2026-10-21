import InitECandidate.Proofs.WordStages.Source792
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody808_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody808_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody808_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody808_0, 808, 2)) (some 69) ([]) (some (8, sourceBody808_1, 808, 3))

def sourceBody808_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody808_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_2 sourceBody808_3

def sourceBody808_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_4 sourceBody808_0

def sourceBody808_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody808_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody808_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody808_0, 808, 4)) (some 68) ([16]) (some (16, sourceBody808_7, 808, 5))

def sourceBody808_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_8 sourceBody808_3

def sourceBody808_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_9 sourceBody808_0

def sourceBody808_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_6 sourceBody808_10

def sourceBody808_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody808_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody808_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody808_0, 808, 6)) (some 68) ([12]) (some (12, sourceBody808_13, 808, 7))

def sourceBody808_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_14 sourceBody808_3

def sourceBody808_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_15 sourceBody808_0

def sourceBody808_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_12 sourceBody808_16

def sourceBody808_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody808_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody808_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody808_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody808_0, 808, 8)) (some 783) ([20, 6]) (some (20, sourceBody808_20, 808, 9))

def sourceBody808_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_21 sourceBody808_3

def sourceBody808_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_22 sourceBody808_0

def sourceBody808_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_19 sourceBody808_23

def sourceBody808_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_18 sourceBody808_24

def sourceBody808_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody808_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody808_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody808_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody808_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 14) sourceBody808_28 sourceBody808_29

def sourceBody808_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_30 sourceBody808_3

def sourceBody808_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody808_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 256#64])

def sourceBody808_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody808_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody808_0, 808, 10)) (some 783) ([20, 6]) (some (20, sourceBody808_20, 808, 11))

def sourceBody808_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_35 sourceBody808_3

def sourceBody808_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_36 sourceBody808_0

def sourceBody808_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_34 sourceBody808_37

def sourceBody808_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_33 sourceBody808_38

def sourceBody808_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody808_39 sourceBody808_0

def sourceBody808_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_40 sourceBody808_3

def sourceBody808_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_41 sourceBody808_0

def sourceBody808_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_32 sourceBody808_42

def sourceBody808_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_31 sourceBody808_43

def sourceBody808_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_27 sourceBody808_44

def sourceBody808_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_26 sourceBody808_45

def sourceBody808_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody808_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody808_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody808_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody808_0, 808, 12)) (some 70) ([6]) (some (6, sourceBody808_49, 808, 13))

def sourceBody808_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_50 sourceBody808_3

def sourceBody808_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_51 sourceBody808_0

def sourceBody808_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_48 sourceBody808_52

def sourceBody808_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_53

def sourceBody808_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_54

def sourceBody808_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody808_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody808_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_57 sourceBody808_0

def sourceBody808_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_56 sourceBody808_58

def sourceBody808_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_55 sourceBody808_59

def sourceBody808_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody808_60 sourceBody808_0

def sourceBody808_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_61 sourceBody808_3

def sourceBody808_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_62 sourceBody808_0

def sourceBody808_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_32 sourceBody808_63

def sourceBody808_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_31 sourceBody808_64

def sourceBody808_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_47 sourceBody808_65

def sourceBody808_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_26 sourceBody808_66

def sourceBody808_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_46 sourceBody808_67

def sourceBody808_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody808_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody808_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody808_0, 808, 14)) (some 779) ([6, 14, 10]) (some (6, sourceBody808_49, 808, 15))

def sourceBody808_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_71 sourceBody808_3

def sourceBody808_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_72 sourceBody808_0

def sourceBody808_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_70 sourceBody808_73

def sourceBody808_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_69 sourceBody808_74

def sourceBody808_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_19 sourceBody808_75

def sourceBody808_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_76

def sourceBody808_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_77

def sourceBody808_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_68 sourceBody808_78

def sourceBody808_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody808_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody808_0, 808, 16)) (some 784) ([6, 14]) (some (6, sourceBody808_49, 808, 17))

def sourceBody808_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_81 sourceBody808_3

def sourceBody808_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_82 sourceBody808_0

def sourceBody808_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_80 sourceBody808_83

def sourceBody808_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_19 sourceBody808_84

def sourceBody808_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_85

def sourceBody808_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_86

def sourceBody808_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_79 sourceBody808_87

def sourceBody808_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody808_0, 808, 18)) (some 70) ([6]) (some (6, sourceBody808_49, 808, 19))

def sourceBody808_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_89 sourceBody808_3

def sourceBody808_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_90 sourceBody808_0

def sourceBody808_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_48 sourceBody808_91

def sourceBody808_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_92

def sourceBody808_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_93

def sourceBody808_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_88 sourceBody808_94

def sourceBody808_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody808_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_96 sourceBody808_58

def sourceBody808_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_95 sourceBody808_97

def sourceBody808_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_25 sourceBody808_98

def sourceBody808_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_99

def sourceBody808_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_100

def sourceBody808_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_17 sourceBody808_101

def sourceBody808_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_102

def sourceBody808_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_103

def sourceBody808_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_11 sourceBody808_104

def sourceBody808_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_105

def sourceBody808_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_106

def sourceBody808_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_5 sourceBody808_107

def sourceBody808_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_108

def sourceBody808_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody808_0 sourceBody808_109

def source808 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (808, 3, sourceBody808_110)
end InitECandidate.Proofs.WordStages
