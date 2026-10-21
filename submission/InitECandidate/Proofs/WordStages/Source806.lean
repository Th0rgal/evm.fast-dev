import InitECandidate.Proofs.WordStages.Source790
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody806_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody806_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody806_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody806_0, 806, 2)) (some 69) ([]) (some (8, sourceBody806_1, 806, 3))

def sourceBody806_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody806_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_2 sourceBody806_3

def sourceBody806_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_4 sourceBody806_0

def sourceBody806_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody806_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody806_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody806_0, 806, 4)) (some 68) ([16]) (some (16, sourceBody806_7, 806, 5))

def sourceBody806_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_8 sourceBody806_3

def sourceBody806_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_9 sourceBody806_0

def sourceBody806_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_6 sourceBody806_10

def sourceBody806_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody806_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody806_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody806_0, 806, 6)) (some 68) ([12]) (some (12, sourceBody806_13, 806, 7))

def sourceBody806_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_14 sourceBody806_3

def sourceBody806_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_15 sourceBody806_0

def sourceBody806_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_12 sourceBody806_16

def sourceBody806_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody806_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody806_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody806_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody806_0, 806, 8)) (some 771) ([20, 6]) (some (20, sourceBody806_20, 806, 9))

def sourceBody806_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_21 sourceBody806_3

def sourceBody806_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_22 sourceBody806_0

def sourceBody806_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_19 sourceBody806_23

def sourceBody806_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_18 sourceBody806_24

def sourceBody806_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody806_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody806_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody806_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody806_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 14) sourceBody806_28 sourceBody806_29

def sourceBody806_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_30 sourceBody806_3

def sourceBody806_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody806_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody806_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody806_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody806_0, 806, 10)) (some 771) ([20, 6]) (some (20, sourceBody806_20, 806, 11))

def sourceBody806_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_35 sourceBody806_3

def sourceBody806_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_36 sourceBody806_0

def sourceBody806_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_34 sourceBody806_37

def sourceBody806_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_33 sourceBody806_38

def sourceBody806_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody806_39 sourceBody806_0

def sourceBody806_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_40 sourceBody806_3

def sourceBody806_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_41 sourceBody806_0

def sourceBody806_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_32 sourceBody806_42

def sourceBody806_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_31 sourceBody806_43

def sourceBody806_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_27 sourceBody806_44

def sourceBody806_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_26 sourceBody806_45

def sourceBody806_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody806_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody806_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody806_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody806_0, 806, 12)) (some 70) ([6]) (some (6, sourceBody806_49, 806, 13))

def sourceBody806_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_50 sourceBody806_3

def sourceBody806_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_51 sourceBody806_0

def sourceBody806_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_48 sourceBody806_52

def sourceBody806_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_53

def sourceBody806_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_54

def sourceBody806_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody806_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody806_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_57 sourceBody806_0

def sourceBody806_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_56 sourceBody806_58

def sourceBody806_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_55 sourceBody806_59

def sourceBody806_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody806_60 sourceBody806_0

def sourceBody806_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_61 sourceBody806_3

def sourceBody806_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_62 sourceBody806_0

def sourceBody806_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_32 sourceBody806_63

def sourceBody806_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_31 sourceBody806_64

def sourceBody806_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_47 sourceBody806_65

def sourceBody806_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_26 sourceBody806_66

def sourceBody806_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_46 sourceBody806_67

def sourceBody806_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody806_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody806_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody806_0, 806, 14)) (some 767) ([6, 14, 10]) (some (6, sourceBody806_49, 806, 15))

def sourceBody806_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_71 sourceBody806_3

def sourceBody806_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_72 sourceBody806_0

def sourceBody806_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_70 sourceBody806_73

def sourceBody806_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_69 sourceBody806_74

def sourceBody806_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_19 sourceBody806_75

def sourceBody806_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_76

def sourceBody806_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_77

def sourceBody806_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_68 sourceBody806_78

def sourceBody806_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody806_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody806_0, 806, 16)) (some 772) ([6, 14]) (some (6, sourceBody806_49, 806, 17))

def sourceBody806_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_81 sourceBody806_3

def sourceBody806_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_82 sourceBody806_0

def sourceBody806_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_80 sourceBody806_83

def sourceBody806_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_19 sourceBody806_84

def sourceBody806_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_85

def sourceBody806_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_86

def sourceBody806_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_79 sourceBody806_87

def sourceBody806_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody806_0, 806, 18)) (some 70) ([6]) (some (6, sourceBody806_49, 806, 19))

def sourceBody806_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_89 sourceBody806_3

def sourceBody806_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_90 sourceBody806_0

def sourceBody806_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_48 sourceBody806_91

def sourceBody806_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_92

def sourceBody806_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_93

def sourceBody806_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_88 sourceBody806_94

def sourceBody806_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody806_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_96 sourceBody806_58

def sourceBody806_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_95 sourceBody806_97

def sourceBody806_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_25 sourceBody806_98

def sourceBody806_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_99

def sourceBody806_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_100

def sourceBody806_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_17 sourceBody806_101

def sourceBody806_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_102

def sourceBody806_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_103

def sourceBody806_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_11 sourceBody806_104

def sourceBody806_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_105

def sourceBody806_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_106

def sourceBody806_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_5 sourceBody806_107

def sourceBody806_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_108

def sourceBody806_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody806_0 sourceBody806_109

def source806 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (806, 3, sourceBody806_110)
end InitECandidate.Proofs.WordStages
