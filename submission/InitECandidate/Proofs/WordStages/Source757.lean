import InitECandidate.Proofs.WordStages.Source741
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody757_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody757_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody757_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 2)) (some 69) ([]) (some (8, sourceBody757_1, 757, 3))

def sourceBody757_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody757_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_2 sourceBody757_3

def sourceBody757_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_4 sourceBody757_0

def sourceBody757_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 864#64)

def sourceBody757_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody757_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 4)) (some 68) ([16]) (some (16, sourceBody757_7, 757, 5))

def sourceBody757_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_8 sourceBody757_3

def sourceBody757_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_9 sourceBody757_0

def sourceBody757_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_6 sourceBody757_10

def sourceBody757_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody757_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody757_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody757_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody757_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody757_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody757_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody757_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 6)) (some 748) ([14, 10, 20]) (some (14, sourceBody757_18, 757, 7))

def sourceBody757_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_19 sourceBody757_3

def sourceBody757_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_20 sourceBody757_0

def sourceBody757_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_17 sourceBody757_21

def sourceBody757_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_16 sourceBody757_22

def sourceBody757_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_15 sourceBody757_23

def sourceBody757_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_24

def sourceBody757_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_25

def sourceBody757_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody757_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody757_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody757_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 8)) (some 748) ([14, 10, 20]) (some (14, sourceBody757_18, 757, 9))

def sourceBody757_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_30 sourceBody757_3

def sourceBody757_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_31 sourceBody757_0

def sourceBody757_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_29 sourceBody757_32

def sourceBody757_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_28 sourceBody757_33

def sourceBody757_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_27 sourceBody757_34

def sourceBody757_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_35

def sourceBody757_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_36

def sourceBody757_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_26 sourceBody757_37

def sourceBody757_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody757_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 10)) (some 749) ([14, 10]) (some (14, sourceBody757_18, 757, 11))

def sourceBody757_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_40 sourceBody757_3

def sourceBody757_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_41 sourceBody757_0

def sourceBody757_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_39 sourceBody757_42

def sourceBody757_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_27 sourceBody757_43

def sourceBody757_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_44

def sourceBody757_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_45

def sourceBody757_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_38 sourceBody757_46

def sourceBody757_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody757_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody757_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody757_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 12)) (some 746) ([14, 10, 20]) (some (14, sourceBody757_18, 757, 13))

def sourceBody757_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_51 sourceBody757_3

def sourceBody757_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_52 sourceBody757_0

def sourceBody757_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_50 sourceBody757_53

def sourceBody757_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_49 sourceBody757_54

def sourceBody757_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_48 sourceBody757_55

def sourceBody757_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_56

def sourceBody757_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_57

def sourceBody757_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_47 sourceBody757_58

def sourceBody757_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody757_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 14)) (some 750) ([14, 10]) (some (14, sourceBody757_18, 757, 15))

def sourceBody757_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_61 sourceBody757_3

def sourceBody757_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_62 sourceBody757_0

def sourceBody757_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_60 sourceBody757_63

def sourceBody757_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_48 sourceBody757_64

def sourceBody757_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_65

def sourceBody757_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_66

def sourceBody757_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_59 sourceBody757_67

def sourceBody757_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody757_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody757_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 16)) (some 748) ([14, 10, 20]) (some (14, sourceBody757_18, 757, 17))

def sourceBody757_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_71 sourceBody757_3

def sourceBody757_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_72 sourceBody757_0

def sourceBody757_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_70 sourceBody757_73

def sourceBody757_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_16 sourceBody757_74

def sourceBody757_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_69 sourceBody757_75

def sourceBody757_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_76

def sourceBody757_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_77

def sourceBody757_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_68 sourceBody757_78

def sourceBody757_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody757_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 18)) (some 748) ([14, 10, 20]) (some (14, sourceBody757_18, 757, 19))

def sourceBody757_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_81 sourceBody757_3

def sourceBody757_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_82 sourceBody757_0

def sourceBody757_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_70 sourceBody757_83

def sourceBody757_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_28 sourceBody757_84

def sourceBody757_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_80 sourceBody757_85

def sourceBody757_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_86

def sourceBody757_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_87

def sourceBody757_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_79 sourceBody757_88

def sourceBody757_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody757_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody757_0, 757, 20)) (some 747) ([14, 10]) (some (14, sourceBody757_18, 757, 21))

def sourceBody757_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_91 sourceBody757_3

def sourceBody757_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_92 sourceBody757_0

def sourceBody757_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_90 sourceBody757_93

def sourceBody757_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_80 sourceBody757_94

def sourceBody757_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_95

def sourceBody757_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_96

def sourceBody757_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_89 sourceBody757_97

def sourceBody757_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody757_100 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody757_0, 757, 22)) (some 70) ([14]) (some (14, sourceBody757_18, 757, 23))

def sourceBody757_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_100 sourceBody757_3

def sourceBody757_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_101 sourceBody757_0

def sourceBody757_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_99 sourceBody757_102

def sourceBody757_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_103

def sourceBody757_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_104

def sourceBody757_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_98 sourceBody757_105

def sourceBody757_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody757_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody757_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_108 sourceBody757_0

def sourceBody757_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_107 sourceBody757_109

def sourceBody757_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_106 sourceBody757_110

def sourceBody757_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_14 sourceBody757_111

def sourceBody757_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_112

def sourceBody757_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_13 sourceBody757_113

def sourceBody757_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_114

def sourceBody757_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_12 sourceBody757_115

def sourceBody757_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_116

def sourceBody757_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_11 sourceBody757_117

def sourceBody757_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_118

def sourceBody757_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_119

def sourceBody757_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_5 sourceBody757_120

def sourceBody757_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_121

def sourceBody757_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody757_0 sourceBody757_122

def source757 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (757, 3, sourceBody757_123)
end InitECandidate.Proofs.WordStages
