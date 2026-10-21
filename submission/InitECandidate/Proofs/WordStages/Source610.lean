import InitECandidate.Proofs.WordStages.Source594
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody610_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody610_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody610_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 2)) (some 69) ([]) (some (22, sourceBody610_1, 610, 3))

def sourceBody610_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody610_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_2 sourceBody610_3

def sourceBody610_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_4 sourceBody610_0

def sourceBody610_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody610_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody610_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 4)) (some 68) ([16]) (some (16, sourceBody610_7, 610, 5))

def sourceBody610_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_8 sourceBody610_3

def sourceBody610_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_9 sourceBody610_0

def sourceBody610_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_6 sourceBody610_10

def sourceBody610_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 9#64])

def sourceBody610_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody610_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody610_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody610_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody610_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 6)) (some 176) ([8, 20, 14]) (some (8, sourceBody610_16, 610, 7))

def sourceBody610_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_17 sourceBody610_3

def sourceBody610_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_18 sourceBody610_0

def sourceBody610_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_15 sourceBody610_19

def sourceBody610_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_14 sourceBody610_20

def sourceBody610_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_13 sourceBody610_21

def sourceBody610_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 28])

def sourceBody610_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody610_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_24 sourceBody610_0

def sourceBody610_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_25 sourceBody610_0

def sourceBody610_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_23 sourceBody610_26

def sourceBody610_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_27

def sourceBody610_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody610_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 8)) (some 177) ([8, 20]) (some (8, sourceBody610_16, 610, 9))

def sourceBody610_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_30 sourceBody610_3

def sourceBody610_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_31 sourceBody610_0

def sourceBody610_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_29 sourceBody610_32

def sourceBody610_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_13 sourceBody610_33

def sourceBody610_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_28 sourceBody610_34

def sourceBody610_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_35 sourceBody610_28

def sourceBody610_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.var 16,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 9#64]])

def sourceBody610_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody610_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody610_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 10)) (some 180) ([14]) (some (14, sourceBody610_39, 610, 11))

def sourceBody610_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_40 sourceBody610_3

def sourceBody610_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_41 sourceBody610_0

def sourceBody610_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_38 sourceBody610_42

def sourceBody610_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 9#64],
      Flapjack.WordLangExpHOL.var 20])

def sourceBody610_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody610_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody610_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 12)) (some 178) ([26, 12]) (some (26, sourceBody610_46, 610, 13))

def sourceBody610_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_47 sourceBody610_3

def sourceBody610_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_48 sourceBody610_0

def sourceBody610_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_45 sourceBody610_49

def sourceBody610_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_44 sourceBody610_50

def sourceBody610_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_51

def sourceBody610_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_52

def sourceBody610_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody610_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 14)) (some 68) ([26]) (some (26, sourceBody610_46, 610, 15))

def sourceBody610_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_55 sourceBody610_3

def sourceBody610_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_56 sourceBody610_0

def sourceBody610_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_54 sourceBody610_57

def sourceBody610_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 9#64],
      Flapjack.WordLangExpHOL.var 20])

def sourceBody610_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 20])

def sourceBody610_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody610_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody610_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 16)) (some 158) ([12, 24, 18]) (some (12, sourceBody610_62, 610, 17))

def sourceBody610_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_63 sourceBody610_3

def sourceBody610_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_64 sourceBody610_0

def sourceBody610_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_61 sourceBody610_65

def sourceBody610_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_60 sourceBody610_66

def sourceBody610_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_59 sourceBody610_67

def sourceBody610_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_68

def sourceBody610_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_69

def sourceBody610_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody610_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 12#64])

def sourceBody610_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody610_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody610_0, 610, 18)) (some 77) ([12, 24, 18]) (some (12, sourceBody610_62, 610, 19))

def sourceBody610_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_74 sourceBody610_3

def sourceBody610_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_75 sourceBody610_0

def sourceBody610_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_73 sourceBody610_76

def sourceBody610_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_72 sourceBody610_77

def sourceBody610_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_71 sourceBody610_78

def sourceBody610_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_79

def sourceBody610_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_80

def sourceBody610_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_70 sourceBody610_81

def sourceBody610_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody610_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody610_0, 610, 20)) (some 70) ([12]) (some (12, sourceBody610_62, 610, 21))

def sourceBody610_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_84 sourceBody610_3

def sourceBody610_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_85 sourceBody610_0

def sourceBody610_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_83 sourceBody610_86

def sourceBody610_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_87

def sourceBody610_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_88

def sourceBody610_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_82 sourceBody610_89

def sourceBody610_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody610_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody610_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_92 sourceBody610_0

def sourceBody610_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_91 sourceBody610_93

def sourceBody610_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_90 sourceBody610_94

def sourceBody610_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_58 sourceBody610_95

def sourceBody610_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_96

def sourceBody610_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_97

def sourceBody610_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_53 sourceBody610_98

def sourceBody610_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_43 sourceBody610_99

def sourceBody610_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_100

def sourceBody610_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_101

def sourceBody610_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_37 sourceBody610_102

def sourceBody610_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_103

def sourceBody610_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_36 sourceBody610_104

def sourceBody610_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_22 sourceBody610_105

def sourceBody610_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_106

def sourceBody610_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_107

def sourceBody610_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_12 sourceBody610_108

def sourceBody610_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_109

def sourceBody610_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_11 sourceBody610_110

def sourceBody610_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_111

def sourceBody610_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_112

def sourceBody610_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_5 sourceBody610_113

def sourceBody610_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_114

def sourceBody610_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody610_0 sourceBody610_115

def source610 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (610, 4, sourceBody610_116)
end InitECandidate.Proofs.WordStages
