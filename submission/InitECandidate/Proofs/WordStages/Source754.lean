import InitECandidate.Proofs.WordStages.Source738
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody754_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody754_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody754_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 2)) (some 69) ([]) (some (22, sourceBody754_1, 754, 3))

def sourceBody754_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody754_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_2 sourceBody754_3

def sourceBody754_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_4 sourceBody754_0

def sourceBody754_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1440#64)

def sourceBody754_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody754_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 4)) (some 68) ([16]) (some (16, sourceBody754_7, 754, 5))

def sourceBody754_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_8 sourceBody754_3

def sourceBody754_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_9 sourceBody754_0

def sourceBody754_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_6 sourceBody754_10

def sourceBody754_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody754_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody754_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody754_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 864#64])

def sourceBody754_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 1152#64])

def sourceBody754_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody754_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody754_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody754_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody754_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 6)) (some 748) ([12, 24, 18]) (some (12, sourceBody754_20, 754, 7))

def sourceBody754_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_21 sourceBody754_3

def sourceBody754_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_22 sourceBody754_0

def sourceBody754_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_19 sourceBody754_23

def sourceBody754_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_18 sourceBody754_24

def sourceBody754_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_17 sourceBody754_25

def sourceBody754_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_26

def sourceBody754_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_27

def sourceBody754_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody754_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody754_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody754_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 8)) (some 748) ([12, 24, 18]) (some (12, sourceBody754_20, 754, 9))

def sourceBody754_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_32 sourceBody754_3

def sourceBody754_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_33 sourceBody754_0

def sourceBody754_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_31 sourceBody754_34

def sourceBody754_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_30 sourceBody754_35

def sourceBody754_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_29 sourceBody754_36

def sourceBody754_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_37

def sourceBody754_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_38

def sourceBody754_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_28 sourceBody754_39

def sourceBody754_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody754_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody754_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 10)) (some 745) ([12, 24, 18]) (some (12, sourceBody754_20, 754, 11))

def sourceBody754_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_43 sourceBody754_3

def sourceBody754_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_44 sourceBody754_0

def sourceBody754_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_42 sourceBody754_45

def sourceBody754_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_18 sourceBody754_46

def sourceBody754_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_41 sourceBody754_47

def sourceBody754_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_48

def sourceBody754_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_49

def sourceBody754_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_40 sourceBody754_50

def sourceBody754_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody754_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody754_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 12)) (some 745) ([12, 24, 18]) (some (12, sourceBody754_20, 754, 13))

def sourceBody754_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_54 sourceBody754_3

def sourceBody754_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_55 sourceBody754_0

def sourceBody754_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_31 sourceBody754_56

def sourceBody754_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_53 sourceBody754_57

def sourceBody754_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_52 sourceBody754_58

def sourceBody754_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_59

def sourceBody754_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_60

def sourceBody754_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_51 sourceBody754_61

def sourceBody754_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody754_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody754_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody754_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 14)) (some 748) ([12, 24, 18]) (some (12, sourceBody754_20, 754, 15))

def sourceBody754_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_66 sourceBody754_3

def sourceBody754_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_67 sourceBody754_0

def sourceBody754_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_65 sourceBody754_68

def sourceBody754_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_64 sourceBody754_69

def sourceBody754_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_63 sourceBody754_70

def sourceBody754_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_71

def sourceBody754_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_72

def sourceBody754_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_62 sourceBody754_73

def sourceBody754_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody754_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody754_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 16)) (some 746) ([12, 24, 18]) (some (12, sourceBody754_20, 754, 17))

def sourceBody754_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_77 sourceBody754_3

def sourceBody754_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_78 sourceBody754_0

def sourceBody754_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_76 sourceBody754_79

def sourceBody754_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_75 sourceBody754_80

def sourceBody754_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_63 sourceBody754_81

def sourceBody754_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_82

def sourceBody754_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_83

def sourceBody754_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_74 sourceBody754_84

def sourceBody754_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody754_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody754_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 18)) (some 746) ([12, 24, 18]) (some (12, sourceBody754_20, 754, 19))

def sourceBody754_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_88 sourceBody754_3

def sourceBody754_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_89 sourceBody754_0

def sourceBody754_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_87 sourceBody754_90

def sourceBody754_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_75 sourceBody754_91

def sourceBody754_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_86 sourceBody754_92

def sourceBody754_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_93

def sourceBody754_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_94

def sourceBody754_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_85 sourceBody754_95

def sourceBody754_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody754_98 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 20)) (some 749) ([12, 24]) (some (12, sourceBody754_20, 754, 21))

def sourceBody754_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_98 sourceBody754_3

def sourceBody754_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_99 sourceBody754_0

def sourceBody754_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_97 sourceBody754_100

def sourceBody754_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_29 sourceBody754_101

def sourceBody754_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_102

def sourceBody754_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_103

def sourceBody754_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_96 sourceBody754_104

def sourceBody754_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody754_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody754_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody754_0, 754, 22)) (some 745) ([12, 24, 18]) (some (12, sourceBody754_20, 754, 23))

def sourceBody754_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_108 sourceBody754_3

def sourceBody754_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_109 sourceBody754_0

def sourceBody754_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_87 sourceBody754_110

def sourceBody754_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_107 sourceBody754_111

def sourceBody754_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_106 sourceBody754_112

def sourceBody754_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_113

def sourceBody754_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_114

def sourceBody754_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_105 sourceBody754_115

def sourceBody754_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody754_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody754_0, 754, 24)) (some 70) ([12]) (some (12, sourceBody754_20, 754, 25))

def sourceBody754_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_118 sourceBody754_3

def sourceBody754_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_119 sourceBody754_0

def sourceBody754_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_117 sourceBody754_120

def sourceBody754_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_121

def sourceBody754_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_122

def sourceBody754_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_116 sourceBody754_123

def sourceBody754_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody754_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody754_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_126 sourceBody754_0

def sourceBody754_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_125 sourceBody754_127

def sourceBody754_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_124 sourceBody754_128

def sourceBody754_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_16 sourceBody754_129

def sourceBody754_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_130

def sourceBody754_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_15 sourceBody754_131

def sourceBody754_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_132

def sourceBody754_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_14 sourceBody754_133

def sourceBody754_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_134

def sourceBody754_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_13 sourceBody754_135

def sourceBody754_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_136

def sourceBody754_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_12 sourceBody754_137

def sourceBody754_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_138

def sourceBody754_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_11 sourceBody754_139

def sourceBody754_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_140

def sourceBody754_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_141

def sourceBody754_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_5 sourceBody754_142

def sourceBody754_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_143

def sourceBody754_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody754_0 sourceBody754_144

def source754 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (754, 4, sourceBody754_145)
end InitECandidate.Proofs.WordStages
