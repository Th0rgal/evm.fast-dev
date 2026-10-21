import InitECandidate.Proofs.WordStages.Source732
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody748_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody748_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody748_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 2)) (some 69) ([]) (some (18, sourceBody748_1, 748, 3))

def sourceBody748_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody748_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_2 sourceBody748_3

def sourceBody748_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_4 sourceBody748_0

def sourceBody748_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 960#64)

def sourceBody748_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody748_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 4)) (some 68) ([14]) (some (14, sourceBody748_7, 748, 5))

def sourceBody748_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_8 sourceBody748_3

def sourceBody748_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_9 sourceBody748_0

def sourceBody748_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_6 sourceBody748_10

def sourceBody748_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody748_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody748_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody748_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody748_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 6)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 7))

def sourceBody748_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_16 sourceBody748_3

def sourceBody748_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_17 sourceBody748_0

def sourceBody748_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_14 sourceBody748_18

def sourceBody748_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_13 sourceBody748_19

def sourceBody748_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_12 sourceBody748_20

def sourceBody748_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_21

def sourceBody748_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_22

def sourceBody748_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody748_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody748_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 8)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 9))

def sourceBody748_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_26 sourceBody748_3

def sourceBody748_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_27 sourceBody748_0

def sourceBody748_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_25 sourceBody748_28

def sourceBody748_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_13 sourceBody748_29

def sourceBody748_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_24 sourceBody748_30

def sourceBody748_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_31

def sourceBody748_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_32

def sourceBody748_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_23 sourceBody748_33

def sourceBody748_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody748_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody748_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 10)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 11))

def sourceBody748_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_37 sourceBody748_3

def sourceBody748_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_38 sourceBody748_0

def sourceBody748_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_36 sourceBody748_39

def sourceBody748_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_13 sourceBody748_40

def sourceBody748_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_35 sourceBody748_41

def sourceBody748_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_42

def sourceBody748_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_43

def sourceBody748_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_34 sourceBody748_44

def sourceBody748_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody748_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody748_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 12)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 13))

def sourceBody748_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_48 sourceBody748_3

def sourceBody748_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_49 sourceBody748_0

def sourceBody748_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_14 sourceBody748_50

def sourceBody748_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_47 sourceBody748_51

def sourceBody748_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_46 sourceBody748_52

def sourceBody748_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_53

def sourceBody748_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_54

def sourceBody748_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_45 sourceBody748_55

def sourceBody748_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody748_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 14)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 15))

def sourceBody748_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_58 sourceBody748_3

def sourceBody748_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_59 sourceBody748_0

def sourceBody748_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_25 sourceBody748_60

def sourceBody748_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_47 sourceBody748_61

def sourceBody748_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_57 sourceBody748_62

def sourceBody748_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_63

def sourceBody748_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_64

def sourceBody748_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_56 sourceBody748_65

def sourceBody748_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody748_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 16)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 17))

def sourceBody748_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_68 sourceBody748_3

def sourceBody748_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_69 sourceBody748_0

def sourceBody748_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_36 sourceBody748_70

def sourceBody748_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_47 sourceBody748_71

def sourceBody748_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_67 sourceBody748_72

def sourceBody748_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_73

def sourceBody748_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_74

def sourceBody748_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_66 sourceBody748_75

def sourceBody748_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody748_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody748_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 18)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 19))

def sourceBody748_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_79 sourceBody748_3

def sourceBody748_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_80 sourceBody748_0

def sourceBody748_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_14 sourceBody748_81

def sourceBody748_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_78 sourceBody748_82

def sourceBody748_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_77 sourceBody748_83

def sourceBody748_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_84

def sourceBody748_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_85

def sourceBody748_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_76 sourceBody748_86

def sourceBody748_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 672#64])

def sourceBody748_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 20)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 21))

def sourceBody748_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_89 sourceBody748_3

def sourceBody748_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_90 sourceBody748_0

def sourceBody748_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_25 sourceBody748_91

def sourceBody748_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_78 sourceBody748_92

def sourceBody748_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_88 sourceBody748_93

def sourceBody748_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_94

def sourceBody748_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_95

def sourceBody748_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_87 sourceBody748_96

def sourceBody748_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody748_99 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 22)) (some 735) ([20, 8, 16]) (some (20, sourceBody748_15, 748, 23))

def sourceBody748_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_99 sourceBody748_3

def sourceBody748_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_100 sourceBody748_0

def sourceBody748_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_36 sourceBody748_101

def sourceBody748_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_78 sourceBody748_102

def sourceBody748_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_98 sourceBody748_103

def sourceBody748_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_104

def sourceBody748_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_105

def sourceBody748_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_97 sourceBody748_106

def sourceBody748_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 864#64])

def sourceBody748_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody748_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody748_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 672#64])

def sourceBody748_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody748_113 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 24)) (some 730) ([8, 16, 12]) (some (8, sourceBody748_112, 748, 25))

def sourceBody748_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_113 sourceBody748_3

def sourceBody748_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_114 sourceBody748_0

def sourceBody748_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_111 sourceBody748_115

def sourceBody748_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_110 sourceBody748_116

def sourceBody748_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_109 sourceBody748_117

def sourceBody748_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_118

def sourceBody748_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_119

def sourceBody748_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody748_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 26)) (some 737) ([8, 16]) (some (8, sourceBody748_112, 748, 27))

def sourceBody748_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_122 sourceBody748_3

def sourceBody748_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_123 sourceBody748_0

def sourceBody748_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_121 sourceBody748_124

def sourceBody748_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_109 sourceBody748_125

def sourceBody748_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_126

def sourceBody748_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_127

def sourceBody748_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_120 sourceBody748_128

def sourceBody748_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody748_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody748_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody748_133 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 28)) (some 730) ([8, 16, 12]) (some (8, sourceBody748_112, 748, 29))

def sourceBody748_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_133 sourceBody748_3

def sourceBody748_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_134 sourceBody748_0

def sourceBody748_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_132 sourceBody748_135

def sourceBody748_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_131 sourceBody748_136

def sourceBody748_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_130 sourceBody748_137

def sourceBody748_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_138

def sourceBody748_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_139

def sourceBody748_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_129 sourceBody748_140

def sourceBody748_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody748_143 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 30)) (some 737) ([8, 16]) (some (8, sourceBody748_112, 748, 31))

def sourceBody748_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_143 sourceBody748_3

def sourceBody748_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_144 sourceBody748_0

def sourceBody748_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_142 sourceBody748_145

def sourceBody748_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_109 sourceBody748_146

def sourceBody748_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_147

def sourceBody748_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_148

def sourceBody748_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_141 sourceBody748_149

def sourceBody748_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody748_152 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 32)) (some 730) ([8, 16, 12]) (some (8, sourceBody748_112, 748, 33))

def sourceBody748_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_152 sourceBody748_3

def sourceBody748_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_153 sourceBody748_0

def sourceBody748_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_151 sourceBody748_154

def sourceBody748_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_121 sourceBody748_155

def sourceBody748_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_109 sourceBody748_156

def sourceBody748_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_157

def sourceBody748_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_158

def sourceBody748_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_150 sourceBody748_159

def sourceBody748_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody748_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody748_163 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 34)) (some 730) ([8, 16, 12]) (some (8, sourceBody748_112, 748, 35))

def sourceBody748_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_163 sourceBody748_3

def sourceBody748_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_164 sourceBody748_0

def sourceBody748_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_162 sourceBody748_165

def sourceBody748_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_121 sourceBody748_166

def sourceBody748_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_161 sourceBody748_167

def sourceBody748_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_168

def sourceBody748_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_169

def sourceBody748_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_160 sourceBody748_170

def sourceBody748_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody748_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody748_174 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 36)) (some 730) ([8, 16, 12]) (some (8, sourceBody748_112, 748, 37))

def sourceBody748_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_174 sourceBody748_3

def sourceBody748_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_175 sourceBody748_0

def sourceBody748_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_173 sourceBody748_176

def sourceBody748_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_172 sourceBody748_177

def sourceBody748_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_109 sourceBody748_178

def sourceBody748_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_179

def sourceBody748_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_180

def sourceBody748_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_171 sourceBody748_181

def sourceBody748_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody748_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody748_185 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody748_0, 748, 38)) (some 730) ([8, 16, 12]) (some (8, sourceBody748_112, 748, 39))

def sourceBody748_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_185 sourceBody748_3

def sourceBody748_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_186 sourceBody748_0

def sourceBody748_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_184 sourceBody748_187

def sourceBody748_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_121 sourceBody748_188

def sourceBody748_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_183 sourceBody748_189

def sourceBody748_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_190

def sourceBody748_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_191

def sourceBody748_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_182 sourceBody748_192

def sourceBody748_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody748_195 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody748_0, 748, 40)) (some 70) ([8]) (some (8, sourceBody748_112, 748, 41))

def sourceBody748_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_195 sourceBody748_3

def sourceBody748_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_196 sourceBody748_0

def sourceBody748_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_194 sourceBody748_197

def sourceBody748_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_198

def sourceBody748_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_199

def sourceBody748_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_193 sourceBody748_200

def sourceBody748_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody748_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody748_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_203 sourceBody748_0

def sourceBody748_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_202 sourceBody748_204

def sourceBody748_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_201 sourceBody748_205

def sourceBody748_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_108 sourceBody748_206

def sourceBody748_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_207

def sourceBody748_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_107 sourceBody748_208

def sourceBody748_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_11 sourceBody748_209

def sourceBody748_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_210

def sourceBody748_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_211

def sourceBody748_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_5 sourceBody748_212

def sourceBody748_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_213

def sourceBody748_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody748_0 sourceBody748_214

def source748 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (748, 4, sourceBody748_215)
end InitECandidate.Proofs.WordStages
