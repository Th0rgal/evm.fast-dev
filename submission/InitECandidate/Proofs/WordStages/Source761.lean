import InitECandidate.Proofs.WordStages.Source745
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody761_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody761_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody761_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 2)) (some 69) ([]) (some (8, sourceBody761_1, 761, 3))

def sourceBody761_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody761_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_2 sourceBody761_3

def sourceBody761_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_4 sourceBody761_0

def sourceBody761_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2880#64)

def sourceBody761_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody761_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 4)) (some 68) ([18]) (some (18, sourceBody761_7, 761, 5))

def sourceBody761_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_8 sourceBody761_3

def sourceBody761_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_9 sourceBody761_0

def sourceBody761_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_6 sourceBody761_10

def sourceBody761_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody761_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody761_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1152#64])

def sourceBody761_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1728#64])

def sourceBody761_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 2304#64])

def sourceBody761_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody761_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody761_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody761_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 6)) (some 757) ([24, 10]) (some (24, sourceBody761_19, 761, 7))

def sourceBody761_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_20 sourceBody761_3

def sourceBody761_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_21 sourceBody761_0

def sourceBody761_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_18 sourceBody761_22

def sourceBody761_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_23

def sourceBody761_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_24

def sourceBody761_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_25

def sourceBody761_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody761_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 8)) (some 756) ([24, 10]) (some (24, sourceBody761_19, 761, 9))

def sourceBody761_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_28 sourceBody761_3

def sourceBody761_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_29 sourceBody761_0

def sourceBody761_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_18 sourceBody761_30

def sourceBody761_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_27 sourceBody761_31

def sourceBody761_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_32

def sourceBody761_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_33

def sourceBody761_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_26 sourceBody761_34

def sourceBody761_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody761_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody761_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 10)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 11))

def sourceBody761_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_38 sourceBody761_3

def sourceBody761_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_39 sourceBody761_0

def sourceBody761_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_37 sourceBody761_40

def sourceBody761_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_36 sourceBody761_41

def sourceBody761_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_27 sourceBody761_42

def sourceBody761_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_43

def sourceBody761_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_44

def sourceBody761_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_35 sourceBody761_45

def sourceBody761_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 12)) (some 758) ([24, 10]) (some (24, sourceBody761_19, 761, 13))

def sourceBody761_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_47 sourceBody761_3

def sourceBody761_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_48 sourceBody761_0

def sourceBody761_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_36 sourceBody761_49

def sourceBody761_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_50

def sourceBody761_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_51

def sourceBody761_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_52

def sourceBody761_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_46 sourceBody761_53

def sourceBody761_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody761_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 14)) (some 758) ([24, 10]) (some (24, sourceBody761_19, 761, 15))

def sourceBody761_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_56 sourceBody761_3

def sourceBody761_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_57 sourceBody761_0

def sourceBody761_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_55 sourceBody761_58

def sourceBody761_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_59

def sourceBody761_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_60

def sourceBody761_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_61

def sourceBody761_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_54 sourceBody761_62

def sourceBody761_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 16)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 17))

def sourceBody761_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_64 sourceBody761_3

def sourceBody761_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_65 sourceBody761_0

def sourceBody761_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_37 sourceBody761_66

def sourceBody761_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_36 sourceBody761_67

def sourceBody761_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_27 sourceBody761_68

def sourceBody761_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_69

def sourceBody761_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_70

def sourceBody761_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_63 sourceBody761_71

def sourceBody761_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody761_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 18)) (some 760) ([24, 10]) (some (24, sourceBody761_19, 761, 19))

def sourceBody761_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_74 sourceBody761_3

def sourceBody761_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_75 sourceBody761_0

def sourceBody761_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_36 sourceBody761_76

def sourceBody761_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_73 sourceBody761_77

def sourceBody761_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_78

def sourceBody761_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_79

def sourceBody761_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_72 sourceBody761_80

def sourceBody761_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 20)) (some 756) ([24, 10]) (some (24, sourceBody761_19, 761, 21))

def sourceBody761_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_82 sourceBody761_3

def sourceBody761_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_83 sourceBody761_0

def sourceBody761_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_36 sourceBody761_84

def sourceBody761_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_85

def sourceBody761_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_86

def sourceBody761_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_87

def sourceBody761_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_81 sourceBody761_88

def sourceBody761_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody761_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 22)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 23))

def sourceBody761_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_91 sourceBody761_3

def sourceBody761_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_92 sourceBody761_0

def sourceBody761_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_37 sourceBody761_93

def sourceBody761_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_90 sourceBody761_94

def sourceBody761_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_73 sourceBody761_95

def sourceBody761_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_96

def sourceBody761_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_97

def sourceBody761_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_89 sourceBody761_98

def sourceBody761_100 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 24)) (some 760) ([24, 10]) (some (24, sourceBody761_19, 761, 25))

def sourceBody761_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_100 sourceBody761_3

def sourceBody761_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_101 sourceBody761_0

def sourceBody761_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_90 sourceBody761_102

def sourceBody761_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_103

def sourceBody761_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_104

def sourceBody761_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_105

def sourceBody761_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_99 sourceBody761_106

def sourceBody761_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 26)) (some 756) ([24, 10]) (some (24, sourceBody761_19, 761, 27))

def sourceBody761_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_108 sourceBody761_3

def sourceBody761_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_109 sourceBody761_0

def sourceBody761_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_90 sourceBody761_110

def sourceBody761_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_73 sourceBody761_111

def sourceBody761_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_112

def sourceBody761_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_113

def sourceBody761_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_107 sourceBody761_114

def sourceBody761_116 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 28)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 29))

def sourceBody761_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_116 sourceBody761_3

def sourceBody761_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_117 sourceBody761_0

def sourceBody761_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_37 sourceBody761_118

def sourceBody761_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_90 sourceBody761_119

def sourceBody761_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_73 sourceBody761_120

def sourceBody761_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_121

def sourceBody761_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_122

def sourceBody761_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_115 sourceBody761_123

def sourceBody761_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody761_126 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 30)) (some 760) ([24, 10]) (some (24, sourceBody761_19, 761, 31))

def sourceBody761_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_126 sourceBody761_3

def sourceBody761_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_127 sourceBody761_0

def sourceBody761_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_90 sourceBody761_128

def sourceBody761_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_125 sourceBody761_129

def sourceBody761_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_130

def sourceBody761_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_131

def sourceBody761_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_124 sourceBody761_132

def sourceBody761_134 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 32)) (some 758) ([24, 10]) (some (24, sourceBody761_19, 761, 33))

def sourceBody761_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_134 sourceBody761_3

def sourceBody761_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_135 sourceBody761_0

def sourceBody761_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_90 sourceBody761_136

def sourceBody761_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_137

def sourceBody761_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_138

def sourceBody761_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_139

def sourceBody761_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_133 sourceBody761_140

def sourceBody761_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 26)

def sourceBody761_143 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 34)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 35))

def sourceBody761_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_143 sourceBody761_3

def sourceBody761_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_144 sourceBody761_0

def sourceBody761_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_37 sourceBody761_145

def sourceBody761_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_142 sourceBody761_146

def sourceBody761_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_125 sourceBody761_147

def sourceBody761_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_148

def sourceBody761_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_149

def sourceBody761_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_141 sourceBody761_150

def sourceBody761_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody761_153 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 36)) (some 760) ([24, 10]) (some (24, sourceBody761_19, 761, 37))

def sourceBody761_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_153 sourceBody761_3

def sourceBody761_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_154 sourceBody761_0

def sourceBody761_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_142 sourceBody761_155

def sourceBody761_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_152 sourceBody761_156

def sourceBody761_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_157

def sourceBody761_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_158

def sourceBody761_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_151 sourceBody761_159

def sourceBody761_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody761_162 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 38)) (some 760) ([24, 10]) (some (24, sourceBody761_19, 761, 39))

def sourceBody761_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_162 sourceBody761_3

def sourceBody761_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_163 sourceBody761_0

def sourceBody761_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_161 sourceBody761_164

def sourceBody761_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_152 sourceBody761_165

def sourceBody761_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_166

def sourceBody761_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_167

def sourceBody761_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_160 sourceBody761_168

def sourceBody761_170 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 40)) (some 758) ([24, 10]) (some (24, sourceBody761_19, 761, 41))

def sourceBody761_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_170 sourceBody761_3

def sourceBody761_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_171 sourceBody761_0

def sourceBody761_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_142 sourceBody761_172

def sourceBody761_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_173

def sourceBody761_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_174

def sourceBody761_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_175

def sourceBody761_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_169 sourceBody761_176

def sourceBody761_178 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 42)) (some 758) ([24, 10]) (some (24, sourceBody761_19, 761, 43))

def sourceBody761_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_178 sourceBody761_3

def sourceBody761_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_179 sourceBody761_0

def sourceBody761_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_55 sourceBody761_180

def sourceBody761_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_181

def sourceBody761_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_182

def sourceBody761_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_183

def sourceBody761_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_177 sourceBody761_184

def sourceBody761_186 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 44)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 45))

def sourceBody761_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_186 sourceBody761_3

def sourceBody761_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_187 sourceBody761_0

def sourceBody761_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_37 sourceBody761_188

def sourceBody761_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_161 sourceBody761_189

def sourceBody761_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_152 sourceBody761_190

def sourceBody761_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_191

def sourceBody761_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_192

def sourceBody761_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_185 sourceBody761_193

def sourceBody761_195 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 46)) (some 756) ([24, 10]) (some (24, sourceBody761_19, 761, 47))

def sourceBody761_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_195 sourceBody761_3

def sourceBody761_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_196 sourceBody761_0

def sourceBody761_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_142 sourceBody761_197

def sourceBody761_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_198

def sourceBody761_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_199

def sourceBody761_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_200

def sourceBody761_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_194 sourceBody761_201

def sourceBody761_203 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 48)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 49))

def sourceBody761_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_203 sourceBody761_3

def sourceBody761_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_204 sourceBody761_0

def sourceBody761_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_37 sourceBody761_205

def sourceBody761_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_161 sourceBody761_206

def sourceBody761_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_152 sourceBody761_207

def sourceBody761_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_208

def sourceBody761_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_209

def sourceBody761_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_202 sourceBody761_210

def sourceBody761_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody761_213 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 50)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 51))

def sourceBody761_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_213 sourceBody761_3

def sourceBody761_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_214 sourceBody761_0

def sourceBody761_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_212 sourceBody761_215

def sourceBody761_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_36 sourceBody761_216

def sourceBody761_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_217

def sourceBody761_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_218

def sourceBody761_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_219

def sourceBody761_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_211 sourceBody761_220

def sourceBody761_222 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 52)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 53))

def sourceBody761_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_222 sourceBody761_3

def sourceBody761_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_223 sourceBody761_0

def sourceBody761_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_212 sourceBody761_224

def sourceBody761_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_55 sourceBody761_225

def sourceBody761_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_17 sourceBody761_226

def sourceBody761_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_227

def sourceBody761_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_228

def sourceBody761_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_221 sourceBody761_229

def sourceBody761_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody761_232 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody761_0, 761, 54)) (some 754) ([24, 10, 20]) (some (24, sourceBody761_19, 761, 55))

def sourceBody761_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_232 sourceBody761_3

def sourceBody761_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_233 sourceBody761_0

def sourceBody761_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_37 sourceBody761_234

def sourceBody761_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_161 sourceBody761_235

def sourceBody761_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_231 sourceBody761_236

def sourceBody761_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_237

def sourceBody761_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_238

def sourceBody761_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_230 sourceBody761_239

def sourceBody761_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody761_242 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody761_0, 761, 56)) (some 70) ([24]) (some (24, sourceBody761_19, 761, 57))

def sourceBody761_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_242 sourceBody761_3

def sourceBody761_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_243 sourceBody761_0

def sourceBody761_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_241 sourceBody761_244

def sourceBody761_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_245

def sourceBody761_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_246

def sourceBody761_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_240 sourceBody761_247

def sourceBody761_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody761_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody761_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_250 sourceBody761_0

def sourceBody761_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_249 sourceBody761_251

def sourceBody761_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_248 sourceBody761_252

def sourceBody761_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_16 sourceBody761_253

def sourceBody761_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_254

def sourceBody761_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_15 sourceBody761_255

def sourceBody761_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_256

def sourceBody761_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_14 sourceBody761_257

def sourceBody761_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_258

def sourceBody761_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_13 sourceBody761_259

def sourceBody761_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_260

def sourceBody761_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_12 sourceBody761_261

def sourceBody761_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_262

def sourceBody761_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_11 sourceBody761_263

def sourceBody761_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_264

def sourceBody761_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_265

def sourceBody761_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_5 sourceBody761_266

def sourceBody761_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_267

def sourceBody761_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody761_0 sourceBody761_268

def source761 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (761, 3, sourceBody761_269)
end InitECandidate.Proofs.WordStages
