import InitECandidate.Proofs.WordStages.Source662
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody678_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody678_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody678_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody678_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 2)) (some 69) ([]) (some (22, sourceBody678_2, 678, 3))

def sourceBody678_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody678_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_3 sourceBody678_4

def sourceBody678_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_5 sourceBody678_0

def sourceBody678_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody678_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 12])

def sourceBody678_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody678_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody678_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody678_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 4)) (some 68) ([20]) (some (20, sourceBody678_11, 678, 5))

def sourceBody678_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_12 sourceBody678_4

def sourceBody678_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_13 sourceBody678_0

def sourceBody678_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_10 sourceBody678_14

def sourceBody678_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 12)

def sourceBody678_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody678_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 6)) (some 68) ([36]) (some (36, sourceBody678_17, 678, 7))

def sourceBody678_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_18 sourceBody678_4

def sourceBody678_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_19 sourceBody678_0

def sourceBody678_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_16 sourceBody678_20

def sourceBody678_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody678_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody678_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 8)) (some 68) ([16]) (some (16, sourceBody678_23, 678, 9))

def sourceBody678_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_24 sourceBody678_4

def sourceBody678_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_25 sourceBody678_0

def sourceBody678_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_22 sourceBody678_26

def sourceBody678_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody678_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody678_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 10)) (some 68) ([32]) (some (32, sourceBody678_29, 678, 11))

def sourceBody678_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_30 sourceBody678_4

def sourceBody678_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_31 sourceBody678_0

def sourceBody678_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_28 sourceBody678_32

def sourceBody678_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody678_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody678_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 12)) (some 68) ([24]) (some (24, sourceBody678_35, 678, 13))

def sourceBody678_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_36 sourceBody678_4

def sourceBody678_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_37 sourceBody678_0

def sourceBody678_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_34 sourceBody678_38

def sourceBody678_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody678_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody678_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 14)) (some 68) ([40]) (some (40, sourceBody678_41, 678, 15))

def sourceBody678_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_42 sourceBody678_4

def sourceBody678_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_43 sourceBody678_0

def sourceBody678_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_40 sourceBody678_44

def sourceBody678_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody678_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody678_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 16)) (some 68) ([8]) (some (8, sourceBody678_47, 678, 17))

def sourceBody678_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_48 sourceBody678_4

def sourceBody678_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_49 sourceBody678_0

def sourceBody678_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_46 sourceBody678_50

def sourceBody678_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody678_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody678_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody678_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody678_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 18)) (some 667) ([26, 18, 34]) (some (26, sourceBody678_55, 678, 19))

def sourceBody678_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_56 sourceBody678_4

def sourceBody678_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_57 sourceBody678_0

def sourceBody678_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_54 sourceBody678_58

def sourceBody678_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_53 sourceBody678_59

def sourceBody678_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_60

def sourceBody678_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_61

def sourceBody678_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_62

def sourceBody678_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody678_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 24)

def sourceBody678_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody678_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 20)) (some 671) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 21))

def sourceBody678_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_67 sourceBody678_4

def sourceBody678_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_68 sourceBody678_0

def sourceBody678_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_66 sourceBody678_69

def sourceBody678_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_65 sourceBody678_70

def sourceBody678_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_64 sourceBody678_71

def sourceBody678_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_72

def sourceBody678_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_73

def sourceBody678_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_74

def sourceBody678_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_63 sourceBody678_75

def sourceBody678_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody678_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody678_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody678_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 22)) (some 666) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 23))

def sourceBody678_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_80 sourceBody678_4

def sourceBody678_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_81 sourceBody678_0

def sourceBody678_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_79 sourceBody678_82

def sourceBody678_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_78 sourceBody678_83

def sourceBody678_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_77 sourceBody678_84

def sourceBody678_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_85

def sourceBody678_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_86

def sourceBody678_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_87

def sourceBody678_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_76 sourceBody678_88

def sourceBody678_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 38)

def sourceBody678_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 24)) (some 666) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 25))

def sourceBody678_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_91 sourceBody678_4

def sourceBody678_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_92 sourceBody678_0

def sourceBody678_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_90 sourceBody678_93

def sourceBody678_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_54 sourceBody678_94

def sourceBody678_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_53 sourceBody678_95

def sourceBody678_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_96

def sourceBody678_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_97

def sourceBody678_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_98

def sourceBody678_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_89 sourceBody678_99

def sourceBody678_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 36)

def sourceBody678_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody678_103 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 26)) (some 666) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 27))

def sourceBody678_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_103 sourceBody678_4

def sourceBody678_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_104 sourceBody678_0

def sourceBody678_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_102 sourceBody678_105

def sourceBody678_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_65 sourceBody678_106

def sourceBody678_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_101 sourceBody678_107

def sourceBody678_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_108

def sourceBody678_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_109

def sourceBody678_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_110

def sourceBody678_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_100 sourceBody678_111

def sourceBody678_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody678_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 28)) (some 667) ([26, 18, 34]) (some (26, sourceBody678_55, 678, 29))

def sourceBody678_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_114 sourceBody678_4

def sourceBody678_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_115 sourceBody678_0

def sourceBody678_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_113 sourceBody678_116

def sourceBody678_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_53 sourceBody678_117

def sourceBody678_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_118

def sourceBody678_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_119

def sourceBody678_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_120

def sourceBody678_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_112 sourceBody678_121

def sourceBody678_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 40)

def sourceBody678_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody678_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody678_126 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 30)) (some 671) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 31))

def sourceBody678_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_126 sourceBody678_4

def sourceBody678_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_127 sourceBody678_0

def sourceBody678_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_125 sourceBody678_128

def sourceBody678_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_124 sourceBody678_129

def sourceBody678_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_123 sourceBody678_130

def sourceBody678_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_131

def sourceBody678_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_132

def sourceBody678_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_133

def sourceBody678_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_122 sourceBody678_134

def sourceBody678_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody678_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 40)

def sourceBody678_138 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 32)) (some 669) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 33))

def sourceBody678_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_138 sourceBody678_4

def sourceBody678_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_139 sourceBody678_0

def sourceBody678_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_137 sourceBody678_140

def sourceBody678_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_65 sourceBody678_141

def sourceBody678_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_136 sourceBody678_142

def sourceBody678_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_143

def sourceBody678_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_144

def sourceBody678_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_145

def sourceBody678_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_135 sourceBody678_146

def sourceBody678_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody678_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 20)

def sourceBody678_150 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 34)) (some 667) ([26, 18, 34]) (some (26, sourceBody678_55, 678, 35))

def sourceBody678_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_150 sourceBody678_4

def sourceBody678_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_151 sourceBody678_0

def sourceBody678_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_149 sourceBody678_152

def sourceBody678_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_148 sourceBody678_153

def sourceBody678_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_154

def sourceBody678_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_155

def sourceBody678_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_156

def sourceBody678_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_147 sourceBody678_157

def sourceBody678_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody678_160 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 36)) (some 666) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 37))

def sourceBody678_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_160 sourceBody678_4

def sourceBody678_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_161 sourceBody678_0

def sourceBody678_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_102 sourceBody678_162

def sourceBody678_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_159 sourceBody678_163

def sourceBody678_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_53 sourceBody678_164

def sourceBody678_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_165

def sourceBody678_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_166

def sourceBody678_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_167

def sourceBody678_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_158 sourceBody678_168

def sourceBody678_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody678_171 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 38)) (some 671) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 39))

def sourceBody678_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_171 sourceBody678_4

def sourceBody678_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_172 sourceBody678_0

def sourceBody678_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_170 sourceBody678_173

def sourceBody678_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_65 sourceBody678_174

def sourceBody678_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_53 sourceBody678_175

def sourceBody678_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_176

def sourceBody678_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_177

def sourceBody678_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_178

def sourceBody678_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_169 sourceBody678_179

def sourceBody678_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody678_182 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 40)) (some 671) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 41))

def sourceBody678_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_182 sourceBody678_4

def sourceBody678_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_183 sourceBody678_0

def sourceBody678_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_181 sourceBody678_184

def sourceBody678_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_124 sourceBody678_185

def sourceBody678_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_123 sourceBody678_186

def sourceBody678_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_187

def sourceBody678_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_188

def sourceBody678_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_189

def sourceBody678_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_180 sourceBody678_190

def sourceBody678_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody678_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody678_194 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 42)) (some 669) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 43))

def sourceBody678_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_194 sourceBody678_4

def sourceBody678_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_195 sourceBody678_0

def sourceBody678_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_193 sourceBody678_196

def sourceBody678_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_192 sourceBody678_197

def sourceBody678_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_123 sourceBody678_198

def sourceBody678_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_199

def sourceBody678_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_200

def sourceBody678_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_201

def sourceBody678_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_191 sourceBody678_202

def sourceBody678_204 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 44)) (some 666) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 45))

def sourceBody678_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_204 sourceBody678_4

def sourceBody678_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_205 sourceBody678_0

def sourceBody678_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_137 sourceBody678_206

def sourceBody678_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_113 sourceBody678_207

def sourceBody678_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_123 sourceBody678_208

def sourceBody678_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_209

def sourceBody678_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_210

def sourceBody678_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_211

def sourceBody678_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_203 sourceBody678_212

def sourceBody678_214 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 46)) (some 667) ([26, 18, 34]) (some (26, sourceBody678_55, 678, 47))

def sourceBody678_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_214 sourceBody678_4

def sourceBody678_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_215 sourceBody678_0

def sourceBody678_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_78 sourceBody678_216

def sourceBody678_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_64 sourceBody678_217

def sourceBody678_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_218

def sourceBody678_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_219

def sourceBody678_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_220

def sourceBody678_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_213 sourceBody678_221

def sourceBody678_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 32)

def sourceBody678_224 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 48)) (some 666) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 49))

def sourceBody678_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_224 sourceBody678_4

def sourceBody678_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_225 sourceBody678_0

def sourceBody678_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_223 sourceBody678_226

def sourceBody678_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_113 sourceBody678_227

def sourceBody678_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_64 sourceBody678_228

def sourceBody678_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_229

def sourceBody678_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_230

def sourceBody678_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_231

def sourceBody678_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_222 sourceBody678_232

def sourceBody678_234 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 50)) (some 671) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 51))

def sourceBody678_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_234 sourceBody678_4

def sourceBody678_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_235 sourceBody678_0

def sourceBody678_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_125 sourceBody678_236

def sourceBody678_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_113 sourceBody678_237

def sourceBody678_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_64 sourceBody678_238

def sourceBody678_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_239

def sourceBody678_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_240

def sourceBody678_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_241

def sourceBody678_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_233 sourceBody678_242

def sourceBody678_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 28)

def sourceBody678_245 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 52)) (some 669) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 53))

def sourceBody678_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_245 sourceBody678_4

def sourceBody678_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_246 sourceBody678_0

def sourceBody678_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_244 sourceBody678_247

def sourceBody678_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_192 sourceBody678_248

def sourceBody678_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_123 sourceBody678_249

def sourceBody678_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_250

def sourceBody678_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_251

def sourceBody678_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_252

def sourceBody678_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_243 sourceBody678_253

def sourceBody678_255 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 54)) (some 666) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 55))

def sourceBody678_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_255 sourceBody678_4

def sourceBody678_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_256 sourceBody678_0

def sourceBody678_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_223 sourceBody678_257

def sourceBody678_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_149 sourceBody678_258

def sourceBody678_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_77 sourceBody678_259

def sourceBody678_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_260

def sourceBody678_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_261

def sourceBody678_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_262

def sourceBody678_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_254 sourceBody678_263

def sourceBody678_265 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 56)) (some 671) ([26, 18, 34, 14]) (some (26, sourceBody678_55, 678, 57))

def sourceBody678_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_265 sourceBody678_4

def sourceBody678_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_266 sourceBody678_0

def sourceBody678_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_125 sourceBody678_267

def sourceBody678_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_149 sourceBody678_268

def sourceBody678_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_77 sourceBody678_269

def sourceBody678_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_52 sourceBody678_270

def sourceBody678_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_271

def sourceBody678_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_272

def sourceBody678_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_264 sourceBody678_273

def sourceBody678_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody678_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody678_277 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 58)) (some 77) ([26, 18, 34]) (some (26, sourceBody678_55, 678, 59))

def sourceBody678_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_277 sourceBody678_4

def sourceBody678_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_278 sourceBody678_0

def sourceBody678_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_276 sourceBody678_279

def sourceBody678_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_53 sourceBody678_280

def sourceBody678_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_275 sourceBody678_281

def sourceBody678_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_282

def sourceBody678_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_283

def sourceBody678_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_274 sourceBody678_284

def sourceBody678_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 12])

def sourceBody678_287 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 60)) (some 77) ([26, 18, 34]) (some (26, sourceBody678_55, 678, 61))

def sourceBody678_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_287 sourceBody678_4

def sourceBody678_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_288 sourceBody678_0

def sourceBody678_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_276 sourceBody678_289

def sourceBody678_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_123 sourceBody678_290

def sourceBody678_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_286 sourceBody678_291

def sourceBody678_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_292

def sourceBody678_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_293

def sourceBody678_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_285 sourceBody678_294

def sourceBody678_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody678_297 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody678_0, 678, 62)) (some 77) ([26, 18, 34]) (some (26, sourceBody678_55, 678, 63))

def sourceBody678_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_297 sourceBody678_4

def sourceBody678_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_298 sourceBody678_0

def sourceBody678_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_276 sourceBody678_299

def sourceBody678_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_77 sourceBody678_300

def sourceBody678_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_296 sourceBody678_301

def sourceBody678_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_302

def sourceBody678_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_303

def sourceBody678_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_295 sourceBody678_304

def sourceBody678_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody678_307 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody678_0, 678, 64)) (some 70) ([26]) (some (26, sourceBody678_55, 678, 65))

def sourceBody678_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_307 sourceBody678_4

def sourceBody678_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_308 sourceBody678_0

def sourceBody678_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_306 sourceBody678_309

def sourceBody678_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_310

def sourceBody678_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_311

def sourceBody678_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_305 sourceBody678_312

def sourceBody678_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody678_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody678_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_315 sourceBody678_0

def sourceBody678_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_314 sourceBody678_316

def sourceBody678_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_313 sourceBody678_317

def sourceBody678_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_51 sourceBody678_318

def sourceBody678_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_319

def sourceBody678_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_320

def sourceBody678_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_45 sourceBody678_321

def sourceBody678_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_322

def sourceBody678_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_323

def sourceBody678_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_39 sourceBody678_324

def sourceBody678_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_325

def sourceBody678_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_326

def sourceBody678_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_33 sourceBody678_327

def sourceBody678_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_328

def sourceBody678_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_329

def sourceBody678_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_27 sourceBody678_330

def sourceBody678_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_331

def sourceBody678_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_332

def sourceBody678_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_21 sourceBody678_333

def sourceBody678_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_334

def sourceBody678_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_335

def sourceBody678_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_15 sourceBody678_336

def sourceBody678_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_337

def sourceBody678_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_338

def sourceBody678_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_9 sourceBody678_339

def sourceBody678_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_340

def sourceBody678_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_8 sourceBody678_341

def sourceBody678_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_342

def sourceBody678_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_7 sourceBody678_343

def sourceBody678_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_344

def sourceBody678_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_6 sourceBody678_345

def sourceBody678_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_346

def sourceBody678_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_347

def sourceBody678_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_1 sourceBody678_348

def sourceBody678_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody678_0 sourceBody678_349

def source678 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (678, 4, sourceBody678_350)
end InitECandidate.Proofs.WordStages
