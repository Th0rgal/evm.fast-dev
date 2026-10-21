import InitECandidate.Proofs.WordStages.Source673
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody689_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody689_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody689_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 2)) (some 69) ([]) (some (20, sourceBody689_1, 689, 3))

def sourceBody689_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody689_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_2 sourceBody689_3

def sourceBody689_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_4 sourceBody689_0

def sourceBody689_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody689_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody689_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 4)) (some 68) ([36]) (some (36, sourceBody689_7, 689, 5))

def sourceBody689_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_8 sourceBody689_3

def sourceBody689_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_9 sourceBody689_0

def sourceBody689_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_6 sourceBody689_10

def sourceBody689_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody689_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody689_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 6)) (some 68) ([12]) (some (12, sourceBody689_13, 689, 7))

def sourceBody689_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_14 sourceBody689_3

def sourceBody689_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_15 sourceBody689_0

def sourceBody689_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_12 sourceBody689_16

def sourceBody689_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody689_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody689_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 8)) (some 68) ([26]) (some (26, sourceBody689_19, 689, 9))

def sourceBody689_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_20 sourceBody689_3

def sourceBody689_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_21 sourceBody689_0

def sourceBody689_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_18 sourceBody689_22

def sourceBody689_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody689_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody689_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 10)) (some 68) ([18]) (some (18, sourceBody689_25, 689, 11))

def sourceBody689_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_26 sourceBody689_3

def sourceBody689_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_27 sourceBody689_0

def sourceBody689_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_24 sourceBody689_28

def sourceBody689_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody689_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody689_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 12)) (some 68) ([34]) (some (34, sourceBody689_31, 689, 13))

def sourceBody689_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_32 sourceBody689_3

def sourceBody689_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_33 sourceBody689_0

def sourceBody689_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_30 sourceBody689_34

def sourceBody689_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody689_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody689_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 14)) (some 68) ([14]) (some (14, sourceBody689_37, 689, 15))

def sourceBody689_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_38 sourceBody689_3

def sourceBody689_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_39 sourceBody689_0

def sourceBody689_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_36 sourceBody689_40

def sourceBody689_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 20)

def sourceBody689_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody689_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody689_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody689_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 16)) (some 77) ([30, 22, 38]) (some (30, sourceBody689_45, 689, 17))

def sourceBody689_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_46 sourceBody689_3

def sourceBody689_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_47 sourceBody689_0

def sourceBody689_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_44 sourceBody689_48

def sourceBody689_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_43 sourceBody689_49

def sourceBody689_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_42 sourceBody689_50

def sourceBody689_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_51

def sourceBody689_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_52

def sourceBody689_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody689_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 18)) (some 77) ([30, 22, 38]) (some (30, sourceBody689_45, 689, 19))

def sourceBody689_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_55 sourceBody689_3

def sourceBody689_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_56 sourceBody689_0

def sourceBody689_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_44 sourceBody689_57

def sourceBody689_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_43 sourceBody689_58

def sourceBody689_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_54 sourceBody689_59

def sourceBody689_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_60

def sourceBody689_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_61

def sourceBody689_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_53 sourceBody689_62

def sourceBody689_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody689_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody689_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody689_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 20)) (some 670) ([30, 22, 38]) (some (30, sourceBody689_45, 689, 21))

def sourceBody689_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_67 sourceBody689_3

def sourceBody689_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_68 sourceBody689_0

def sourceBody689_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_66 sourceBody689_69

def sourceBody689_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_65 sourceBody689_70

def sourceBody689_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_64 sourceBody689_71

def sourceBody689_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_72

def sourceBody689_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_73

def sourceBody689_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_63 sourceBody689_74

def sourceBody689_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody689_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 22)) (some 675) ([30, 22]) (some (30, sourceBody689_45, 689, 23))

def sourceBody689_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_77 sourceBody689_3

def sourceBody689_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_78 sourceBody689_0

def sourceBody689_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_76 sourceBody689_79

def sourceBody689_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_64 sourceBody689_80

def sourceBody689_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_81

def sourceBody689_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_82

def sourceBody689_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_75 sourceBody689_83

def sourceBody689_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody689_86 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 24)) (some 675) ([30, 22]) (some (30, sourceBody689_45, 689, 25))

def sourceBody689_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_86 sourceBody689_3

def sourceBody689_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_87 sourceBody689_0

def sourceBody689_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_85 sourceBody689_88

def sourceBody689_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_64 sourceBody689_89

def sourceBody689_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_90

def sourceBody689_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_91

def sourceBody689_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_84 sourceBody689_92

def sourceBody689_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody689_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody689_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 14)

def sourceBody689_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody689_98 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 22 (Flapjack.WordRegImm.reg 38) sourceBody689_97 sourceBody689_95

def sourceBody689_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_98 sourceBody689_3

def sourceBody689_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody689_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody689_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody689_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_102 sourceBody689_0

def sourceBody689_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_103 sourceBody689_0

def sourceBody689_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_101 sourceBody689_104

def sourceBody689_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_105

def sourceBody689_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody689_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody689_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 34)

def sourceBody689_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody689_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody689_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 8)

def sourceBody689_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody689_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 26)) (some 681) ([22, 38, 10, 24, 16, 32]) (some (22, sourceBody689_113, 689, 27))

def sourceBody689_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_114 sourceBody689_3

def sourceBody689_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_115 sourceBody689_0

def sourceBody689_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_112 sourceBody689_116

def sourceBody689_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_111 sourceBody689_117

def sourceBody689_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_110 sourceBody689_118

def sourceBody689_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_119

def sourceBody689_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_108 sourceBody689_120

def sourceBody689_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_121

def sourceBody689_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_122

def sourceBody689_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_123

def sourceBody689_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_106 sourceBody689_124

def sourceBody689_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 2)

def sourceBody689_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 28)) (some 665) ([22, 38]) (some (22, sourceBody689_113, 689, 29))

def sourceBody689_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_127 sourceBody689_3

def sourceBody689_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_128 sourceBody689_0

def sourceBody689_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_126 sourceBody689_129

def sourceBody689_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_76 sourceBody689_130

def sourceBody689_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_131

def sourceBody689_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_132

def sourceBody689_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_125 sourceBody689_133

def sourceBody689_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody689_136 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 30)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 31))

def sourceBody689_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_136 sourceBody689_3

def sourceBody689_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_137 sourceBody689_0

def sourceBody689_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_135 sourceBody689_138

def sourceBody689_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_126 sourceBody689_139

def sourceBody689_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_76 sourceBody689_140

def sourceBody689_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_141

def sourceBody689_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_142

def sourceBody689_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_134 sourceBody689_143

def sourceBody689_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 4)

def sourceBody689_146 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 32)) (some 665) ([22, 38]) (some (22, sourceBody689_113, 689, 33))

def sourceBody689_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_146 sourceBody689_3

def sourceBody689_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_147 sourceBody689_0

def sourceBody689_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_145 sourceBody689_148

def sourceBody689_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_85 sourceBody689_149

def sourceBody689_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_150

def sourceBody689_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_151

def sourceBody689_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_144 sourceBody689_152

def sourceBody689_154 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 34)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 35))

def sourceBody689_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_154 sourceBody689_3

def sourceBody689_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_155 sourceBody689_0

def sourceBody689_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_156

def sourceBody689_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_145 sourceBody689_157

def sourceBody689_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_85 sourceBody689_158

def sourceBody689_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_159

def sourceBody689_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_160

def sourceBody689_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_153 sourceBody689_161

def sourceBody689_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 20)

def sourceBody689_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 20)

def sourceBody689_165 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 36)) (some 678) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 37))

def sourceBody689_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_165 sourceBody689_3

def sourceBody689_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_166 sourceBody689_0

def sourceBody689_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_164 sourceBody689_167

def sourceBody689_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_163 sourceBody689_168

def sourceBody689_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_169

def sourceBody689_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_170

def sourceBody689_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_171

def sourceBody689_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_162 sourceBody689_172

def sourceBody689_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.const 11637723931993326632#64)
        (Flapjack.WordLangExpHOL.var 14),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody689_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody689_176 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 38) sourceBody689_97 sourceBody689_95

def sourceBody689_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_176 sourceBody689_3

def sourceBody689_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody689_179 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 38)) (some 681) ([22, 38, 10, 24, 16, 32]) (some (22, sourceBody689_113, 689, 39))

def sourceBody689_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_179 sourceBody689_3

def sourceBody689_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_180 sourceBody689_0

def sourceBody689_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_112 sourceBody689_181

def sourceBody689_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_178 sourceBody689_182

def sourceBody689_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_110 sourceBody689_183

def sourceBody689_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_184

def sourceBody689_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_108 sourceBody689_185

def sourceBody689_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_186

def sourceBody689_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_187

def sourceBody689_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_188

def sourceBody689_190 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 40)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 41))

def sourceBody689_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_190 sourceBody689_3

def sourceBody689_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_191 sourceBody689_0

def sourceBody689_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_135 sourceBody689_192

def sourceBody689_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_126 sourceBody689_193

def sourceBody689_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_76 sourceBody689_194

def sourceBody689_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_195

def sourceBody689_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_196

def sourceBody689_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_189 sourceBody689_197

def sourceBody689_199 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 42)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 43))

def sourceBody689_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_199 sourceBody689_3

def sourceBody689_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_200 sourceBody689_0

def sourceBody689_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_201

def sourceBody689_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_145 sourceBody689_202

def sourceBody689_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_85 sourceBody689_203

def sourceBody689_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_204

def sourceBody689_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_205

def sourceBody689_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_198 sourceBody689_206

def sourceBody689_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody689_209 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 44)) (some 679) ([22, 38, 10, 24]) (some (22, sourceBody689_113, 689, 45))

def sourceBody689_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_209 sourceBody689_3

def sourceBody689_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_210 sourceBody689_0

def sourceBody689_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_208 sourceBody689_211

def sourceBody689_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_164 sourceBody689_212

def sourceBody689_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_163 sourceBody689_213

def sourceBody689_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_214

def sourceBody689_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_215

def sourceBody689_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_216

def sourceBody689_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_207 sourceBody689_217

def sourceBody689_219 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody689_218 sourceBody689_0

def sourceBody689_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_219 sourceBody689_3

def sourceBody689_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_220 sourceBody689_0

def sourceBody689_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_100 sourceBody689_221

def sourceBody689_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_177 sourceBody689_222

def sourceBody689_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_175 sourceBody689_223

def sourceBody689_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_174 sourceBody689_224

def sourceBody689_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_173 sourceBody689_225

def sourceBody689_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.const 290499802545784960#64)
        (Flapjack.WordLangExpHOL.var 14),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody689_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 36)

def sourceBody689_229 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 46)) (some 681) ([22, 38, 10, 24, 16, 32]) (some (22, sourceBody689_113, 689, 47))

def sourceBody689_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_229 sourceBody689_3

def sourceBody689_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_230 sourceBody689_0

def sourceBody689_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_112 sourceBody689_231

def sourceBody689_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_228 sourceBody689_232

def sourceBody689_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_110 sourceBody689_233

def sourceBody689_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_234

def sourceBody689_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_108 sourceBody689_235

def sourceBody689_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_236

def sourceBody689_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_237

def sourceBody689_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_238

def sourceBody689_240 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 48)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 49))

def sourceBody689_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_240 sourceBody689_3

def sourceBody689_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_241 sourceBody689_0

def sourceBody689_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_135 sourceBody689_242

def sourceBody689_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_126 sourceBody689_243

def sourceBody689_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_76 sourceBody689_244

def sourceBody689_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_245

def sourceBody689_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_246

def sourceBody689_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_239 sourceBody689_247

def sourceBody689_249 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 50)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 51))

def sourceBody689_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_249 sourceBody689_3

def sourceBody689_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_250 sourceBody689_0

def sourceBody689_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_251

def sourceBody689_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_145 sourceBody689_252

def sourceBody689_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_85 sourceBody689_253

def sourceBody689_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_254

def sourceBody689_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_255

def sourceBody689_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_248 sourceBody689_256

def sourceBody689_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody689_259 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 52)) (some 679) ([22, 38, 10, 24]) (some (22, sourceBody689_113, 689, 53))

def sourceBody689_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_259 sourceBody689_3

def sourceBody689_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_260 sourceBody689_0

def sourceBody689_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_258 sourceBody689_261

def sourceBody689_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_164 sourceBody689_262

def sourceBody689_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_163 sourceBody689_263

def sourceBody689_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_264

def sourceBody689_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_265

def sourceBody689_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_266

def sourceBody689_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_257 sourceBody689_267

def sourceBody689_269 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody689_268 sourceBody689_0

def sourceBody689_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_269 sourceBody689_3

def sourceBody689_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_270 sourceBody689_0

def sourceBody689_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_100 sourceBody689_271

def sourceBody689_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_177 sourceBody689_272

def sourceBody689_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_175 sourceBody689_273

def sourceBody689_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_227 sourceBody689_274

def sourceBody689_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_226 sourceBody689_275

def sourceBody689_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody689_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_276 sourceBody689_277

def sourceBody689_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody689_280 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody689_278 sourceBody689_279

def sourceBody689_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_280 sourceBody689_3

def sourceBody689_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_281 sourceBody689_0

def sourceBody689_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_100 sourceBody689_282

def sourceBody689_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_99 sourceBody689_283

def sourceBody689_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_96 sourceBody689_284

def sourceBody689_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_95 sourceBody689_285

def sourceBody689_287 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody689_286 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody689_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_287 sourceBody689_3

def sourceBody689_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_3 sourceBody689_288

def sourceBody689_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody689_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 6)

def sourceBody689_292 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 54)) (some 684) ([22, 38]) (some (22, sourceBody689_113, 689, 55))

def sourceBody689_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_292 sourceBody689_3

def sourceBody689_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_293 sourceBody689_0

def sourceBody689_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_291 sourceBody689_294

def sourceBody689_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_290 sourceBody689_295

def sourceBody689_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_296

def sourceBody689_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_297

def sourceBody689_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_289 sourceBody689_298

def sourceBody689_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody689_301 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 56)) (some 684) ([22, 38]) (some (22, sourceBody689_113, 689, 57))

def sourceBody689_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_301 sourceBody689_3

def sourceBody689_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_302 sourceBody689_0

def sourceBody689_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_66 sourceBody689_303

def sourceBody689_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_300 sourceBody689_304

def sourceBody689_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_305

def sourceBody689_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_306

def sourceBody689_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_299 sourceBody689_307

def sourceBody689_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody689_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody689_311 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 58)) (some 684) ([22, 38]) (some (22, sourceBody689_113, 689, 59))

def sourceBody689_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_311 sourceBody689_3

def sourceBody689_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_312 sourceBody689_0

def sourceBody689_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_310 sourceBody689_313

def sourceBody689_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_309 sourceBody689_314

def sourceBody689_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_315

def sourceBody689_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_316

def sourceBody689_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_308 sourceBody689_317

def sourceBody689_319 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody689_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 12)

def sourceBody689_321 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 60)) (some 684) ([22, 38]) (some (22, sourceBody689_113, 689, 61))

def sourceBody689_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_321 sourceBody689_3

def sourceBody689_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_322 sourceBody689_0

def sourceBody689_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_320 sourceBody689_323

def sourceBody689_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_319 sourceBody689_324

def sourceBody689_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_325

def sourceBody689_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_326

def sourceBody689_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_318 sourceBody689_327

def sourceBody689_329 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody689_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody689_331 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 62)) (some 684) ([22, 38]) (some (22, sourceBody689_113, 689, 63))

def sourceBody689_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_331 sourceBody689_3

def sourceBody689_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_332 sourceBody689_0

def sourceBody689_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_330 sourceBody689_333

def sourceBody689_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_329 sourceBody689_334

def sourceBody689_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_335

def sourceBody689_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_336

def sourceBody689_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_328 sourceBody689_337

def sourceBody689_339 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody689_340 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody689_341 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 64)) (some 670) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 65))

def sourceBody689_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_341 sourceBody689_3

def sourceBody689_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_342 sourceBody689_0

def sourceBody689_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_340 sourceBody689_343

def sourceBody689_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_339 sourceBody689_344

def sourceBody689_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_345

def sourceBody689_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_346

def sourceBody689_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_347

def sourceBody689_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_338 sourceBody689_348

def sourceBody689_350 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody689_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 768#64])

def sourceBody689_352 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 66)) (some 684) ([22, 38]) (some (22, sourceBody689_113, 689, 67))

def sourceBody689_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_352 sourceBody689_3

def sourceBody689_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_353 sourceBody689_0

def sourceBody689_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_351 sourceBody689_354

def sourceBody689_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_350 sourceBody689_355

def sourceBody689_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_356

def sourceBody689_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_357

def sourceBody689_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_349 sourceBody689_358

def sourceBody689_360 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody689_361 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 68)) (some 681) ([22, 38, 10, 24, 16, 32]) (some (22, sourceBody689_113, 689, 69))

def sourceBody689_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_361 sourceBody689_3

def sourceBody689_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_362 sourceBody689_0

def sourceBody689_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_112 sourceBody689_363

def sourceBody689_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_360 sourceBody689_364

def sourceBody689_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_110 sourceBody689_365

def sourceBody689_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_366

def sourceBody689_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_108 sourceBody689_367

def sourceBody689_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_368

def sourceBody689_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_369

def sourceBody689_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_370

def sourceBody689_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_359 sourceBody689_371

def sourceBody689_373 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 70)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 71))

def sourceBody689_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_373 sourceBody689_3

def sourceBody689_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_374 sourceBody689_0

def sourceBody689_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_135 sourceBody689_375

def sourceBody689_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_126 sourceBody689_376

def sourceBody689_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_76 sourceBody689_377

def sourceBody689_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_378

def sourceBody689_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_379

def sourceBody689_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_372 sourceBody689_380

def sourceBody689_382 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 72)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 73))

def sourceBody689_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_382 sourceBody689_3

def sourceBody689_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_383 sourceBody689_0

def sourceBody689_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_384

def sourceBody689_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_145 sourceBody689_385

def sourceBody689_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_85 sourceBody689_386

def sourceBody689_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_387

def sourceBody689_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_388

def sourceBody689_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_381 sourceBody689_389

def sourceBody689_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody689_392 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 74)) (some 679) ([22, 38, 10, 24]) (some (22, sourceBody689_113, 689, 75))

def sourceBody689_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_392 sourceBody689_3

def sourceBody689_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_393 sourceBody689_0

def sourceBody689_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_391 sourceBody689_394

def sourceBody689_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_164 sourceBody689_395

def sourceBody689_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_163 sourceBody689_396

def sourceBody689_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_397

def sourceBody689_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_398

def sourceBody689_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_399

def sourceBody689_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_390 sourceBody689_400

def sourceBody689_402 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody689_403 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 76)) (some 681) ([22, 38, 10, 24, 16, 32]) (some (22, sourceBody689_113, 689, 77))

def sourceBody689_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_403 sourceBody689_3

def sourceBody689_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_404 sourceBody689_0

def sourceBody689_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_112 sourceBody689_405

def sourceBody689_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_402 sourceBody689_406

def sourceBody689_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_110 sourceBody689_407

def sourceBody689_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_408

def sourceBody689_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_108 sourceBody689_409

def sourceBody689_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_107 sourceBody689_410

def sourceBody689_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_411

def sourceBody689_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_412

def sourceBody689_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_401 sourceBody689_413

def sourceBody689_415 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 78)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 79))

def sourceBody689_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_415 sourceBody689_3

def sourceBody689_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_416 sourceBody689_0

def sourceBody689_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_135 sourceBody689_417

def sourceBody689_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_126 sourceBody689_418

def sourceBody689_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_76 sourceBody689_419

def sourceBody689_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_420

def sourceBody689_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_421

def sourceBody689_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_414 sourceBody689_422

def sourceBody689_424 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody689_0, 689, 80)) (some 664) ([22, 38, 10]) (some (22, sourceBody689_113, 689, 81))

def sourceBody689_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_424 sourceBody689_3

def sourceBody689_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_425 sourceBody689_0

def sourceBody689_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_109 sourceBody689_426

def sourceBody689_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_145 sourceBody689_427

def sourceBody689_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_85 sourceBody689_428

def sourceBody689_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_429

def sourceBody689_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_430

def sourceBody689_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_423 sourceBody689_431

def sourceBody689_433 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody689_434 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody689_0, 689, 82)) (some 70) ([22]) (some (22, sourceBody689_113, 689, 83))

def sourceBody689_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_434 sourceBody689_3

def sourceBody689_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_435 sourceBody689_0

def sourceBody689_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_433 sourceBody689_436

def sourceBody689_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_437

def sourceBody689_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_438

def sourceBody689_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_432 sourceBody689_439

def sourceBody689_441 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody689_442 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody689_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_442 sourceBody689_0

def sourceBody689_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_441 sourceBody689_443

def sourceBody689_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_440 sourceBody689_444

def sourceBody689_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_94 sourceBody689_445

def sourceBody689_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_446

def sourceBody689_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_93 sourceBody689_447

def sourceBody689_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_41 sourceBody689_448

def sourceBody689_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_449

def sourceBody689_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_450

def sourceBody689_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_35 sourceBody689_451

def sourceBody689_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_452

def sourceBody689_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_453

def sourceBody689_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_29 sourceBody689_454

def sourceBody689_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_455

def sourceBody689_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_456

def sourceBody689_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_23 sourceBody689_457

def sourceBody689_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_458

def sourceBody689_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_459

def sourceBody689_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_17 sourceBody689_460

def sourceBody689_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_461

def sourceBody689_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_462

def sourceBody689_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_11 sourceBody689_463

def sourceBody689_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_464

def sourceBody689_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_465

def sourceBody689_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_5 sourceBody689_466

def sourceBody689_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_467

def sourceBody689_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody689_0 sourceBody689_468

def source689 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (689, 5, sourceBody689_469)
end InitECandidate.Proofs.WordStages
