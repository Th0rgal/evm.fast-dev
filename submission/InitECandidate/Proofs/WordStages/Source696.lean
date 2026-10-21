import InitECandidate.Proofs.WordStages.Source680
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody696_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody696_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody696_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 2)) (some 653) ([]) (some (12, sourceBody696_1, 696, 3))

def sourceBody696_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody696_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_2 sourceBody696_3

def sourceBody696_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_4 sourceBody696_0

def sourceBody696_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_5

def sourceBody696_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_6

def sourceBody696_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 4)) (some 69) ([]) (some (12, sourceBody696_1, 696, 5))

def sourceBody696_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_8 sourceBody696_3

def sourceBody696_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_9 sourceBody696_0

def sourceBody696_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody696_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody696_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 6)) (some 68) ([40]) (some (40, sourceBody696_12, 696, 7))

def sourceBody696_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_13 sourceBody696_3

def sourceBody696_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_14 sourceBody696_0

def sourceBody696_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_11 sourceBody696_15

def sourceBody696_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody696_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody696_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 8)) (some 68) ([26]) (some (26, sourceBody696_18, 696, 9))

def sourceBody696_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_19 sourceBody696_3

def sourceBody696_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_20 sourceBody696_0

def sourceBody696_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_17 sourceBody696_21

def sourceBody696_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody696_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody696_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 10)) (some 68) ([56]) (some (56, sourceBody696_24, 696, 11))

def sourceBody696_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_25 sourceBody696_3

def sourceBody696_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_26 sourceBody696_0

def sourceBody696_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_23 sourceBody696_27

def sourceBody696_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody696_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody696_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 12)) (some 68) ([8]) (some (8, sourceBody696_30, 696, 13))

def sourceBody696_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_31 sourceBody696_3

def sourceBody696_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_32 sourceBody696_0

def sourceBody696_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_29 sourceBody696_33

def sourceBody696_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody696_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody696_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 14)) (some 68) ([36]) (some (36, sourceBody696_36, 696, 15))

def sourceBody696_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_37 sourceBody696_3

def sourceBody696_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_38 sourceBody696_0

def sourceBody696_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_35 sourceBody696_39

def sourceBody696_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1152#64)

def sourceBody696_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody696_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 16)) (some 68) ([22]) (some (22, sourceBody696_42, 696, 17))

def sourceBody696_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_43 sourceBody696_3

def sourceBody696_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_44 sourceBody696_0

def sourceBody696_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_41 sourceBody696_45

def sourceBody696_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody696_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody696_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 18)) (some 68) ([52]) (some (52, sourceBody696_48, 696, 19))

def sourceBody696_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_49 sourceBody696_3

def sourceBody696_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_50 sourceBody696_0

def sourceBody696_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_47 sourceBody696_51

def sourceBody696_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody696_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody696_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 20)) (some 68) ([16]) (some (16, sourceBody696_54, 696, 21))

def sourceBody696_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_55 sourceBody696_3

def sourceBody696_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_56 sourceBody696_0

def sourceBody696_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_53 sourceBody696_57

def sourceBody696_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody696_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody696_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 22)) (some 68) ([44]) (some (44, sourceBody696_60, 696, 23))

def sourceBody696_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_61 sourceBody696_3

def sourceBody696_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_62 sourceBody696_0

def sourceBody696_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_59 sourceBody696_63

def sourceBody696_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody696_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody696_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 24)) (some 68) ([30]) (some (30, sourceBody696_66, 696, 25))

def sourceBody696_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_67 sourceBody696_3

def sourceBody696_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_68 sourceBody696_0

def sourceBody696_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_65 sourceBody696_69

def sourceBody696_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody696_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody696_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 26)) (some 68) ([60]) (some (60, sourceBody696_72, 696, 27))

def sourceBody696_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_73 sourceBody696_3

def sourceBody696_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_74 sourceBody696_0

def sourceBody696_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_71 sourceBody696_75

def sourceBody696_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody696_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody696_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody696_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 28)) (some 675) ([6, 34]) (some (6, sourceBody696_79, 696, 29))

def sourceBody696_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_80 sourceBody696_3

def sourceBody696_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_81 sourceBody696_0

def sourceBody696_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_78 sourceBody696_82

def sourceBody696_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_77 sourceBody696_83

def sourceBody696_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_84

def sourceBody696_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_85

def sourceBody696_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 44)

def sourceBody696_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 30)) (some 675) ([6, 34]) (some (6, sourceBody696_79, 696, 31))

def sourceBody696_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_88 sourceBody696_3

def sourceBody696_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_89 sourceBody696_0

def sourceBody696_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_87 sourceBody696_90

def sourceBody696_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_77 sourceBody696_91

def sourceBody696_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_92

def sourceBody696_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_93

def sourceBody696_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_86 sourceBody696_94

def sourceBody696_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody696_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 4)

def sourceBody696_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 50) sourceBody696_100 sourceBody696_101

def sourceBody696_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_102 sourceBody696_3

def sourceBody696_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody696_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody696_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody696_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 50 50 34 20))

def sourceBody696_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_107 sourceBody696_0

def sourceBody696_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_106 sourceBody696_108

def sourceBody696_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_105 sourceBody696_109

def sourceBody696_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 50])

def sourceBody696_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody696_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 12)

def sourceBody696_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody696_115 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 32)) (some 691) ([28, 58]) (some (28, sourceBody696_114, 696, 33))

def sourceBody696_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_115 sourceBody696_3

def sourceBody696_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_116 sourceBody696_0

def sourceBody696_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_113 sourceBody696_117

def sourceBody696_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_112 sourceBody696_118

def sourceBody696_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 42)

def sourceBody696_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_124 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.reg 10) sourceBody696_122 sourceBody696_123

def sourceBody696_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_124 sourceBody696_3

def sourceBody696_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 58)

def sourceBody696_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 48)

def sourceBody696_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody696_129 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody696_0, 696, 34)) (some 70) ([58]) (some (58, sourceBody696_128, 696, 35))

def sourceBody696_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_129 sourceBody696_3

def sourceBody696_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_130 sourceBody696_0

def sourceBody696_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_127 sourceBody696_131

def sourceBody696_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_132

def sourceBody696_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_133

def sourceBody696_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody696_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody696_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_136 sourceBody696_0

def sourceBody696_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_135 sourceBody696_137

def sourceBody696_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_134 sourceBody696_138

def sourceBody696_140 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody696_139 sourceBody696_0

def sourceBody696_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_140 sourceBody696_3

def sourceBody696_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_141 sourceBody696_0

def sourceBody696_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_126 sourceBody696_142

def sourceBody696_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_125 sourceBody696_143

def sourceBody696_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_121 sourceBody696_144

def sourceBody696_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_120 sourceBody696_145

def sourceBody696_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody696_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 40)

def sourceBody696_149 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 36)) (some 692) ([58, 10]) (some (58, sourceBody696_128, 696, 37))

def sourceBody696_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_149 sourceBody696_3

def sourceBody696_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_150 sourceBody696_0

def sourceBody696_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_148 sourceBody696_151

def sourceBody696_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_147 sourceBody696_152

def sourceBody696_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody696_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_157 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 38) sourceBody696_156 sourceBody696_121

def sourceBody696_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_157 sourceBody696_3

def sourceBody696_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody696_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 48)

def sourceBody696_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody696_162 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody696_0, 696, 38)) (some 70) ([10]) (some (10, sourceBody696_161, 696, 39))

def sourceBody696_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_162 sourceBody696_3

def sourceBody696_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_163 sourceBody696_0

def sourceBody696_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_160 sourceBody696_164

def sourceBody696_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_165

def sourceBody696_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_166

def sourceBody696_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody696_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [58]

def sourceBody696_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_169 sourceBody696_0

def sourceBody696_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_168 sourceBody696_170

def sourceBody696_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_167 sourceBody696_171

def sourceBody696_173 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody696_172 sourceBody696_0

def sourceBody696_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_173 sourceBody696_3

def sourceBody696_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_174 sourceBody696_0

def sourceBody696_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_159 sourceBody696_175

def sourceBody696_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_158 sourceBody696_176

def sourceBody696_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_155 sourceBody696_177

def sourceBody696_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_154 sourceBody696_178

def sourceBody696_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 26)

def sourceBody696_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody696_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 4891460686036598785#64)

def sourceBody696_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2896914383306846353#64)

def sourceBody696_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 13281191951274694749#64)

def sourceBody696_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3486998266802970665#64)

def sourceBody696_186 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 40)) (some 680) ([10, 38, 24, 54, 18, 46, 32]) (some (10, sourceBody696_161, 696, 41))

def sourceBody696_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_186 sourceBody696_3

def sourceBody696_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_187 sourceBody696_0

def sourceBody696_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_185 sourceBody696_188

def sourceBody696_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_184 sourceBody696_189

def sourceBody696_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_183 sourceBody696_190

def sourceBody696_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_182 sourceBody696_191

def sourceBody696_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_181 sourceBody696_192

def sourceBody696_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_180 sourceBody696_193

def sourceBody696_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_156 sourceBody696_194

def sourceBody696_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_195

def sourceBody696_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_196

def sourceBody696_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_179 sourceBody696_197

def sourceBody696_199 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 42)) (some 677) ([10, 38]) (some (10, sourceBody696_161, 696, 43))

def sourceBody696_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_199 sourceBody696_3

def sourceBody696_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_200 sourceBody696_0

def sourceBody696_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_180 sourceBody696_201

def sourceBody696_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_156 sourceBody696_202

def sourceBody696_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_206 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 38 (Flapjack.WordRegImm.reg 24) sourceBody696_205 sourceBody696_155

def sourceBody696_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_206 sourceBody696_3

def sourceBody696_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 38)

def sourceBody696_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 48)

def sourceBody696_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody696_211 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody696_0, 696, 44)) (some 70) ([38]) (some (38, sourceBody696_210, 696, 45))

def sourceBody696_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_211 sourceBody696_3

def sourceBody696_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_212 sourceBody696_0

def sourceBody696_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_209 sourceBody696_213

def sourceBody696_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_214

def sourceBody696_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_215

def sourceBody696_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody696_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody696_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_218 sourceBody696_0

def sourceBody696_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_217 sourceBody696_219

def sourceBody696_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_216 sourceBody696_220

def sourceBody696_222 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody696_221 sourceBody696_0

def sourceBody696_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_222 sourceBody696_3

def sourceBody696_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_223 sourceBody696_0

def sourceBody696_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_208 sourceBody696_224

def sourceBody696_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_207 sourceBody696_225

def sourceBody696_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_204 sourceBody696_226

def sourceBody696_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_126 sourceBody696_227

def sourceBody696_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody696_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 56)

def sourceBody696_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody696_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 4891460686036598785#64)

def sourceBody696_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 2896914383306846353#64)

def sourceBody696_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 13281191951274694749#64)

def sourceBody696_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 3486998266802970665#64)

def sourceBody696_236 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 46)) (some 680) ([38, 24, 54, 18, 46, 32, 62]) (some (38, sourceBody696_210, 696, 47))

def sourceBody696_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_236 sourceBody696_3

def sourceBody696_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_237 sourceBody696_0

def sourceBody696_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_235 sourceBody696_238

def sourceBody696_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_234 sourceBody696_239

def sourceBody696_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_233 sourceBody696_240

def sourceBody696_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_232 sourceBody696_241

def sourceBody696_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_231 sourceBody696_242

def sourceBody696_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_230 sourceBody696_243

def sourceBody696_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_229 sourceBody696_244

def sourceBody696_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_245

def sourceBody696_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_246

def sourceBody696_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_228 sourceBody696_247

def sourceBody696_249 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 48)) (some 677) ([38, 24]) (some (38, sourceBody696_210, 696, 49))

def sourceBody696_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_249 sourceBody696_3

def sourceBody696_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_250 sourceBody696_0

def sourceBody696_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_230 sourceBody696_251

def sourceBody696_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_229 sourceBody696_252

def sourceBody696_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_256 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 54) sourceBody696_255 sourceBody696_204

def sourceBody696_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_256 sourceBody696_3

def sourceBody696_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody696_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 48)

def sourceBody696_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody696_261 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody696_0, 696, 50)) (some 70) ([24]) (some (24, sourceBody696_260, 696, 51))

def sourceBody696_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_261 sourceBody696_3

def sourceBody696_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_262 sourceBody696_0

def sourceBody696_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_259 sourceBody696_263

def sourceBody696_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_264

def sourceBody696_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_265

def sourceBody696_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38]

def sourceBody696_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_267 sourceBody696_0

def sourceBody696_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_229 sourceBody696_268

def sourceBody696_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_266 sourceBody696_269

def sourceBody696_271 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody696_270 sourceBody696_0

def sourceBody696_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_271 sourceBody696_3

def sourceBody696_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_272 sourceBody696_0

def sourceBody696_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_258 sourceBody696_273

def sourceBody696_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_257 sourceBody696_274

def sourceBody696_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_254 sourceBody696_275

def sourceBody696_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_159 sourceBody696_276

def sourceBody696_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 12)

def sourceBody696_279 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 52)) (some 677) ([24, 54]) (some (24, sourceBody696_260, 696, 53))

def sourceBody696_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_279 sourceBody696_3

def sourceBody696_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_280 sourceBody696_0

def sourceBody696_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_278 sourceBody696_281

def sourceBody696_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_255 sourceBody696_282

def sourceBody696_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody696_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 40)

def sourceBody696_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody696_287 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 54)) (some 677) ([54, 18]) (some (54, sourceBody696_286, 696, 55))

def sourceBody696_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_287 sourceBody696_3

def sourceBody696_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_288 sourceBody696_0

def sourceBody696_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_285 sourceBody696_289

def sourceBody696_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_284 sourceBody696_290

def sourceBody696_292 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.var 24])

def sourceBody696_293 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_296 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 46) sourceBody696_294 sourceBody696_295

def sourceBody696_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_296 sourceBody696_3

def sourceBody696_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody696_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody696_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 40)

def sourceBody696_301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody696_302 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 56)) (some 682) ([18, 46]) (some (18, sourceBody696_301, 696, 57))

def sourceBody696_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_302 sourceBody696_3

def sourceBody696_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_303 sourceBody696_0

def sourceBody696_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_300 sourceBody696_304

def sourceBody696_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_299 sourceBody696_305

def sourceBody696_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_306

def sourceBody696_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_307

def sourceBody696_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 36)

def sourceBody696_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody696_311 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 58)) (some 683) ([18, 46]) (some (18, sourceBody696_301, 696, 59))

def sourceBody696_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_311 sourceBody696_3

def sourceBody696_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_312 sourceBody696_0

def sourceBody696_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_310 sourceBody696_313

def sourceBody696_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_309 sourceBody696_314

def sourceBody696_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_315

def sourceBody696_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_316

def sourceBody696_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_308 sourceBody696_317

def sourceBody696_319 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody696_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 52)

def sourceBody696_321 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 8)

def sourceBody696_322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 36)

def sourceBody696_323 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 60)) (some 689) ([18, 46, 32, 62]) (some (18, sourceBody696_301, 696, 61))

def sourceBody696_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_323 sourceBody696_3

def sourceBody696_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_324 sourceBody696_0

def sourceBody696_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_322 sourceBody696_325

def sourceBody696_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_321 sourceBody696_326

def sourceBody696_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_320 sourceBody696_327

def sourceBody696_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_319 sourceBody696_328

def sourceBody696_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_329

def sourceBody696_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_330

def sourceBody696_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_318 sourceBody696_331

def sourceBody696_333 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody696_334 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 16)

def sourceBody696_335 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody696_336 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 62)) (some 664) ([18, 46, 32]) (some (18, sourceBody696_301, 696, 63))

def sourceBody696_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_336 sourceBody696_3

def sourceBody696_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_337 sourceBody696_0

def sourceBody696_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_335 sourceBody696_338

def sourceBody696_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_334 sourceBody696_339

def sourceBody696_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_333 sourceBody696_340

def sourceBody696_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_341

def sourceBody696_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_342

def sourceBody696_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_332 sourceBody696_343

def sourceBody696_345 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 44)

def sourceBody696_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 44)

def sourceBody696_347 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 52)

def sourceBody696_348 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 64)) (some 664) ([18, 46, 32]) (some (18, sourceBody696_301, 696, 65))

def sourceBody696_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_348 sourceBody696_3

def sourceBody696_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_349 sourceBody696_0

def sourceBody696_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_347 sourceBody696_350

def sourceBody696_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_346 sourceBody696_351

def sourceBody696_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_345 sourceBody696_352

def sourceBody696_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_353

def sourceBody696_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_354

def sourceBody696_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_344 sourceBody696_355

def sourceBody696_357 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_357 sourceBody696_0

def sourceBody696_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_358 sourceBody696_0

def sourceBody696_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_356 sourceBody696_359

def sourceBody696_361 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody696_360 sourceBody696_0

def sourceBody696_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_361 sourceBody696_3

def sourceBody696_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_362 sourceBody696_0

def sourceBody696_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_298 sourceBody696_363

def sourceBody696_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_297 sourceBody696_364

def sourceBody696_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_293 sourceBody696_365

def sourceBody696_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_292 sourceBody696_366

def sourceBody696_368 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody696_369 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 54)

def sourceBody696_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_369 sourceBody696_0

def sourceBody696_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_370 sourceBody696_0

def sourceBody696_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_368 sourceBody696_371

def sourceBody696_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_372

def sourceBody696_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_367 sourceBody696_373

def sourceBody696_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_291 sourceBody696_374

def sourceBody696_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_375

def sourceBody696_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_376

def sourceBody696_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_283 sourceBody696_377

def sourceBody696_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_378

def sourceBody696_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_379

def sourceBody696_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_277 sourceBody696_380

def sourceBody696_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_253 sourceBody696_381

def sourceBody696_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_382

def sourceBody696_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_383

def sourceBody696_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_248 sourceBody696_384

def sourceBody696_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_203 sourceBody696_385

def sourceBody696_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_386

def sourceBody696_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_387

def sourceBody696_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_198 sourceBody696_388

def sourceBody696_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_153 sourceBody696_389

def sourceBody696_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_390

def sourceBody696_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_391

def sourceBody696_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_146 sourceBody696_392

def sourceBody696_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_119 sourceBody696_393

def sourceBody696_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_394

def sourceBody696_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_395

def sourceBody696_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_111 sourceBody696_396

def sourceBody696_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_110 sourceBody696_397

def sourceBody696_399 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody696_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_398 sourceBody696_399

def sourceBody696_401 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody696_402 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody696_400 sourceBody696_401

def sourceBody696_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_402 sourceBody696_3

def sourceBody696_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_403 sourceBody696_0

def sourceBody696_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_104 sourceBody696_404

def sourceBody696_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_103 sourceBody696_405

def sourceBody696_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_99 sourceBody696_406

def sourceBody696_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_98 sourceBody696_407

def sourceBody696_409 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln) sourceBody696_408 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody696_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_409 sourceBody696_3

def sourceBody696_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_3 sourceBody696_410

def sourceBody696_412 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_413 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 60)

def sourceBody696_414 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_415 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody696_416 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody696_417 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 50 (Flapjack.WordRegImm.reg 14) sourceBody696_415 sourceBody696_416

def sourceBody696_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_417 sourceBody696_3

def sourceBody696_419 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 50)

def sourceBody696_420 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 44)

def sourceBody696_421 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 44)

def sourceBody696_422 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody696_423 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 66)) (some 687) ([50, 14]) (some (50, sourceBody696_422, 696, 67))

def sourceBody696_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_423 sourceBody696_3

def sourceBody696_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_424 sourceBody696_0

def sourceBody696_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_421 sourceBody696_425

def sourceBody696_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_420 sourceBody696_426

def sourceBody696_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_427

def sourceBody696_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_428

def sourceBody696_430 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 16)

def sourceBody696_431 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody696_432 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 44)

def sourceBody696_433 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 68)) (some 664) ([50, 14, 42]) (some (50, sourceBody696_422, 696, 69))

def sourceBody696_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_433 sourceBody696_3

def sourceBody696_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_434 sourceBody696_0

def sourceBody696_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_432 sourceBody696_435

def sourceBody696_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_431 sourceBody696_436

def sourceBody696_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_430 sourceBody696_437

def sourceBody696_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_438

def sourceBody696_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_439

def sourceBody696_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_429 sourceBody696_440

def sourceBody696_442 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 30)

def sourceBody696_443 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 384#64]))

def sourceBody696_444 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody696_445 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 70)) (some 688) ([50, 14, 42, 28]) (some (50, sourceBody696_422, 696, 71))

def sourceBody696_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_445 sourceBody696_3

def sourceBody696_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_446 sourceBody696_0

def sourceBody696_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_444 sourceBody696_447

def sourceBody696_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_443 sourceBody696_448

def sourceBody696_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_431 sourceBody696_449

def sourceBody696_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_442 sourceBody696_450

def sourceBody696_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_451

def sourceBody696_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_452

def sourceBody696_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_441 sourceBody696_453

def sourceBody696_455 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 22)

def sourceBody696_456 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody696_457 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 72)) (some 78) ([50, 14]) (some (50, sourceBody696_422, 696, 73))

def sourceBody696_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_457 sourceBody696_3

def sourceBody696_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_458 sourceBody696_0

def sourceBody696_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_456 sourceBody696_459

def sourceBody696_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_455 sourceBody696_460

def sourceBody696_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_461

def sourceBody696_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_462

def sourceBody696_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_454 sourceBody696_463

def sourceBody696_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody696_466 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 15230403791020821917#64)

def sourceBody696_467 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 754611498739239741#64)

def sourceBody696_468 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 7381016538464732716#64)

def sourceBody696_469 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1011752739694698287#64)

def sourceBody696_470 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 50)

def sourceBody696_471 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 58

def sourceBody696_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_471 sourceBody696_0

def sourceBody696_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_470 sourceBody696_472

def sourceBody696_474 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 14)

def sourceBody696_475 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 8#64])
  58

def sourceBody696_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_475 sourceBody696_0

def sourceBody696_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_474 sourceBody696_476

def sourceBody696_478 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 16#64])
  58

def sourceBody696_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_478 sourceBody696_0

def sourceBody696_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_120 sourceBody696_479

def sourceBody696_481 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 28)

def sourceBody696_482 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 24#64])
  58

def sourceBody696_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_482 sourceBody696_0

def sourceBody696_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_481 sourceBody696_483

def sourceBody696_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_484 sourceBody696_0

def sourceBody696_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_480 sourceBody696_485

def sourceBody696_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_477 sourceBody696_486

def sourceBody696_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_473 sourceBody696_487

def sourceBody696_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_469 sourceBody696_488

def sourceBody696_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_489

def sourceBody696_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_468 sourceBody696_490

def sourceBody696_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_491

def sourceBody696_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_467 sourceBody696_492

def sourceBody696_494 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_493

def sourceBody696_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_466 sourceBody696_494

def sourceBody696_496 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_495

def sourceBody696_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_465 sourceBody696_496

def sourceBody696_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_497

def sourceBody696_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_464 sourceBody696_498

def sourceBody696_500 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody696_501 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody696_502 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 74)) (some 79) ([20, 50, 14]) (some (20, sourceBody696_501, 696, 75))

def sourceBody696_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_502 sourceBody696_3

def sourceBody696_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_503 sourceBody696_0

def sourceBody696_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_456 sourceBody696_504

def sourceBody696_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_455 sourceBody696_505

def sourceBody696_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_500 sourceBody696_506

def sourceBody696_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_499 sourceBody696_507

def sourceBody696_509 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody696_508 sourceBody696_0

def sourceBody696_510 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_509 sourceBody696_3

def sourceBody696_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_510 sourceBody696_0

def sourceBody696_512 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_419 sourceBody696_511

def sourceBody696_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_418 sourceBody696_512

def sourceBody696_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_414 sourceBody696_513

def sourceBody696_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_413 sourceBody696_514

def sourceBody696_516 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 48)

def sourceBody696_517 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody696_0, 696, 76)) (some 70) ([50]) (some (50, sourceBody696_422, 696, 77))

def sourceBody696_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_517 sourceBody696_3

def sourceBody696_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_518 sourceBody696_0

def sourceBody696_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_516 sourceBody696_519

def sourceBody696_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_520

def sourceBody696_522 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_521

def sourceBody696_523 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_515 sourceBody696_522

def sourceBody696_524 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 34)

def sourceBody696_525 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody696_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_525 sourceBody696_0

def sourceBody696_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_524 sourceBody696_526

def sourceBody696_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_523 sourceBody696_527

def sourceBody696_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_412 sourceBody696_528

def sourceBody696_530 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_529

def sourceBody696_531 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_411 sourceBody696_530

def sourceBody696_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_97 sourceBody696_531

def sourceBody696_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_532

def sourceBody696_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_96 sourceBody696_533

def sourceBody696_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_534

def sourceBody696_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_95 sourceBody696_535

def sourceBody696_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_76 sourceBody696_536

def sourceBody696_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_537

def sourceBody696_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_538

def sourceBody696_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_70 sourceBody696_539

def sourceBody696_541 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_540

def sourceBody696_542 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_541

def sourceBody696_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_64 sourceBody696_542

def sourceBody696_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_543

def sourceBody696_545 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_544

def sourceBody696_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_58 sourceBody696_545

def sourceBody696_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_546

def sourceBody696_548 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_547

def sourceBody696_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_52 sourceBody696_548

def sourceBody696_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_549

def sourceBody696_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_550

def sourceBody696_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_46 sourceBody696_551

def sourceBody696_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_552

def sourceBody696_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_553

def sourceBody696_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_40 sourceBody696_554

def sourceBody696_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_555

def sourceBody696_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_556

def sourceBody696_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_34 sourceBody696_557

def sourceBody696_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_558

def sourceBody696_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_559

def sourceBody696_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_28 sourceBody696_560

def sourceBody696_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_561

def sourceBody696_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_562

def sourceBody696_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_22 sourceBody696_563

def sourceBody696_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_564

def sourceBody696_566 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_565

def sourceBody696_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_16 sourceBody696_566

def sourceBody696_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_567

def sourceBody696_569 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_568

def sourceBody696_570 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_10 sourceBody696_569

def sourceBody696_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_570

def sourceBody696_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_0 sourceBody696_571

def sourceBody696_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody696_7 sourceBody696_572

def source696 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (696, 3, sourceBody696_573)
end InitECandidate.Proofs.WordStages
