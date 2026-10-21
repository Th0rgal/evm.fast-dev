import InitECandidate.Proofs.WordStages.Source540
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody556_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody556_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody556_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 40, 28, 52]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 2)) (some 471) ([]) (some (10, sourceBody556_1, 556, 3))

def sourceBody556_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody556_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_2 sourceBody556_3

def sourceBody556_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_4 sourceBody556_0

def sourceBody556_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody556_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 36, 24, 48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 4)) (some 471) ([]) (some (18, sourceBody556_6, 556, 5))

def sourceBody556_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_7 sourceBody556_3

def sourceBody556_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_8 sourceBody556_0

def sourceBody556_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody556_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 44, 32, 56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 6)) (some 471) ([]) (some (8, sourceBody556_10, 556, 7))

def sourceBody556_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_11 sourceBody556_3

def sourceBody556_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_12 sourceBody556_0

def sourceBody556_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody556_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 44)

def sourceBody556_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 32)

def sourceBody556_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 56)

def sourceBody556_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody556_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 8)) (some 458) ([34, 22, 46, 16]) (some (34, sourceBody556_18, 556, 9))

def sourceBody556_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_19 sourceBody556_3

def sourceBody556_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_20 sourceBody556_0

def sourceBody556_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_17 sourceBody556_21

def sourceBody556_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_16 sourceBody556_22

def sourceBody556_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_15 sourceBody556_23

def sourceBody556_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_14 sourceBody556_24

def sourceBody556_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody556_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody556_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 10)) (some 461) ([22]) (some (22, sourceBody556_27, 556, 11))

def sourceBody556_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_28 sourceBody556_3

def sourceBody556_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_29 sourceBody556_0

def sourceBody556_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_26 sourceBody556_30

def sourceBody556_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody556_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody556_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody556_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 52)

def sourceBody556_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody556_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody556_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 32)

def sourceBody556_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 56)

def sourceBody556_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody556_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([22, 46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 12)) (some 476) ([16, 42, 30, 54, 12, 38, 26, 50]) (some (16, sourceBody556_40, 556, 13))

def sourceBody556_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_41 sourceBody556_3

def sourceBody556_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_42 sourceBody556_0

def sourceBody556_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_39 sourceBody556_43

def sourceBody556_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_38 sourceBody556_44

def sourceBody556_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_37 sourceBody556_45

def sourceBody556_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_36 sourceBody556_46

def sourceBody556_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_35 sourceBody556_47

def sourceBody556_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_34 sourceBody556_48

def sourceBody556_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_33 sourceBody556_49

def sourceBody556_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_32 sourceBody556_50

def sourceBody556_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 34)

def sourceBody556_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody556_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 54 54 42 30))

def sourceBody556_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 54])

def sourceBody556_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 22)

def sourceBody556_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody556_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 14)) (some 459) ([12, 38]) (some (42, sourceBody556_57, 556, 15))

def sourceBody556_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_58 sourceBody556_3

def sourceBody556_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_59 sourceBody556_0

def sourceBody556_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_56 sourceBody556_60

def sourceBody556_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_55 sourceBody556_61

def sourceBody556_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_54 sourceBody556_62

def sourceBody556_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_53 sourceBody556_63

def sourceBody556_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_52 sourceBody556_64

def sourceBody556_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody556_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody556_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 16)) (some 466) ([30]) (some (30, sourceBody556_67, 556, 17))

def sourceBody556_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_68 sourceBody556_3

def sourceBody556_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_69 sourceBody556_0

def sourceBody556_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_66 sourceBody556_70

def sourceBody556_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_71

def sourceBody556_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_72

def sourceBody556_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 46)

def sourceBody556_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 18)) (some 478) ([30]) (some (30, sourceBody556_67, 556, 19))

def sourceBody556_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_75 sourceBody556_3

def sourceBody556_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_76 sourceBody556_0

def sourceBody556_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_74 sourceBody556_77

def sourceBody556_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_78

def sourceBody556_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_79

def sourceBody556_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_73 sourceBody556_80

def sourceBody556_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody556_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody556_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody556_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody556_86 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 54) sourceBody556_84 sourceBody556_85

def sourceBody556_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_86 sourceBody556_3

def sourceBody556_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody556_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody556_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody556_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody556_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 52)

def sourceBody556_93 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 20)) (some 458) ([30, 54, 12, 38]) (some (30, sourceBody556_67, 556, 21))

def sourceBody556_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_93 sourceBody556_3

def sourceBody556_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_94 sourceBody556_0

def sourceBody556_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_92 sourceBody556_95

def sourceBody556_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_91 sourceBody556_96

def sourceBody556_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_90 sourceBody556_97

def sourceBody556_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_89 sourceBody556_98

def sourceBody556_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 10)

def sourceBody556_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody556_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 24)

def sourceBody556_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 48)

def sourceBody556_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody556_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody556_0, 556, 22)) (some 458) ([54, 12, 38, 26]) (some (54, sourceBody556_104, 556, 23))

def sourceBody556_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_105 sourceBody556_3

def sourceBody556_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_106 sourceBody556_0

def sourceBody556_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_103 sourceBody556_107

def sourceBody556_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_102 sourceBody556_108

def sourceBody556_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_101 sourceBody556_109

def sourceBody556_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_100 sourceBody556_110

def sourceBody556_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody556_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 6)

def sourceBody556_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody556_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 8)

def sourceBody556_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 24#64]),
      Flapjack.WordLangExpHOL.var 42])

def sourceBody556_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody556_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([54]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody556_0, 556, 24)) (some 480) ([12, 38, 26, 50, 20]) (some (12, sourceBody556_117, 556, 25))

def sourceBody556_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_118 sourceBody556_3

def sourceBody556_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_119 sourceBody556_0

def sourceBody556_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_116 sourceBody556_120

def sourceBody556_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_115 sourceBody556_121

def sourceBody556_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_114 sourceBody556_122

def sourceBody556_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_113 sourceBody556_123

def sourceBody556_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_112 sourceBody556_124

def sourceBody556_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_125

def sourceBody556_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_126

def sourceBody556_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_111 sourceBody556_127

def sourceBody556_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_128

def sourceBody556_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_129

def sourceBody556_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_99 sourceBody556_130

def sourceBody556_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_131

def sourceBody556_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_132

def sourceBody556_134 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody556_133 sourceBody556_0

def sourceBody556_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_134 sourceBody556_3

def sourceBody556_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_135 sourceBody556_0

def sourceBody556_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_88 sourceBody556_136

def sourceBody556_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_87 sourceBody556_137

def sourceBody556_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_83 sourceBody556_138

def sourceBody556_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_82 sourceBody556_139

def sourceBody556_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_81 sourceBody556_140

def sourceBody556_142 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody556_0, 556, 26)) (some 486) ([30]) (some (30, sourceBody556_67, 556, 27))

def sourceBody556_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_142 sourceBody556_3

def sourceBody556_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_143 sourceBody556_0

def sourceBody556_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_84 sourceBody556_144

def sourceBody556_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_145

def sourceBody556_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_146

def sourceBody556_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_141 sourceBody556_147

def sourceBody556_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody556_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [42]

def sourceBody556_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_150 sourceBody556_0

def sourceBody556_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_149 sourceBody556_151

def sourceBody556_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_148 sourceBody556_152

def sourceBody556_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_65 sourceBody556_153

def sourceBody556_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_154

def sourceBody556_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_155

def sourceBody556_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_51 sourceBody556_156

def sourceBody556_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_157

def sourceBody556_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_158

def sourceBody556_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_159

def sourceBody556_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_160

def sourceBody556_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_31 sourceBody556_161

def sourceBody556_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_162

def sourceBody556_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_163

def sourceBody556_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_25 sourceBody556_164

def sourceBody556_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_165

def sourceBody556_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_166

def sourceBody556_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_13 sourceBody556_167

def sourceBody556_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_168

def sourceBody556_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_169

def sourceBody556_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_170

def sourceBody556_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_171

def sourceBody556_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_172

def sourceBody556_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_173

def sourceBody556_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_174

def sourceBody556_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_175

def sourceBody556_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_9 sourceBody556_176

def sourceBody556_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_177

def sourceBody556_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_178

def sourceBody556_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_179

def sourceBody556_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_180

def sourceBody556_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_181

def sourceBody556_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_182

def sourceBody556_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_183

def sourceBody556_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_184

def sourceBody556_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_5 sourceBody556_185

def sourceBody556_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_186

def sourceBody556_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_187

def sourceBody556_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_188

def sourceBody556_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_189

def sourceBody556_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_190

def sourceBody556_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_191

def sourceBody556_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_192

def sourceBody556_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody556_0 sourceBody556_193

def source556 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (556, 4, sourceBody556_194)
end InitECandidate.Proofs.WordStages
