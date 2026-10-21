import InitECandidate.Proofs.WordStages.Source514
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody530_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody530_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody530_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 50, 10, 42]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody530_0, 530, 2)) (some 471) ([]) (some (26, sourceBody530_1, 530, 3))

def sourceBody530_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody530_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_2 sourceBody530_3

def sourceBody530_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_4 sourceBody530_0

def sourceBody530_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody530_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 58, 6, 38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 4)) (some 471) ([]) (some (22, sourceBody530_6, 530, 5))

def sourceBody530_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_7 sourceBody530_3

def sourceBody530_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_8 sourceBody530_0

def sourceBody530_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody530_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([22, 54, 14, 46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 6)) (some 471) ([]) (some (30, sourceBody530_10, 530, 7))

def sourceBody530_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_11 sourceBody530_3

def sourceBody530_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_12 sourceBody530_0

def sourceBody530_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 22)

def sourceBody530_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 54)

def sourceBody530_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 14)

def sourceBody530_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 46)

def sourceBody530_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 62

def sourceBody530_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 8)) (some 458) ([62, 4, 36, 20]) (some (62, sourceBody530_18, 530, 9))

def sourceBody530_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_19 sourceBody530_3

def sourceBody530_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_20 sourceBody530_0

def sourceBody530_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_17 sourceBody530_21

def sourceBody530_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_16 sourceBody530_22

def sourceBody530_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_15 sourceBody530_23

def sourceBody530_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_14 sourceBody530_24

def sourceBody530_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 30)

def sourceBody530_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody530_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 10)) (some 461) ([4]) (some (4, sourceBody530_27, 530, 11))

def sourceBody530_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_28 sourceBody530_3

def sourceBody530_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_29 sourceBody530_0

def sourceBody530_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_26 sourceBody530_30

def sourceBody530_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody530_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 58)

def sourceBody530_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody530_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 38)

def sourceBody530_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody530_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 54)

def sourceBody530_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody530_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 46)

def sourceBody530_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody530_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 50)

def sourceBody530_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody530_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 42)

def sourceBody530_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody530_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 54)

def sourceBody530_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 14)

def sourceBody530_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 46)

def sourceBody530_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody530_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([4, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 12)) (some 477) ([20, 52, 12, 44, 28, 60, 8, 40, 24, 56, 16, 48, 32, 64, 2, 34]) (some (20, sourceBody530_48, 530, 13))

def sourceBody530_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_49 sourceBody530_3

def sourceBody530_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_50 sourceBody530_0

def sourceBody530_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_47 sourceBody530_51

def sourceBody530_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_46 sourceBody530_52

def sourceBody530_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_45 sourceBody530_53

def sourceBody530_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_44 sourceBody530_54

def sourceBody530_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_43 sourceBody530_55

def sourceBody530_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_42 sourceBody530_56

def sourceBody530_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_41 sourceBody530_57

def sourceBody530_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_40 sourceBody530_58

def sourceBody530_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_39 sourceBody530_59

def sourceBody530_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_38 sourceBody530_60

def sourceBody530_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_37 sourceBody530_61

def sourceBody530_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_36 sourceBody530_62

def sourceBody530_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_35 sourceBody530_63

def sourceBody530_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_34 sourceBody530_64

def sourceBody530_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_33 sourceBody530_65

def sourceBody530_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_32 sourceBody530_66

def sourceBody530_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 62)

def sourceBody530_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody530_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 44 44 52 12))

def sourceBody530_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 3#64, Flapjack.WordLangExpHOL.var 44])

def sourceBody530_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 4)

def sourceBody530_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody530_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 14)) (some 459) ([28, 60]) (some (52, sourceBody530_73, 530, 15))

def sourceBody530_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_74 sourceBody530_3

def sourceBody530_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_75 sourceBody530_0

def sourceBody530_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_72 sourceBody530_76

def sourceBody530_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_71 sourceBody530_77

def sourceBody530_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_70 sourceBody530_78

def sourceBody530_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_69 sourceBody530_79

def sourceBody530_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_68 sourceBody530_80

def sourceBody530_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody530_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody530_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 16)) (some 466) ([12]) (some (12, sourceBody530_83, 530, 17))

def sourceBody530_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_84 sourceBody530_3

def sourceBody530_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_85 sourceBody530_0

def sourceBody530_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_82 sourceBody530_86

def sourceBody530_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_87

def sourceBody530_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_88

def sourceBody530_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 36)

def sourceBody530_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 18)) (some 478) ([12]) (some (12, sourceBody530_83, 530, 19))

def sourceBody530_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_91 sourceBody530_3

def sourceBody530_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_92 sourceBody530_0

def sourceBody530_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_90 sourceBody530_93

def sourceBody530_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_94

def sourceBody530_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_95

def sourceBody530_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_89 sourceBody530_96

def sourceBody530_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody530_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody530_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody530_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody530_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 44) sourceBody530_100 sourceBody530_101

def sourceBody530_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_102 sourceBody530_3

def sourceBody530_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody530_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody530_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 50)

def sourceBody530_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody530_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 42)

def sourceBody530_109 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 20)) (some 458) ([12, 44, 28, 60]) (some (12, sourceBody530_83, 530, 21))

def sourceBody530_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_109 sourceBody530_3

def sourceBody530_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_110 sourceBody530_0

def sourceBody530_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_108 sourceBody530_111

def sourceBody530_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_107 sourceBody530_112

def sourceBody530_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_106 sourceBody530_113

def sourceBody530_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_105 sourceBody530_114

def sourceBody530_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 26)

def sourceBody530_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 58)

def sourceBody530_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 6)

def sourceBody530_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 38)

def sourceBody530_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody530_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 22)) (some 458) ([44, 28, 60, 8]) (some (44, sourceBody530_120, 530, 23))

def sourceBody530_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_121 sourceBody530_3

def sourceBody530_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_122 sourceBody530_0

def sourceBody530_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_119 sourceBody530_123

def sourceBody530_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_118 sourceBody530_124

def sourceBody530_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_117 sourceBody530_125

def sourceBody530_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_116 sourceBody530_126

def sourceBody530_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody530_129 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 24)) (some 69) ([]) (some (28, sourceBody530_128, 530, 25))

def sourceBody530_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_129 sourceBody530_3

def sourceBody530_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_130 sourceBody530_0

def sourceBody530_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 30)

def sourceBody530_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody530_134 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 26)) (some 68) ([60]) (some (60, sourceBody530_133, 530, 27))

def sourceBody530_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_134 sourceBody530_3

def sourceBody530_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_135 sourceBody530_0

def sourceBody530_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_132 sourceBody530_136

def sourceBody530_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody530_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
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
      Flapjack.WordLangExpHOL.var 12])

def sourceBody530_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody530_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody530_142 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 28)) (some 77) ([8, 40, 24]) (some (8, sourceBody530_141, 530, 29))

def sourceBody530_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_142 sourceBody530_3

def sourceBody530_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_143 sourceBody530_0

def sourceBody530_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_140 sourceBody530_144

def sourceBody530_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_139 sourceBody530_145

def sourceBody530_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_138 sourceBody530_146

def sourceBody530_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_147

def sourceBody530_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_148

def sourceBody530_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
      Flapjack.WordLangExpHOL.var 52])

def sourceBody530_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody530_152 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody530_0, 530, 30)) (some 77) ([8, 40, 24]) (some (8, sourceBody530_141, 530, 31))

def sourceBody530_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_152 sourceBody530_3

def sourceBody530_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_153 sourceBody530_0

def sourceBody530_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_140 sourceBody530_154

def sourceBody530_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_151 sourceBody530_155

def sourceBody530_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_150 sourceBody530_156

def sourceBody530_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_157

def sourceBody530_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_158

def sourceBody530_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_149 sourceBody530_159

def sourceBody530_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 44)

def sourceBody530_162 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody530_0, 530, 32)) (some 70) ([8]) (some (8, sourceBody530_141, 530, 33))

def sourceBody530_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_162 sourceBody530_3

def sourceBody530_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_163 sourceBody530_0

def sourceBody530_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_161 sourceBody530_164

def sourceBody530_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_165

def sourceBody530_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_166

def sourceBody530_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_160 sourceBody530_167

def sourceBody530_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_137 sourceBody530_168

def sourceBody530_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_169

def sourceBody530_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_170

def sourceBody530_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_131 sourceBody530_171

def sourceBody530_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_172

def sourceBody530_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_173

def sourceBody530_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_127 sourceBody530_174

def sourceBody530_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_175

def sourceBody530_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_176

def sourceBody530_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_115 sourceBody530_177

def sourceBody530_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_178

def sourceBody530_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_179

def sourceBody530_181 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody530_180 sourceBody530_0

def sourceBody530_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_181 sourceBody530_3

def sourceBody530_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_182 sourceBody530_0

def sourceBody530_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_104 sourceBody530_183

def sourceBody530_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_103 sourceBody530_184

def sourceBody530_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_99 sourceBody530_185

def sourceBody530_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_98 sourceBody530_186

def sourceBody530_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_97 sourceBody530_187

def sourceBody530_189 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody530_0, 530, 34)) (some 486) ([12]) (some (12, sourceBody530_83, 530, 35))

def sourceBody530_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_189 sourceBody530_3

def sourceBody530_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_190 sourceBody530_0

def sourceBody530_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_100 sourceBody530_191

def sourceBody530_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_192

def sourceBody530_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_193

def sourceBody530_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_188 sourceBody530_194

def sourceBody530_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody530_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [52]

def sourceBody530_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_197 sourceBody530_0

def sourceBody530_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_196 sourceBody530_198

def sourceBody530_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_195 sourceBody530_199

def sourceBody530_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_81 sourceBody530_200

def sourceBody530_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_201

def sourceBody530_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_202

def sourceBody530_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_67 sourceBody530_203

def sourceBody530_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_204

def sourceBody530_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_205

def sourceBody530_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_206

def sourceBody530_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_207

def sourceBody530_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_31 sourceBody530_208

def sourceBody530_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_209

def sourceBody530_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_210

def sourceBody530_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_25 sourceBody530_211

def sourceBody530_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_212

def sourceBody530_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_213

def sourceBody530_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_13 sourceBody530_214

def sourceBody530_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_215

def sourceBody530_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_216

def sourceBody530_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_217

def sourceBody530_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_218

def sourceBody530_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_219

def sourceBody530_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_220

def sourceBody530_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_221

def sourceBody530_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_222

def sourceBody530_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_9 sourceBody530_223

def sourceBody530_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_224

def sourceBody530_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_225

def sourceBody530_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_226

def sourceBody530_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_227

def sourceBody530_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_228

def sourceBody530_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_229

def sourceBody530_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_230

def sourceBody530_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_231

def sourceBody530_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_5 sourceBody530_232

def sourceBody530_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_233

def sourceBody530_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_234

def sourceBody530_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_235

def sourceBody530_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_236

def sourceBody530_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_237

def sourceBody530_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_238

def sourceBody530_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_239

def sourceBody530_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody530_0 sourceBody530_240

def source530 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (530, 1, sourceBody530_241)
end InitECandidate.Proofs.WordStages
