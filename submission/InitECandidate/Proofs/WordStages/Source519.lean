import InitECandidate.Proofs.WordStages.Source503
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody519_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody519_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody519_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 40, 8, 34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody519_0, 519, 2)) (some 471) ([]) (some (22, sourceBody519_1, 519, 3))

def sourceBody519_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody519_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_2 sourceBody519_3

def sourceBody519_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_4 sourceBody519_0

def sourceBody519_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody519_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([22, 46, 4, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 4)) (some 471) ([]) (some (18, sourceBody519_6, 519, 5))

def sourceBody519_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_7 sourceBody519_3

def sourceBody519_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_8 sourceBody519_0

def sourceBody519_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 22)

def sourceBody519_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 46)

def sourceBody519_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 4)

def sourceBody519_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody519_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody519_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 6)) (some 458) ([44, 12, 38, 26]) (some (44, sourceBody519_14, 519, 7))

def sourceBody519_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_15 sourceBody519_3

def sourceBody519_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_16 sourceBody519_0

def sourceBody519_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_13 sourceBody519_17

def sourceBody519_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_12 sourceBody519_18

def sourceBody519_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_11 sourceBody519_19

def sourceBody519_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_10 sourceBody519_20

def sourceBody519_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody519_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody519_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 8)) (some 461) ([12]) (some (12, sourceBody519_23, 519, 9))

def sourceBody519_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_24 sourceBody519_3

def sourceBody519_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_25 sourceBody519_0

def sourceBody519_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_22 sourceBody519_26

def sourceBody519_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody519_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 40)

def sourceBody519_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody519_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody519_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody519_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 46)

def sourceBody519_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody519_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 30)

def sourceBody519_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody519_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 10)) (some 476) ([26, 50, 2, 28, 16, 42, 10, 36]) (some (26, sourceBody519_36, 519, 11))

def sourceBody519_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_37 sourceBody519_3

def sourceBody519_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_38 sourceBody519_0

def sourceBody519_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_35 sourceBody519_39

def sourceBody519_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_34 sourceBody519_40

def sourceBody519_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_33 sourceBody519_41

def sourceBody519_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_32 sourceBody519_42

def sourceBody519_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_31 sourceBody519_43

def sourceBody519_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_30 sourceBody519_44

def sourceBody519_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_29 sourceBody519_45

def sourceBody519_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_28 sourceBody519_46

def sourceBody519_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 44)

def sourceBody519_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody519_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 28 28 50 2))

def sourceBody519_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 30#64, Flapjack.WordLangExpHOL.var 28])

def sourceBody519_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody519_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody519_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 12)) (some 459) ([16, 42]) (some (50, sourceBody519_53, 519, 13))

def sourceBody519_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_54 sourceBody519_3

def sourceBody519_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_55 sourceBody519_0

def sourceBody519_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_52 sourceBody519_56

def sourceBody519_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_51 sourceBody519_57

def sourceBody519_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_50 sourceBody519_58

def sourceBody519_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_49 sourceBody519_59

def sourceBody519_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_48 sourceBody519_60

def sourceBody519_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 26)

def sourceBody519_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody519_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 14)) (some 466) ([2]) (some (2, sourceBody519_63, 519, 15))

def sourceBody519_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_64 sourceBody519_3

def sourceBody519_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_65 sourceBody519_0

def sourceBody519_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_62 sourceBody519_66

def sourceBody519_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_67

def sourceBody519_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_68

def sourceBody519_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 38)

def sourceBody519_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 16)) (some 478) ([2]) (some (2, sourceBody519_63, 519, 17))

def sourceBody519_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_71 sourceBody519_3

def sourceBody519_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_72 sourceBody519_0

def sourceBody519_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_70 sourceBody519_73

def sourceBody519_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_74

def sourceBody519_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_75

def sourceBody519_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_69 sourceBody519_76

def sourceBody519_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 18)) (some 69) ([]) (some (2, sourceBody519_63, 519, 19))

def sourceBody519_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_78 sourceBody519_3

def sourceBody519_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_79 sourceBody519_0

def sourceBody519_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody519_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody519_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 20)) (some 68) ([28]) (some (28, sourceBody519_82, 519, 21))

def sourceBody519_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_83 sourceBody519_3

def sourceBody519_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_84 sourceBody519_0

def sourceBody519_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_81 sourceBody519_85

def sourceBody519_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody519_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody519_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody519_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 34)

def sourceBody519_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody519_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 22)) (some 458) ([16, 42, 10, 36]) (some (16, sourceBody519_91, 519, 23))

def sourceBody519_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_92 sourceBody519_3

def sourceBody519_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_93 sourceBody519_0

def sourceBody519_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_90 sourceBody519_94

def sourceBody519_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_89 sourceBody519_95

def sourceBody519_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_88 sourceBody519_96

def sourceBody519_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_87 sourceBody519_97

def sourceBody519_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
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
      Flapjack.WordLangExpHOL.var 28])

def sourceBody519_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody519_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 2)

def sourceBody519_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody519_103 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 24)) (some 158) ([42, 10, 36]) (some (42, sourceBody519_102, 519, 25))

def sourceBody519_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_103 sourceBody519_3

def sourceBody519_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_104 sourceBody519_0

def sourceBody519_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_101 sourceBody519_105

def sourceBody519_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_100 sourceBody519_106

def sourceBody519_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_99 sourceBody519_107

def sourceBody519_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_108

def sourceBody519_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_109

def sourceBody519_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody519_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody519_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody519_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 42, 10, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 26)) (some 146) ([24, 48]) (some (24, sourceBody519_113, 519, 27))

def sourceBody519_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_114 sourceBody519_3

def sourceBody519_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_115 sourceBody519_0

def sourceBody519_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_112 sourceBody519_116

def sourceBody519_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_111 sourceBody519_117

def sourceBody519_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 50)

def sourceBody519_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody519_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody519_0, 519, 28)) (some 70) ([48]) (some (48, sourceBody519_120, 519, 29))

def sourceBody519_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_121 sourceBody519_3

def sourceBody519_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_122 sourceBody519_0

def sourceBody519_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_119 sourceBody519_123

def sourceBody519_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_124

def sourceBody519_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_125

def sourceBody519_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 16)

def sourceBody519_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 42)

def sourceBody519_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody519_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 36)

def sourceBody519_131 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody519_0, 519, 30)) (some 472) ([48, 6, 32, 20]) (some (48, sourceBody519_120, 519, 31))

def sourceBody519_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_131 sourceBody519_3

def sourceBody519_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_132 sourceBody519_0

def sourceBody519_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_130 sourceBody519_133

def sourceBody519_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_129 sourceBody519_134

def sourceBody519_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_128 sourceBody519_135

def sourceBody519_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_127 sourceBody519_136

def sourceBody519_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_137

def sourceBody519_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_138

def sourceBody519_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_126 sourceBody519_139

def sourceBody519_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody519_142 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody519_0, 519, 32)) (some 486) ([48]) (some (48, sourceBody519_120, 519, 33))

def sourceBody519_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_142 sourceBody519_3

def sourceBody519_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_143 sourceBody519_0

def sourceBody519_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_141 sourceBody519_144

def sourceBody519_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_145

def sourceBody519_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_146

def sourceBody519_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_140 sourceBody519_147

def sourceBody519_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody519_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody519_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_150 sourceBody519_0

def sourceBody519_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_149 sourceBody519_151

def sourceBody519_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_148 sourceBody519_152

def sourceBody519_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_118 sourceBody519_153

def sourceBody519_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_154

def sourceBody519_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_155

def sourceBody519_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_156

def sourceBody519_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_157

def sourceBody519_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_158

def sourceBody519_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_159

def sourceBody519_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_160

def sourceBody519_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_161

def sourceBody519_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_110 sourceBody519_162

def sourceBody519_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_98 sourceBody519_163

def sourceBody519_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_164

def sourceBody519_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_165

def sourceBody519_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_86 sourceBody519_166

def sourceBody519_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_167

def sourceBody519_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_168

def sourceBody519_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_80 sourceBody519_169

def sourceBody519_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_170

def sourceBody519_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_171

def sourceBody519_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_77 sourceBody519_172

def sourceBody519_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_61 sourceBody519_173

def sourceBody519_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_174

def sourceBody519_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_175

def sourceBody519_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_47 sourceBody519_176

def sourceBody519_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_177

def sourceBody519_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_178

def sourceBody519_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_179

def sourceBody519_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_180

def sourceBody519_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_27 sourceBody519_181

def sourceBody519_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_182

def sourceBody519_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_183

def sourceBody519_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_21 sourceBody519_184

def sourceBody519_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_185

def sourceBody519_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_186

def sourceBody519_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_9 sourceBody519_187

def sourceBody519_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_188

def sourceBody519_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_189

def sourceBody519_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_190

def sourceBody519_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_191

def sourceBody519_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_192

def sourceBody519_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_193

def sourceBody519_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_194

def sourceBody519_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_195

def sourceBody519_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_5 sourceBody519_196

def sourceBody519_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_197

def sourceBody519_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_198

def sourceBody519_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_199

def sourceBody519_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_200

def sourceBody519_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_201

def sourceBody519_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_202

def sourceBody519_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_203

def sourceBody519_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody519_0 sourceBody519_204

def source519 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (519, 1, sourceBody519_205)
end InitECandidate.Proofs.WordStages
