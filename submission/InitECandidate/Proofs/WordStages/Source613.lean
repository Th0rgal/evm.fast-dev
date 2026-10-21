import InitECandidate.Proofs.WordStages.Source597
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody613_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody613_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody613_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody613_0, 613, 2)) (some 488) ([]) (some (46, sourceBody613_1, 613, 3))

def sourceBody613_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody613_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_2 sourceBody613_3

def sourceBody613_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_4 sourceBody613_0

def sourceBody613_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_5

def sourceBody613_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_6

def sourceBody613_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody613_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 46, 8, 38]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody613_0, 613, 4)) (some 471) ([]) (some (24, sourceBody613_8, 613, 5))

def sourceBody613_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_9 sourceBody613_3

def sourceBody613_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_10 sourceBody613_0

def sourceBody613_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody613_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 54, 4, 34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 6)) (some 471) ([]) (some (20, sourceBody613_12, 613, 7))

def sourceBody613_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_13 sourceBody613_3

def sourceBody613_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_14 sourceBody613_0

def sourceBody613_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody613_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 50, 12, 42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 8)) (some 471) ([]) (some (28, sourceBody613_16, 613, 9))

def sourceBody613_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_17 sourceBody613_3

def sourceBody613_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_18 sourceBody613_0

def sourceBody613_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 20)

def sourceBody613_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 50)

def sourceBody613_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody613_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 42)

def sourceBody613_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody613_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 10)) (some 458) ([58, 2, 32, 18]) (some (58, sourceBody613_24, 613, 11))

def sourceBody613_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_25 sourceBody613_3

def sourceBody613_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_26 sourceBody613_0

def sourceBody613_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_23 sourceBody613_27

def sourceBody613_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_22 sourceBody613_28

def sourceBody613_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_21 sourceBody613_29

def sourceBody613_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_20 sourceBody613_30

def sourceBody613_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody613_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 54)

def sourceBody613_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 4)

def sourceBody613_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 34)

def sourceBody613_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody613_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 50)

def sourceBody613_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 12)

def sourceBody613_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 42)

def sourceBody613_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody613_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([58, 2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 12)) (some 476) ([32, 18, 48, 10, 40, 26, 56, 6]) (some (32, sourceBody613_40, 613, 13))

def sourceBody613_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_41 sourceBody613_3

def sourceBody613_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_42 sourceBody613_0

def sourceBody613_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_39 sourceBody613_43

def sourceBody613_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_38 sourceBody613_44

def sourceBody613_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_37 sourceBody613_45

def sourceBody613_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_36 sourceBody613_46

def sourceBody613_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_35 sourceBody613_47

def sourceBody613_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_34 sourceBody613_48

def sourceBody613_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_33 sourceBody613_49

def sourceBody613_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_32 sourceBody613_50

def sourceBody613_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody613_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody613_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 14)) (some 461) ([18]) (some (18, sourceBody613_53, 613, 15))

def sourceBody613_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_54 sourceBody613_3

def sourceBody613_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_55 sourceBody613_0

def sourceBody613_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_52 sourceBody613_56

def sourceBody613_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 12000#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody613_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 58)

def sourceBody613_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody613_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 16)) (some 459) ([48, 10]) (some (48, sourceBody613_60, 613, 17))

def sourceBody613_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_61 sourceBody613_3

def sourceBody613_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_62 sourceBody613_0

def sourceBody613_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_59 sourceBody613_63

def sourceBody613_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_58 sourceBody613_64

def sourceBody613_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody613_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody613_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 18)) (some 466) ([10]) (some (10, sourceBody613_67, 613, 19))

def sourceBody613_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_68 sourceBody613_3

def sourceBody613_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_69 sourceBody613_0

def sourceBody613_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_66 sourceBody613_70

def sourceBody613_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_71

def sourceBody613_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_72

def sourceBody613_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody613_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 20)) (some 478) ([10]) (some (10, sourceBody613_67, 613, 21))

def sourceBody613_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_75 sourceBody613_3

def sourceBody613_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_76 sourceBody613_0

def sourceBody613_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_74 sourceBody613_77

def sourceBody613_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_78

def sourceBody613_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_79

def sourceBody613_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_73 sourceBody613_80

def sourceBody613_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody613_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody613_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody613_85 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 22)) (some 403) ([40]) (some (40, sourceBody613_84, 613, 23))

def sourceBody613_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_85 sourceBody613_3

def sourceBody613_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_86 sourceBody613_0

def sourceBody613_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_83 sourceBody613_87

def sourceBody613_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody613_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody613_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 24)) (some 68) ([26]) (some (26, sourceBody613_90, 613, 25))

def sourceBody613_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_91 sourceBody613_3

def sourceBody613_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_92 sourceBody613_0

def sourceBody613_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_89 sourceBody613_93

def sourceBody613_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody613_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody613_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 40)

def sourceBody613_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody613_99 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 26)) (some 610) ([56, 6, 36]) (some (56, sourceBody613_98, 613, 27))

def sourceBody613_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_99 sourceBody613_3

def sourceBody613_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_100 sourceBody613_0

def sourceBody613_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_97 sourceBody613_101

def sourceBody613_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_96 sourceBody613_102

def sourceBody613_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_95 sourceBody613_103

def sourceBody613_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_104

def sourceBody613_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_105

def sourceBody613_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 24)

def sourceBody613_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 54)

def sourceBody613_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 4)

def sourceBody613_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 34)

def sourceBody613_111 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody613_0, 613, 28)) (some 458) ([56, 6, 36, 22]) (some (56, sourceBody613_98, 613, 29))

def sourceBody613_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_111 sourceBody613_3

def sourceBody613_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_112 sourceBody613_0

def sourceBody613_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_110 sourceBody613_113

def sourceBody613_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_109 sourceBody613_114

def sourceBody613_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_108 sourceBody613_115

def sourceBody613_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_107 sourceBody613_116

def sourceBody613_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody613_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 46)

def sourceBody613_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody613_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 38)

def sourceBody613_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 40)

def sourceBody613_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 26)

def sourceBody613_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 28)

def sourceBody613_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody613_126 : WordLangProgHOL (BitVec 64) :=
.call (some (([56]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody613_0, 613, 30)) (some 612) ([6, 36, 22, 52, 14, 44, 30]) (some (6, sourceBody613_125, 613, 31))

def sourceBody613_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_126 sourceBody613_3

def sourceBody613_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_127 sourceBody613_0

def sourceBody613_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_124 sourceBody613_128

def sourceBody613_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_123 sourceBody613_129

def sourceBody613_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_122 sourceBody613_130

def sourceBody613_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_121 sourceBody613_131

def sourceBody613_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_120 sourceBody613_132

def sourceBody613_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_119 sourceBody613_133

def sourceBody613_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_118 sourceBody613_134

def sourceBody613_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 56)

def sourceBody613_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody613_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody613_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody613_140 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 36 (Flapjack.WordRegImm.reg 22) sourceBody613_138 sourceBody613_139

def sourceBody613_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_140 sourceBody613_3

def sourceBody613_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 36)

def sourceBody613_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody613_144 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody613_0, 613, 32)) (some 486) ([36]) (some (36, sourceBody613_143, 613, 33))

def sourceBody613_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_144 sourceBody613_3

def sourceBody613_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_145 sourceBody613_0

def sourceBody613_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_138 sourceBody613_146

def sourceBody613_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_147

def sourceBody613_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_148

def sourceBody613_150 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 52 (Flapjack.WordRegImm.imm 0#64) sourceBody613_149 sourceBody613_0

def sourceBody613_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_150 sourceBody613_3

def sourceBody613_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_151 sourceBody613_0

def sourceBody613_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_142 sourceBody613_152

def sourceBody613_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_141 sourceBody613_153

def sourceBody613_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_137 sourceBody613_154

def sourceBody613_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_136 sourceBody613_155

def sourceBody613_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody613_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody613_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_158 sourceBody613_0

def sourceBody613_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_157 sourceBody613_159

def sourceBody613_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_156 sourceBody613_160

def sourceBody613_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_135 sourceBody613_161

def sourceBody613_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_162

def sourceBody613_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_163

def sourceBody613_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_117 sourceBody613_164

def sourceBody613_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_165

def sourceBody613_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_166

def sourceBody613_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_106 sourceBody613_167

def sourceBody613_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_94 sourceBody613_168

def sourceBody613_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_169

def sourceBody613_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_170

def sourceBody613_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_88 sourceBody613_171

def sourceBody613_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_172

def sourceBody613_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_173

def sourceBody613_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_82 sourceBody613_174

def sourceBody613_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_175

def sourceBody613_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_81 sourceBody613_176

def sourceBody613_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_65 sourceBody613_177

def sourceBody613_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_178

def sourceBody613_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_179

def sourceBody613_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_57 sourceBody613_180

def sourceBody613_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_181

def sourceBody613_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_182

def sourceBody613_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_51 sourceBody613_183

def sourceBody613_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_184

def sourceBody613_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_185

def sourceBody613_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_186

def sourceBody613_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_187

def sourceBody613_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_31 sourceBody613_188

def sourceBody613_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_189

def sourceBody613_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_190

def sourceBody613_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_19 sourceBody613_191

def sourceBody613_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_192

def sourceBody613_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_193

def sourceBody613_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_194

def sourceBody613_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_195

def sourceBody613_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_196

def sourceBody613_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_197

def sourceBody613_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_198

def sourceBody613_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_199

def sourceBody613_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_15 sourceBody613_200

def sourceBody613_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_201

def sourceBody613_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_202

def sourceBody613_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_203

def sourceBody613_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_204

def sourceBody613_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_205

def sourceBody613_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_206

def sourceBody613_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_207

def sourceBody613_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_208

def sourceBody613_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_11 sourceBody613_209

def sourceBody613_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_210

def sourceBody613_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_211

def sourceBody613_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_212

def sourceBody613_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_213

def sourceBody613_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_214

def sourceBody613_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_215

def sourceBody613_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_216

def sourceBody613_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_0 sourceBody613_217

def sourceBody613_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody613_7 sourceBody613_218

def source613 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (613, 1, sourceBody613_219)
end InitECandidate.Proofs.WordStages
