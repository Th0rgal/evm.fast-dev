import InitECandidate.Proofs.WordStages.Source549
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody565_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody565_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody565_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([14, 38, 8, 32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody565_0, 565, 2)) (some 471) ([]) (some (20, sourceBody565_1, 565, 3))

def sourceBody565_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody565_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_2 sourceBody565_3

def sourceBody565_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_4 sourceBody565_0

def sourceBody565_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody565_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 44, 4, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 4)) (some 471) ([]) (some (18, sourceBody565_6, 565, 5))

def sourceBody565_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_7 sourceBody565_3

def sourceBody565_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_8 sourceBody565_0

def sourceBody565_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody565_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 42, 12, 36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 6)) (some 471) ([]) (some (24, sourceBody565_10, 565, 7))

def sourceBody565_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_11 sourceBody565_3

def sourceBody565_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_12 sourceBody565_0

def sourceBody565_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 18)

def sourceBody565_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 42)

def sourceBody565_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 12)

def sourceBody565_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 36)

def sourceBody565_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody565_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 8)) (some 458) ([48, 2, 26, 16]) (some (48, sourceBody565_18, 565, 9))

def sourceBody565_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_19 sourceBody565_3

def sourceBody565_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_20 sourceBody565_0

def sourceBody565_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_17 sourceBody565_21

def sourceBody565_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_16 sourceBody565_22

def sourceBody565_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_15 sourceBody565_23

def sourceBody565_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_14 sourceBody565_24

def sourceBody565_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 24)

def sourceBody565_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody565_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 10)) (some 461) ([2]) (some (2, sourceBody565_27, 565, 11))

def sourceBody565_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_28 sourceBody565_3

def sourceBody565_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_29 sourceBody565_0

def sourceBody565_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_26 sourceBody565_30

def sourceBody565_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody565_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 38)

def sourceBody565_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody565_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody565_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody565_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 42)

def sourceBody565_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody565_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody565_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody565_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 12)) (some 476) ([16, 40, 10, 34, 22, 46, 6, 30]) (some (16, sourceBody565_40, 565, 13))

def sourceBody565_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_41 sourceBody565_3

def sourceBody565_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_42 sourceBody565_0

def sourceBody565_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_39 sourceBody565_43

def sourceBody565_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_38 sourceBody565_44

def sourceBody565_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_37 sourceBody565_45

def sourceBody565_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_36 sourceBody565_46

def sourceBody565_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_35 sourceBody565_47

def sourceBody565_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_34 sourceBody565_48

def sourceBody565_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_33 sourceBody565_49

def sourceBody565_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_32 sourceBody565_50

def sourceBody565_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 48)

def sourceBody565_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody565_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 34 34 40 10))

def sourceBody565_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 3#64, Flapjack.WordLangExpHOL.var 34])

def sourceBody565_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 2)

def sourceBody565_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody565_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 14)) (some 459) ([22, 46]) (some (40, sourceBody565_57, 565, 15))

def sourceBody565_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_58 sourceBody565_3

def sourceBody565_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_59 sourceBody565_0

def sourceBody565_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_56 sourceBody565_60

def sourceBody565_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_55 sourceBody565_61

def sourceBody565_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_54 sourceBody565_62

def sourceBody565_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_53 sourceBody565_63

def sourceBody565_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_52 sourceBody565_64

def sourceBody565_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody565_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody565_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 16)) (some 466) ([10]) (some (10, sourceBody565_67, 565, 17))

def sourceBody565_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_68 sourceBody565_3

def sourceBody565_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_69 sourceBody565_0

def sourceBody565_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_66 sourceBody565_70

def sourceBody565_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_71

def sourceBody565_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_72

def sourceBody565_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 20)

def sourceBody565_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 44)

def sourceBody565_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody565_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 28)

def sourceBody565_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 18)) (some 458) ([10, 34, 22, 46]) (some (10, sourceBody565_67, 565, 19))

def sourceBody565_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_78 sourceBody565_3

def sourceBody565_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_79 sourceBody565_0

def sourceBody565_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_77 sourceBody565_80

def sourceBody565_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_76 sourceBody565_81

def sourceBody565_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_75 sourceBody565_82

def sourceBody565_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_74 sourceBody565_83

def sourceBody565_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody565_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody565_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody565_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 20)) (some 459) ([34, 22]) (some (34, sourceBody565_87, 565, 21))

def sourceBody565_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_88 sourceBody565_3

def sourceBody565_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_89 sourceBody565_0

def sourceBody565_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_86 sourceBody565_90

def sourceBody565_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_85 sourceBody565_91

def sourceBody565_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
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
        Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody565_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 10)

def sourceBody565_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody565_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody565_97 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 22 (Flapjack.WordRegImm.reg 46) sourceBody565_95 sourceBody565_96

def sourceBody565_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_97 sourceBody565_3

def sourceBody565_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 22)

def sourceBody565_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody565_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 34)

def sourceBody565_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_101 sourceBody565_0

def sourceBody565_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_102 sourceBody565_0

def sourceBody565_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_100 sourceBody565_103

def sourceBody565_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_104

def sourceBody565_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody565_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_106 sourceBody565_87

def sourceBody565_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_105 sourceBody565_107

def sourceBody565_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody565_108 sourceBody565_0

def sourceBody565_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_109 sourceBody565_3

def sourceBody565_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_110 sourceBody565_0

def sourceBody565_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_99 sourceBody565_111

def sourceBody565_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_98 sourceBody565_112

def sourceBody565_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_94 sourceBody565_113

def sourceBody565_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_93 sourceBody565_114

def sourceBody565_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody565_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody565_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 22)) (some 478) ([22]) (some (22, sourceBody565_117, 565, 23))

def sourceBody565_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_118 sourceBody565_3

def sourceBody565_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_119 sourceBody565_0

def sourceBody565_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_116 sourceBody565_120

def sourceBody565_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_121

def sourceBody565_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_122

def sourceBody565_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_115 sourceBody565_123

def sourceBody565_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody565_126 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 46) sourceBody565_95 sourceBody565_96

def sourceBody565_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_126 sourceBody565_3

def sourceBody565_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody565_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 38)

def sourceBody565_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody565_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 32)

def sourceBody565_132 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody565_0, 565, 24)) (some 458) ([22, 46, 6, 30]) (some (22, sourceBody565_117, 565, 25))

def sourceBody565_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_132 sourceBody565_3

def sourceBody565_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_133 sourceBody565_0

def sourceBody565_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_131 sourceBody565_134

def sourceBody565_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_130 sourceBody565_135

def sourceBody565_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_129 sourceBody565_136

def sourceBody565_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_128 sourceBody565_137

def sourceBody565_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
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
      Flapjack.WordLangExpHOL.var 34])

def sourceBody565_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
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
            Flapjack.WordLangExpHOL.const 144#64]),
      Flapjack.WordLangExpHOL.var 40])

def sourceBody565_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody565_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody565_143 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody565_0, 565, 26)) (some 77) ([46, 6, 30]) (some (46, sourceBody565_142, 565, 27))

def sourceBody565_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_143 sourceBody565_3

def sourceBody565_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_144 sourceBody565_0

def sourceBody565_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_141 sourceBody565_145

def sourceBody565_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_140 sourceBody565_146

def sourceBody565_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_139 sourceBody565_147

def sourceBody565_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_148

def sourceBody565_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_149

def sourceBody565_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_138 sourceBody565_150

def sourceBody565_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_151

def sourceBody565_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_152

def sourceBody565_154 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody565_153 sourceBody565_0

def sourceBody565_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_154 sourceBody565_3

def sourceBody565_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_155 sourceBody565_0

def sourceBody565_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_99 sourceBody565_156

def sourceBody565_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_127 sourceBody565_157

def sourceBody565_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_125 sourceBody565_158

def sourceBody565_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_86 sourceBody565_159

def sourceBody565_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_124 sourceBody565_160

def sourceBody565_162 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody565_0, 565, 28)) (some 486) ([22]) (some (22, sourceBody565_117, 565, 29))

def sourceBody565_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_162 sourceBody565_3

def sourceBody565_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_163 sourceBody565_0

def sourceBody565_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_95 sourceBody565_164

def sourceBody565_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_165

def sourceBody565_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_166

def sourceBody565_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_161 sourceBody565_167

def sourceBody565_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody565_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [34]

def sourceBody565_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_170 sourceBody565_0

def sourceBody565_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_169 sourceBody565_171

def sourceBody565_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_168 sourceBody565_172

def sourceBody565_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_92 sourceBody565_173

def sourceBody565_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_174

def sourceBody565_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_175

def sourceBody565_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_84 sourceBody565_176

def sourceBody565_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_177

def sourceBody565_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_178

def sourceBody565_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_73 sourceBody565_179

def sourceBody565_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_65 sourceBody565_180

def sourceBody565_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_181

def sourceBody565_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_182

def sourceBody565_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_51 sourceBody565_183

def sourceBody565_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_184

def sourceBody565_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_185

def sourceBody565_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_186

def sourceBody565_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_187

def sourceBody565_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_31 sourceBody565_188

def sourceBody565_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_189

def sourceBody565_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_190

def sourceBody565_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_25 sourceBody565_191

def sourceBody565_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_192

def sourceBody565_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_193

def sourceBody565_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_13 sourceBody565_194

def sourceBody565_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_195

def sourceBody565_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_196

def sourceBody565_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_197

def sourceBody565_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_198

def sourceBody565_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_199

def sourceBody565_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_200

def sourceBody565_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_201

def sourceBody565_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_202

def sourceBody565_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_9 sourceBody565_203

def sourceBody565_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_204

def sourceBody565_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_205

def sourceBody565_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_206

def sourceBody565_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_207

def sourceBody565_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_208

def sourceBody565_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_209

def sourceBody565_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_210

def sourceBody565_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_211

def sourceBody565_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_5 sourceBody565_212

def sourceBody565_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_213

def sourceBody565_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_214

def sourceBody565_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_215

def sourceBody565_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_216

def sourceBody565_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_217

def sourceBody565_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_218

def sourceBody565_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_219

def sourceBody565_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody565_0 sourceBody565_220

def source565 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (565, 1, sourceBody565_221)
end InitECandidate.Proofs.WordStages
