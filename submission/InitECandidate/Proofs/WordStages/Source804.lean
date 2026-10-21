import InitECandidate.Proofs.WordStages.Source788
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody804_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody804_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody804_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 2)) (some 69) ([]) (some (22, sourceBody804_1, 804, 3))

def sourceBody804_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody804_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_2 sourceBody804_3

def sourceBody804_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_4 sourceBody804_0

def sourceBody804_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody804_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody804_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 4)) (some 68) ([38]) (some (38, sourceBody804_7, 804, 5))

def sourceBody804_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_8 sourceBody804_3

def sourceBody804_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_9 sourceBody804_0

def sourceBody804_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_6 sourceBody804_10

def sourceBody804_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody804_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody804_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 6)) (some 68) ([12]) (some (12, sourceBody804_13, 804, 7))

def sourceBody804_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_14 sourceBody804_3

def sourceBody804_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_15 sourceBody804_0

def sourceBody804_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_12 sourceBody804_16

def sourceBody804_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody804_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody804_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 8)) (some 68) ([28]) (some (28, sourceBody804_19, 804, 9))

def sourceBody804_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_20 sourceBody804_3

def sourceBody804_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_21 sourceBody804_0

def sourceBody804_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_18 sourceBody804_22

def sourceBody804_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody804_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody804_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 10)) (some 68) ([20]) (some (20, sourceBody804_25, 804, 11))

def sourceBody804_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_26 sourceBody804_3

def sourceBody804_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_27 sourceBody804_0

def sourceBody804_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_24 sourceBody804_28

def sourceBody804_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 144#64)

def sourceBody804_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody804_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 12)) (some 68) ([36]) (some (36, sourceBody804_31, 804, 13))

def sourceBody804_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_32 sourceBody804_3

def sourceBody804_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_33 sourceBody804_0

def sourceBody804_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_30 sourceBody804_34

def sourceBody804_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 288#64)

def sourceBody804_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody804_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 14)) (some 68) ([16]) (some (16, sourceBody804_37, 804, 15))

def sourceBody804_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_38 sourceBody804_3

def sourceBody804_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_39 sourceBody804_0

def sourceBody804_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_36 sourceBody804_40

def sourceBody804_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody804_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody804_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 16)) (some 68) ([32]) (some (32, sourceBody804_43, 804, 17))

def sourceBody804_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_44 sourceBody804_3

def sourceBody804_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_45 sourceBody804_0

def sourceBody804_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_42 sourceBody804_46

def sourceBody804_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody804_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 480#64])

def sourceBody804_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody804_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 18)) (some 725) ([24, 40]) (some (24, sourceBody804_50, 804, 19))

def sourceBody804_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_51 sourceBody804_3

def sourceBody804_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_52 sourceBody804_0

def sourceBody804_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_49 sourceBody804_53

def sourceBody804_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_48 sourceBody804_54

def sourceBody804_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_55

def sourceBody804_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_56

def sourceBody804_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody804_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 576#64])

def sourceBody804_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 20)) (some 725) ([24, 40]) (some (24, sourceBody804_50, 804, 21))

def sourceBody804_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_60 sourceBody804_3

def sourceBody804_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_61 sourceBody804_0

def sourceBody804_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_59 sourceBody804_62

def sourceBody804_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_58 sourceBody804_63

def sourceBody804_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_64

def sourceBody804_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_65

def sourceBody804_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_57 sourceBody804_66

def sourceBody804_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody804_69 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 22)) (some 727) ([24]) (some (24, sourceBody804_50, 804, 23))

def sourceBody804_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_69 sourceBody804_3

def sourceBody804_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_70 sourceBody804_0

def sourceBody804_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_68 sourceBody804_71

def sourceBody804_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_72

def sourceBody804_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_73

def sourceBody804_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_67 sourceBody804_74

def sourceBody804_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody804_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 22)

def sourceBody804_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 24)) (some 803) ([24, 40]) (some (24, sourceBody804_50, 804, 25))

def sourceBody804_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_78 sourceBody804_3

def sourceBody804_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_79 sourceBody804_0

def sourceBody804_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_77 sourceBody804_80

def sourceBody804_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_76 sourceBody804_81

def sourceBody804_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_82

def sourceBody804_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_83

def sourceBody804_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_75 sourceBody804_84

def sourceBody804_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody804_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 12)

def sourceBody804_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody804_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody804_90 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 26)) (some 780) ([24, 40, 10, 26]) (some (24, sourceBody804_50, 804, 27))

def sourceBody804_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_90 sourceBody804_3

def sourceBody804_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_91 sourceBody804_0

def sourceBody804_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_89 sourceBody804_92

def sourceBody804_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_88 sourceBody804_93

def sourceBody804_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_87 sourceBody804_94

def sourceBody804_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_86 sourceBody804_95

def sourceBody804_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_96

def sourceBody804_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_97

def sourceBody804_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_85 sourceBody804_98

def sourceBody804_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody804_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 672#64])

def sourceBody804_102 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 28)) (some 725) ([24, 40]) (some (24, sourceBody804_50, 804, 29))

def sourceBody804_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_102 sourceBody804_3

def sourceBody804_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_103 sourceBody804_0

def sourceBody804_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_101 sourceBody804_104

def sourceBody804_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_100 sourceBody804_105

def sourceBody804_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_106

def sourceBody804_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_107

def sourceBody804_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_99 sourceBody804_108

def sourceBody804_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody804_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 768#64])

def sourceBody804_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 30)) (some 725) ([24, 40]) (some (24, sourceBody804_50, 804, 31))

def sourceBody804_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_112 sourceBody804_3

def sourceBody804_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_113 sourceBody804_0

def sourceBody804_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_111 sourceBody804_114

def sourceBody804_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_110 sourceBody804_115

def sourceBody804_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_116

def sourceBody804_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_117

def sourceBody804_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_109 sourceBody804_118

def sourceBody804_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody804_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 32)) (some 727) ([24]) (some (24, sourceBody804_50, 804, 33))

def sourceBody804_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_121 sourceBody804_3

def sourceBody804_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_122 sourceBody804_0

def sourceBody804_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_120 sourceBody804_123

def sourceBody804_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_124

def sourceBody804_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_125

def sourceBody804_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_119 sourceBody804_126

def sourceBody804_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody804_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 36)

def sourceBody804_130 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 34)) (some 779) ([24, 40, 10]) (some (24, sourceBody804_50, 804, 35))

def sourceBody804_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_130 sourceBody804_3

def sourceBody804_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_131 sourceBody804_0

def sourceBody804_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_129 sourceBody804_132

def sourceBody804_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_128 sourceBody804_133

def sourceBody804_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_86 sourceBody804_134

def sourceBody804_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_135

def sourceBody804_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_136

def sourceBody804_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_127 sourceBody804_137

def sourceBody804_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 38)

def sourceBody804_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 384#64])

def sourceBody804_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody804_142 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 36)) (some 77) ([24, 40, 10]) (some (24, sourceBody804_50, 804, 37))

def sourceBody804_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_142 sourceBody804_3

def sourceBody804_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_143 sourceBody804_0

def sourceBody804_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_141 sourceBody804_144

def sourceBody804_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_140 sourceBody804_145

def sourceBody804_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_139 sourceBody804_146

def sourceBody804_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_147

def sourceBody804_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_148

def sourceBody804_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_138 sourceBody804_149

def sourceBody804_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody804_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 432#64])

def sourceBody804_153 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 38)) (some 77) ([24, 40, 10]) (some (24, sourceBody804_50, 804, 39))

def sourceBody804_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_153 sourceBody804_3

def sourceBody804_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_154 sourceBody804_0

def sourceBody804_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_141 sourceBody804_155

def sourceBody804_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_152 sourceBody804_156

def sourceBody804_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_151 sourceBody804_157

def sourceBody804_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_158

def sourceBody804_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_159

def sourceBody804_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_150 sourceBody804_160

def sourceBody804_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody804_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 8505329371266088957#64)

def sourceBody804_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 17002214543764226050#64)

def sourceBody804_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6865905132761471162#64)

def sourceBody804_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 8632934651105793861#64)

def sourceBody804_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 6631298214892334189#64)

def sourceBody804_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1582556514881692819#64)

def sourceBody804_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody804_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 14

def sourceBody804_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_170 sourceBody804_0

def sourceBody804_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_169 sourceBody804_171

def sourceBody804_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 40)

def sourceBody804_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 8#64])
  14

def sourceBody804_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_174 sourceBody804_0

def sourceBody804_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_173 sourceBody804_175

def sourceBody804_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody804_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 16#64])
  14

def sourceBody804_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_178 sourceBody804_0

def sourceBody804_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_177 sourceBody804_179

def sourceBody804_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 26)

def sourceBody804_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 24#64])
  14

def sourceBody804_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_182 sourceBody804_0

def sourceBody804_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_181 sourceBody804_183

def sourceBody804_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody804_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 32#64])
  14

def sourceBody804_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_186 sourceBody804_0

def sourceBody804_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_185 sourceBody804_187

def sourceBody804_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 34)

def sourceBody804_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 40#64])
  14

def sourceBody804_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_190 sourceBody804_0

def sourceBody804_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_189 sourceBody804_191

def sourceBody804_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_192 sourceBody804_0

def sourceBody804_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_188 sourceBody804_193

def sourceBody804_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_184 sourceBody804_194

def sourceBody804_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_180 sourceBody804_195

def sourceBody804_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_176 sourceBody804_196

def sourceBody804_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_172 sourceBody804_197

def sourceBody804_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_168 sourceBody804_198

def sourceBody804_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_199

def sourceBody804_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_167 sourceBody804_200

def sourceBody804_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_201

def sourceBody804_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_166 sourceBody804_202

def sourceBody804_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_203

def sourceBody804_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_165 sourceBody804_204

def sourceBody804_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_205

def sourceBody804_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_164 sourceBody804_206

def sourceBody804_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_207

def sourceBody804_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_163 sourceBody804_208

def sourceBody804_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_209

def sourceBody804_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_162 sourceBody804_210

def sourceBody804_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_211

def sourceBody804_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_161 sourceBody804_212

def sourceBody804_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody804_215 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 40)) (some 803) ([24, 40]) (some (24, sourceBody804_50, 804, 41))

def sourceBody804_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_215 sourceBody804_3

def sourceBody804_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_216 sourceBody804_0

def sourceBody804_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_77 sourceBody804_217

def sourceBody804_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_214 sourceBody804_218

def sourceBody804_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_219

def sourceBody804_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_220

def sourceBody804_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_213 sourceBody804_221

def sourceBody804_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody804_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 38)

def sourceBody804_225 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 42)) (some 768) ([24, 40, 10, 26]) (some (24, sourceBody804_50, 804, 43))

def sourceBody804_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_225 sourceBody804_3

def sourceBody804_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_226 sourceBody804_0

def sourceBody804_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_89 sourceBody804_227

def sourceBody804_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_88 sourceBody804_228

def sourceBody804_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_224 sourceBody804_229

def sourceBody804_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_223 sourceBody804_230

def sourceBody804_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_231

def sourceBody804_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_232

def sourceBody804_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_222 sourceBody804_233

def sourceBody804_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody804_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 20)

def sourceBody804_237 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 44)) (some 767) ([24, 40, 10]) (some (24, sourceBody804_50, 804, 45))

def sourceBody804_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_237 sourceBody804_3

def sourceBody804_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_238 sourceBody804_0

def sourceBody804_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_236 sourceBody804_239

def sourceBody804_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_235 sourceBody804_240

def sourceBody804_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_223 sourceBody804_241

def sourceBody804_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_242

def sourceBody804_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_243

def sourceBody804_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_234 sourceBody804_244

def sourceBody804_246 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 46)) (some 777) ([24, 40]) (some (24, sourceBody804_50, 804, 47))

def sourceBody804_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_246 sourceBody804_3

def sourceBody804_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_247 sourceBody804_0

def sourceBody804_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_87 sourceBody804_248

def sourceBody804_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_48 sourceBody804_249

def sourceBody804_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_250

def sourceBody804_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_251

def sourceBody804_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_245 sourceBody804_252

def sourceBody804_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody804_255 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 48)) (some 752) ([24]) (some (24, sourceBody804_50, 804, 49))

def sourceBody804_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_255 sourceBody804_3

def sourceBody804_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_256 sourceBody804_0

def sourceBody804_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_254 sourceBody804_257

def sourceBody804_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_258

def sourceBody804_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_259

def sourceBody804_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_253 sourceBody804_260

def sourceBody804_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody804_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody804_264 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 50)) (some 790) ([24, 40, 10]) (some (24, sourceBody804_50, 804, 51))

def sourceBody804_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_264 sourceBody804_3

def sourceBody804_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_265 sourceBody804_0

def sourceBody804_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_263 sourceBody804_266

def sourceBody804_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_262 sourceBody804_267

def sourceBody804_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_254 sourceBody804_268

def sourceBody804_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_269

def sourceBody804_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_270

def sourceBody804_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_261 sourceBody804_271

def sourceBody804_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 8)

def sourceBody804_274 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 52)) (some 790) ([24, 40, 10]) (some (24, sourceBody804_50, 804, 53))

def sourceBody804_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_274 sourceBody804_3

def sourceBody804_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_275 sourceBody804_0

def sourceBody804_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_129 sourceBody804_276

def sourceBody804_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_273 sourceBody804_277

def sourceBody804_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_254 sourceBody804_278

def sourceBody804_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_279

def sourceBody804_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_280

def sourceBody804_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_272 sourceBody804_281

def sourceBody804_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody804_284 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 54)) (some 761) ([24, 40]) (some (24, sourceBody804_50, 804, 55))

def sourceBody804_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_284 sourceBody804_3

def sourceBody804_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_285 sourceBody804_0

def sourceBody804_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_283 sourceBody804_286

def sourceBody804_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_254 sourceBody804_287

def sourceBody804_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_288

def sourceBody804_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_289

def sourceBody804_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_282 sourceBody804_290

def sourceBody804_292 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 56)) (some 753) ([24]) (some (24, sourceBody804_50, 804, 57))

def sourceBody804_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_292 sourceBody804_3

def sourceBody804_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_293 sourceBody804_0

def sourceBody804_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_254 sourceBody804_294

def sourceBody804_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 30)

def sourceBody804_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody804_298 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody804_0, 804, 58)) (some 70) ([40]) (some (40, sourceBody804_297, 804, 59))

def sourceBody804_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_298 sourceBody804_3

def sourceBody804_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_299 sourceBody804_0

def sourceBody804_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_296 sourceBody804_300

def sourceBody804_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_301

def sourceBody804_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_302

def sourceBody804_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 32)

def sourceBody804_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody804_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_305 sourceBody804_0

def sourceBody804_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_304 sourceBody804_306

def sourceBody804_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_303 sourceBody804_307

def sourceBody804_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_295 sourceBody804_308

def sourceBody804_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_309

def sourceBody804_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_310

def sourceBody804_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_291 sourceBody804_311

def sourceBody804_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_47 sourceBody804_312

def sourceBody804_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_313

def sourceBody804_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_314

def sourceBody804_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_41 sourceBody804_315

def sourceBody804_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_316

def sourceBody804_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_317

def sourceBody804_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_35 sourceBody804_318

def sourceBody804_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_319

def sourceBody804_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_320

def sourceBody804_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_29 sourceBody804_321

def sourceBody804_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_322

def sourceBody804_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_323

def sourceBody804_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_23 sourceBody804_324

def sourceBody804_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_325

def sourceBody804_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_326

def sourceBody804_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_17 sourceBody804_327

def sourceBody804_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_328

def sourceBody804_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_329

def sourceBody804_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_11 sourceBody804_330

def sourceBody804_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_331

def sourceBody804_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_332

def sourceBody804_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_5 sourceBody804_333

def sourceBody804_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_334

def sourceBody804_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody804_0 sourceBody804_335

def source804 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (804, 5, sourceBody804_336)
end InitECandidate.Proofs.WordStages
