import InitECandidate.Proofs.WordStages.Source766
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody782_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody782_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody782_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 2)) (some 69) ([]) (some (8, sourceBody782_1, 782, 3))

def sourceBody782_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody782_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_2 sourceBody782_3

def sourceBody782_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_4 sourceBody782_0

def sourceBody782_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody782_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody782_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 4)) (some 68) ([14]) (some (14, sourceBody782_7, 782, 5))

def sourceBody782_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_8 sourceBody782_3

def sourceBody782_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_9 sourceBody782_0

def sourceBody782_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_6 sourceBody782_10

def sourceBody782_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody782_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody782_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 6)) (some 68) ([10]) (some (10, sourceBody782_13, 782, 7))

def sourceBody782_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_14 sourceBody782_3

def sourceBody782_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_15 sourceBody782_0

def sourceBody782_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_12 sourceBody782_16

def sourceBody782_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody782_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody782_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody782_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 8)) (some 736) ([18, 6]) (some (18, sourceBody782_20, 782, 9))

def sourceBody782_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_21 sourceBody782_3

def sourceBody782_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_22 sourceBody782_0

def sourceBody782_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_19 sourceBody782_23

def sourceBody782_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_18 sourceBody782_24

def sourceBody782_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_25

def sourceBody782_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_26

def sourceBody782_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody782_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody782_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 10)) (some 736) ([18, 6]) (some (18, sourceBody782_20, 782, 11))

def sourceBody782_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_30 sourceBody782_3

def sourceBody782_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_31 sourceBody782_0

def sourceBody782_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_29 sourceBody782_32

def sourceBody782_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_28 sourceBody782_33

def sourceBody782_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_34

def sourceBody782_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_35

def sourceBody782_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_27 sourceBody782_36

def sourceBody782_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody782_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody782_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 12)) (some 735) ([18, 6, 12]) (some (18, sourceBody782_20, 782, 13))

def sourceBody782_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_40 sourceBody782_3

def sourceBody782_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_41 sourceBody782_0

def sourceBody782_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_39 sourceBody782_42

def sourceBody782_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_38 sourceBody782_43

def sourceBody782_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_28 sourceBody782_44

def sourceBody782_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_45

def sourceBody782_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_46

def sourceBody782_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_37 sourceBody782_47

def sourceBody782_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 288#64])

def sourceBody782_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 14)) (some 730) ([18, 6, 12]) (some (18, sourceBody782_20, 782, 15))

def sourceBody782_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_50 sourceBody782_3

def sourceBody782_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_51 sourceBody782_0

def sourceBody782_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_49 sourceBody782_52

def sourceBody782_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_38 sourceBody782_53

def sourceBody782_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_28 sourceBody782_54

def sourceBody782_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_55

def sourceBody782_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_56

def sourceBody782_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_48 sourceBody782_57

def sourceBody782_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 16)) (some 729) ([18, 6]) (some (18, sourceBody782_20, 782, 17))

def sourceBody782_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_59 sourceBody782_3

def sourceBody782_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_60 sourceBody782_0

def sourceBody782_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_38 sourceBody782_61

def sourceBody782_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_18 sourceBody782_62

def sourceBody782_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody782_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody782_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody782_0, 782, 18)) (some 70) ([6]) (some (6, sourceBody782_65, 782, 19))

def sourceBody782_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_66 sourceBody782_3

def sourceBody782_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_67 sourceBody782_0

def sourceBody782_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_64 sourceBody782_68

def sourceBody782_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_69

def sourceBody782_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_70

def sourceBody782_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody782_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody782_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_73 sourceBody782_0

def sourceBody782_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_72 sourceBody782_74

def sourceBody782_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_71 sourceBody782_75

def sourceBody782_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_63 sourceBody782_76

def sourceBody782_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_77

def sourceBody782_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_78

def sourceBody782_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_58 sourceBody782_79

def sourceBody782_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_17 sourceBody782_80

def sourceBody782_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_81

def sourceBody782_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_82

def sourceBody782_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_11 sourceBody782_83

def sourceBody782_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_84

def sourceBody782_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_85

def sourceBody782_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_5 sourceBody782_86

def sourceBody782_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_87

def sourceBody782_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody782_0 sourceBody782_88

def source782 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (782, 3, sourceBody782_89)
end InitECandidate.Proofs.WordStages
