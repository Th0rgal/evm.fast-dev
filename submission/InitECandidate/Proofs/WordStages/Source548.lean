import InitECandidate.Proofs.WordStages.Source532
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody548_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody548_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody548_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody548_0, 548, 2)) (some 488) ([]) (some (28, sourceBody548_1, 548, 3))

def sourceBody548_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody548_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_2 sourceBody548_3

def sourceBody548_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_4 sourceBody548_0

def sourceBody548_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_5

def sourceBody548_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_6

def sourceBody548_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody548_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody548_0, 548, 4)) (some 471) ([]) (some (16, sourceBody548_8, 548, 5))

def sourceBody548_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_9 sourceBody548_3

def sourceBody548_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_10 sourceBody548_0

def sourceBody548_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody548_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 32, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody548_0, 548, 6)) (some 471) ([]) (some (14, sourceBody548_12, 548, 7))

def sourceBody548_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_13 sourceBody548_3

def sourceBody548_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_14 sourceBody548_0

def sourceBody548_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 100#64)

def sourceBody548_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody548_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody548_0, 548, 8)) (some 466) ([30]) (some (30, sourceBody548_17, 548, 9))

def sourceBody548_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_18 sourceBody548_3

def sourceBody548_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_19 sourceBody548_0

def sourceBody548_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_16 sourceBody548_20

def sourceBody548_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_21

def sourceBody548_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_22

def sourceBody548_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 280#64]))

def sourceBody548_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody548_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody548_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody548_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 24)

def sourceBody548_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 14)

def sourceBody548_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody548_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody548_0, 548, 10)) (some 147) ([8, 26, 18, 34, 2]) (some (8, sourceBody548_30, 548, 11))

def sourceBody548_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_31 sourceBody548_3

def sourceBody548_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_32 sourceBody548_0

def sourceBody548_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_29 sourceBody548_33

def sourceBody548_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_28 sourceBody548_34

def sourceBody548_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_27 sourceBody548_35

def sourceBody548_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_26 sourceBody548_36

def sourceBody548_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_25 sourceBody548_37

def sourceBody548_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_38

def sourceBody548_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_39

def sourceBody548_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
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
              Flapjack.WordLangExpHOL.const 112#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody548_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody548_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody548_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody548_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 32)

def sourceBody548_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody548_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody548_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody548_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody548_0, 548, 12)) (some 422) ([26, 18, 34, 2, 20, 12]) (some (26, sourceBody548_48, 548, 13))

def sourceBody548_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_49 sourceBody548_3

def sourceBody548_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_50 sourceBody548_0

def sourceBody548_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_47 sourceBody548_51

def sourceBody548_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_46 sourceBody548_52

def sourceBody548_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_45 sourceBody548_53

def sourceBody548_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_44 sourceBody548_54

def sourceBody548_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_43 sourceBody548_55

def sourceBody548_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_42 sourceBody548_56

def sourceBody548_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_57

def sourceBody548_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_58

def sourceBody548_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody548_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody548_0, 548, 14)) (some 486) ([26]) (some (26, sourceBody548_48, 548, 15))

def sourceBody548_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_61 sourceBody548_3

def sourceBody548_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_62 sourceBody548_0

def sourceBody548_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_60 sourceBody548_63

def sourceBody548_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_64

def sourceBody548_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_65

def sourceBody548_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_59 sourceBody548_66

def sourceBody548_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody548_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody548_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_69 sourceBody548_0

def sourceBody548_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_68 sourceBody548_70

def sourceBody548_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_67 sourceBody548_71

def sourceBody548_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_41 sourceBody548_72

def sourceBody548_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_73

def sourceBody548_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_40 sourceBody548_74

def sourceBody548_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_24 sourceBody548_75

def sourceBody548_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_76

def sourceBody548_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_23 sourceBody548_77

def sourceBody548_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_15 sourceBody548_78

def sourceBody548_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_79

def sourceBody548_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_80

def sourceBody548_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_81

def sourceBody548_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_82

def sourceBody548_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_83

def sourceBody548_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_84

def sourceBody548_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_85

def sourceBody548_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_86

def sourceBody548_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_11 sourceBody548_87

def sourceBody548_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_88

def sourceBody548_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_89

def sourceBody548_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_90

def sourceBody548_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_91

def sourceBody548_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_92

def sourceBody548_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_93

def sourceBody548_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_94

def sourceBody548_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_0 sourceBody548_95

def sourceBody548_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody548_7 sourceBody548_96

def source548 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (548, 1, sourceBody548_97)
end InitECandidate.Proofs.WordStages
